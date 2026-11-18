#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 The RadioFoundry Authors
"""
APRS host helper for a RadioFoundry radio in KISS mode (docs/spec/aprs.md 9): the APRS-IS connection for the
radio's iGate, a KISS TCP port for APRS programs (APRSdroid, Xastir, YAAC ...), and NMEA forwarding from a GPS on the
computer.

    aprs_gate.py --port /dev/cu.usbmodemXXXX | --port udp:192.168.10.1 [--call CALL] [--passcode N]
                 [--server rotate.aprs2.net:14580] [--filter "m/50"] [--no-is]
                 [--kiss-tcp 8001] [--nmea /dev/cu.gps | --nmea-file track.nmea] [-v]

The radio gates and decides (the iGate rules are in the firmware, aprs_igate.c); this tool only carries lines:

- radio -> APRS-IS: KISS SetHardware frames tagged 'G' carry finished APRS-IS lines (RF packets with qAR, our own
  beacons with TCPIP*). Sent as they are, with CR LF.
- APRS-IS -> radio: every server line that isn't a comment ('#') goes to the radio as a SetHardware 'G' frame; the
  radio passes on only messages to stations it heard directly (iGate TX on), and drops the rest.
- KISS TCP clients <-> radio: DATA frames both ways (what the radio hears, RX builds; what the client sends goes out
  on RF if its source is the radio's callsign, rate limited by the radio).
- NMEA: $GPRMC / $GPGGA lines from a serial GPS or a file go to the radio as SetHardware 'N' frames (the radio's
  "Computer" position source).

Turn KISS on first: Tools > APRS > KISS on USB, or `rfoundry_debug.py aprs set kiss 1`. The radio must not be in hotspot
mode. The passcode is computed from the callsign when not given (the public APRS-IS hash); without --call the tool
logs in receive-only ("-1"), which APRS-IS takes for reading but not for gating.
"""
import argparse
import logging
import os
import selectors
import socket
import sys
import time

FEND, FESC, TFEND, TFESC = 0xC0, 0xDB, 0xDC, 0xDD
CMD_DATA, CMD_SETHW = 0x00, 0x06
TAG_IS, TAG_NMEA = ord("G"), ord("N")
VERSION = "RadioFoundry-aprs_gate 1.0"
GROUP_CALL = {"DX9","DZ9"}


def kiss_encode(cmd: int, payload: bytes) -> bytes:
    out = bytearray([FEND, cmd & 0x0F])
    for b in payload:
        if b == FEND:
            out += bytes([FESC, TFEND])
        elif b == FESC:
            out += bytes([FESC, TFESC])
        else:
            out.append(b)
    out.append(FEND)
    return bytes(out)


class KissDecoder:
    """Bytes in, (type byte, payload) frames out."""

    def __init__(self):
        self.buf = bytearray()
        self.inside = False
        self.esc = False

    def feed(self, data: bytes):
        frames = []
        for b in data:
            if b == FEND:
                if self.inside and self.buf:
                    frames.append((self.buf[0], bytes(self.buf[1:])))
                self.buf = bytearray()
                self.inside = True
                self.esc = False
            elif not self.inside:
                continue
            elif self.esc:
                self.buf.append(FEND if b == TFEND else FESC if b == TFESC else b)
                self.esc = False
            elif b == FESC:
                self.esc = True
            else:
                self.buf.append(b)
        return frames


def passcode(call: str) -> int:
    """The APRS-IS passcode of a callsign (base call, upper case): the published 15-bit hash."""
    base = call.upper().split("-")[0]
    h = 0x73E2
    for i in range(0, len(base), 2):
        h ^= ord(base[i]) << 8
        if i + 1 < len(base):
            h ^= ord(base[i + 1])
    return h & 0x7FFF


def nmea_ok(line: str) -> bool:
    if not line.startswith("$") or "*" not in line:
        return False
    body, _, cs = line[1:].partition("*")
    c = 0
    for ch in body.encode("ascii", "replace"):
        c ^= ch
    try:
        return int(cs[:2], 16) == c
    except ValueError:
        return False

def ax25_to_is(frame: bytes, my_base: str):
    """AX.25 UI frame from a KISS client -> APRS-IS line (TCPIP*), or None. Own callsign only."""
    my_base = my_base.upper().split("-")[0]
    n = 1
    while n * 7 + 6 < len(frame) and not frame[n * 7 + 6] & 1:
        n += 1
    ctl = (n + 1) * 7
    if n * 7 + 6 >= len(frame) or frame[ctl:ctl + 2] != b"\x03\xf0":
        return None

    def addr(b):
        call = bytes(c >> 1 for c in b[:6]).decode("ascii", "replace").strip()
        ssid = (b[6] >> 1) & 0x0F
        return call + (f"-{ssid}" if ssid else "")

    src, dst = addr(frame[7:14]), addr(frame[0:7])
    if src.split("-")[0] != my_base:
        return None
    info = frame[ctl + 2:].replace(b"\r", b"").replace(b"\n", b"")
    return f"{src}>{dst},TCPIP*:".encode("ascii", "replace") + info

def tnc2_to_ax25(line: bytes):
    """APRS-IS text line -> AX.25 UI frame for a KISS client, path replaced by TCPIP*; None if it can't be encoded."""
    try:
        head, info = line.split(b":", 1)
        src, rest = head.split(b">", 1)
        dst = rest.split(b",")[0]

        def enc(call: bytes, last: bool, used: bool = False) -> bytes:
            name, _, ssid = call.decode("ascii").upper().partition("-")
            s = int(ssid) if ssid else 0
            if not name or len(name) > 6 or s > 15:
                raise ValueError
            b = bytearray(ord(ch) << 1 for ch in name.ljust(6))
            b.append(0x60 | (s << 1) | (1 if last else 0) | (0x80 if used else 0))
            return bytes(b)

        return enc(dst, False) + enc(src, False) + enc(b"TCPIP", True, True) + b"\x03\xf0" + info
    except (ValueError, UnicodeDecodeError):
        return None

def message_addressee(line: bytes):
    """Return the fixed-width APRS message/ack addressee, or None."""
    try:
        _, info = line.split(b":", 1)
    except ValueError:
        return None
    if len(info) < 11 or info[:1] != b":" or info[10:11] != b":":
        return None
    try:
        return info[1:10].decode("ascii").strip().upper()
    except UnicodeDecodeError:
        return None

def ax25_source(frame: bytes):
    """(source call-SSID, heard directly?) for an AX.25 UI frame heard on RF, or None."""
    n = 1
    while n * 7 + 6 < len(frame) and not frame[n * 7 + 6] & 1:
        n += 1
    ctl = (n + 1) * 7
    if n * 7 + 6 >= len(frame) or frame[ctl:ctl + 2] != b"\x03\xf0":
        return None
    s = frame[7:14]
    call = bytes(c >> 1 for c in s[:6]).decode("ascii", "replace").strip()
    ssid = (s[6] >> 1) & 0x0F
    src = (call + (f"-{ssid}" if ssid else "")).upper()
    direct = not any(frame[i * 7 + 6] & 0x80 for i in range(2, n + 1))   # no digipeater has repeated it
    return src, direct


class Gating:
    """Mirrors the firmware's IS -> RF rules (docs/spec/aprs.md) so the log shows only what should go on air."""
    DIRECT_S, SENDER_S, DUP_S = 1800, 600, 30

    def __init__(self):
        self.direct = {}    # call -> last time heard directly on RF
        self.any = {}       # call -> last time heard on RF at all
        self.seen = {}      # (source, info) -> last time this IS packet arrived

    def heard(self, frame: bytes):
        r = ax25_source(frame)
        if r is None:
            return
        src, direct = r
        now = time.time()
        self.any[src] = now
        if direct:
            self.direct[src] = now

    def check(self, line: bytes):
        """(True, "") if the radio should transmit this IS line, else (False, reason)."""
        now = time.time()
        for d in (self.direct, self.any, self.seen):
            if len(d) > 2000:
                for k in [k for k, t in d.items() if now - t > 1800]:
                    del d[k]
        to = message_addressee(line)
        if to is None:
            return False, "not a message"
        head, info = line.split(b":", 1)
        src = head.split(b">")[0].decode("latin-1").upper()
        key = (src, info)
        dup = now - self.seen.get(key, 0) < self.DUP_S
        self.seen[key] = now
        if dup:
            return False, "duplicate within 30 s"
        if now - self.direct.get(to, 0) > self.DIRECT_S:
            return False, f"{to} not heard directly in the last 30 min"
        if now - self.any.get(src, 0) < self.SENDER_S:
            return False, f"sender {src} heard on RF in the last 10 min"
        return True, ""

class Radio:
    """The radio's host port: a USB serial port, or udp:<ip>[:3334] for a radio in USB network mode."""

    def __init__(self, port: str):
        self.udp = port.startswith("udp:")
        if self.udp:
            host, _, p = port[4:].partition(":")
            self.addr = (host, int(p or 3334))
            self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            self.sock.setblocking(False)
            self.fileobj = self.sock
        else:
            try:
                import serial
            except ImportError:
                sys.exit("needs pyserial for a serial port: pip install pyserial")
            self.ser = serial.Serial(port, 115200, timeout=0)
            try:    # an FTDI cable passes received bytes on after 1 ms, not 16 (Linux only)
                self.ser.set_low_latency_mode(True)
            except (AttributeError, NotImplementedError, OSError, ValueError):
                pass
            self.fileobj = self.ser

    def read(self) -> bytes:
        if self.udp:
            try:
                data, _ = self.sock.recvfrom(2048)
                return data
            except BlockingIOError:
                return b""
        return self.ser.read(4096)

    def write(self, data: bytes):
        if self.udp:
            self.sock.sendto(data, self.addr)
        else:
            self.ser.write(data)

    def keepalive(self):
        # An empty KISS frame keeps the radio's host link in its TNC mode (it ends after 30 s without frames)
        # This now uses a valid KISS TXDELAY command with a value of 0
        self.write(kiss_encode(0x01, b"\x00"))


class AprsIs:
    def __init__(self, server: str, call: str, code: int, filt: str):
        host, _, p = server.partition(":")
        self.target = (host, int(p or 14580))
        self.call, self.code, self.filt = call, code, filt
        self.sock = None
        self.buf = b""
        self.next_try = 0.0

    def connect(self):
        if time.time() < self.next_try:
            return False
        try:
            s = socket.create_connection(self.target, timeout=10)
        except OSError as e:
            logging.warning("APRS-IS %s:%d: %s, retrying in 30 s", *self.target, e)
            self.next_try = time.time() + 30
            return False
        login = f"user {self.call} pass {self.code} vers {VERSION}"
        if self.filt:
            login += f" filter {self.filt}"
        s.sendall((login + "\r\n").encode("ascii"))
        s.setblocking(False)
        self.sock = s
        logging.info("APRS-IS connected to %s:%d as %s", *self.target, self.call)
        return True

    def lines(self):
        try:
            data = self.sock.recv(4096)
        except BlockingIOError:
            return []
        except OSError:
            data = b""
        if not data:
            logging.warning("APRS-IS connection closed")
            self.close()
            return []
        self.buf += data
        *done, self.buf = self.buf.split(b"\n")
        return [d.rstrip(b"\r") for d in done]

    def send(self, line: bytes):
        if self.sock is None:
            return
        try:
            self.sock.sendall(line + b"\r\n")
        except OSError:
            self.close()

    def close(self):
        if self.sock is not None:
            self.sock.close()
        self.sock = None
        self.next_try = time.time() + 30


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--port", default=os.environ.get("RFOUNDRY_PORT"), help="radio serial port, or udp:<radio ip>[:port]")
    ap.add_argument("--call", help="callsign for APRS-IS (the radio's own, with the SSID it uses)")
    ap.add_argument("--passcode", type=int, help="APRS-IS passcode (default: computed from --call)")
    ap.add_argument("--server", default="rotate.aprs2.net:14580")
    ap.add_argument("--filter", default="", help='APRS-IS filter, e.g. "m/50" (messages need none: the server '
                    "sends messages for stations the connection gated)")
    ap.add_argument("--no-is", action="store_true", help="no APRS-IS connection (KISS TCP / NMEA only)")
    ap.add_argument("--kiss-tcp", type=int, default=0, help="listen for KISS TCP clients on this port (e.g. 8001)")
    ap.add_argument("--nmea", help="a serial GPS whose NMEA goes to the radio")
    ap.add_argument("--nmea-file", help="replay an NMEA file to the radio, one sentence per second")
    ap.add_argument("-v", "--verbose", action="store_true")
    a = ap.parse_args(argv)
    logging.basicConfig(level=logging.DEBUG if a.verbose else logging.INFO, format="%(asctime)s %(message)s")
    if not a.port:
        ap.error("--port (or $RFOUNDRY_PORT) is required")

    radio = Radio(a.port)
    sel = selectors.DefaultSelector()
    sel.register(radio.fileobj, selectors.EVENT_READ, "radio")
    dec = KissDecoder()

    ais = None
    if not a.no_is:
        call = (a.call or "NOCALL").upper()     # APRS-IS receive-only login without one
        code = a.passcode if a.passcode is not None else (passcode(call) if a.call else -1)
        ais = AprsIs(a.server, call, code, a.filter)

    clients = {}
    if a.kiss_tcp:
        lst = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        lst.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        lst.bind(("0.0.0.0", a.kiss_tcp))
        lst.listen(4)
        lst.setblocking(False)
        sel.register(lst, selectors.EVENT_READ, "listen")
        logging.info("KISS TCP on 0.0.0.0:%d", a.kiss_tcp)

    gps = None
    gps_buf = b""
    if a.nmea:
        import serial
        gps = serial.Serial(a.nmea, 4800, timeout=0)
        sel.register(gps, selectors.EVENT_READ, "gps")
    replay = open(a.nmea_file, "r", errors="replace") if a.nmea_file else None
    next_replay = 0.0
    next_keepalive = 0.0
    gating = Gating()

    def to_radio_nmea(line: str):
        if nmea_ok(line) and line[3:6] in ("RMC", "GGA"):
            radio.write(kiss_encode(CMD_SETHW, bytes([TAG_NMEA]) + line.encode("ascii", "replace")))

    while True:
        if ais is not None and ais.sock is None and ais.connect():
            sel.register(ais.sock, selectors.EVENT_READ, "is")
        now = time.time()
        if now >= next_keepalive:
            radio.keepalive()
            next_keepalive = now + 10
        if replay is not None and now >= next_replay:
            line = replay.readline()
            if not line:
                replay.seek(0)
            else:
                to_radio_nmea(line.strip())
            next_replay = now + 1.0
        for key, _ in sel.select(timeout=0.2):
            what = key.data
            if what == "radio":
                for typ, payload in dec.feed(radio.read()):
                    if typ & 0x0F == CMD_SETHW and payload[:1] == bytes([TAG_IS]):
                        logging.info("radio -> IS: %s", payload[1:].decode("latin-1"))
                        if ais is not None:
                            ais.send(payload[1:])
                    elif typ & 0x0F == CMD_DATA:
                        logging.debug("radio heard %d bytes", len(payload))
                        gating.heard(payload)
                        frame = kiss_encode(CMD_DATA, payload)
                        for c in list(clients):
                            try:
                                c.sendall(frame)
                            except OSError:
                                sel.unregister(c)
                                clients.pop(c, None)
                                c.close()
            elif what == "is":
                if ais.sock is None:
                    sel.unregister(key.fileobj)
                    continue
                lines = ais.lines()
                if ais.sock is None:
                    sel.unregister(key.fileobj)
                for line in lines:
                    if not line or line.startswith(b"#"):
                        if line:
                            logging.debug("IS: %s", line.decode("latin-1"))
                        continue
                    radio.write(kiss_encode(CMD_SETHW, bytes([TAG_IS]) + line[:300]))
                    ok, why = gating.check(line)
                    if ok:
                        logging.info("IS -> radio (should transmit): %s", line.decode("latin-1"))
                    if clients and message_addressee(line) is not None:
                        ax = tnc2_to_ax25(line)
                        if ax:
                            logging.info("IS -> client: %s", line.decode("latin-1"))
                            frame = kiss_encode(CMD_DATA, ax)
                            for c in list(clients):
                                try:
                                    c.sendall(frame)
                                except OSError:
                                    sel.unregister(c)
                                    clients.pop(c, None)
                                    c.close()
            elif what == "listen":
                c, peer = key.fileobj.accept()
                c.setblocking(False)
                clients[c] = KissDecoder()
                sel.register(c, selectors.EVENT_READ, "client")
                logging.info("KISS client %s:%d", *peer)
            elif what == "client":
                c = key.fileobj
                try:
                    data = c.recv(4096)
                except OSError:
                    data = b""
                if not data:
                    sel.unregister(c)
                    clients.pop(c, None)
                    c.close()
                    continue
                for typ, payload in clients[c].feed(data):
                    if typ & 0x0F == CMD_DATA and typ >> 4 == 0:
                        radio.write(kiss_encode(CMD_DATA, payload))
                        if ais is not None and a.call:
                            line = ax25_to_is(payload, a.call)
                            if line:
                                logging.info("client -> IS: %s", line.decode("latin-1"))
                                ais.send(line)
            elif what == "gps":
                gps_buf += gps.read(1024)
                *done, gps_buf = gps_buf.split(b"\n")
                for line in done:
                    to_radio_nmea(line.decode("ascii", "replace").strip())


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        sys.exit(0)
