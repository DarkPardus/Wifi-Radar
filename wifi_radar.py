#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
WI-FI RADAR  -  Yesil askeri radar tarzinda canli Wi-Fi tarayici
Parrot OS / KDE Plasma (PyQt5)

Kurulum:   sudo apt install python3-pyqt5 network-manager iw
Calistir:  python3 wifi_radar.py
Demo:      python3 wifi_radar.py --demo        (Wi-Fi karti yoksa / VM'de)
Tam ekran: F11   |   Cikis: Ctrl+Q

Radar notu: Tek antenle yon bilgisi alinamaz. Bu yuzden
  - MESAFE  = sinyal gucune gore (merkeze yakin = guclu sinyal)
  - ACI     = her BSSID icin sabit (MAC'ten uretilir)
"""
import sys
import os
import re
import math
import time
import random
import hashlib
import shutil
import argparse
import subprocess
from collections import deque

from PyQt5 import QtCore, QtGui, QtWidgets
from PyQt5.QtCore import Qt, QRectF, QPointF, pyqtSignal
from PyQt5.QtGui import (QColor, QPainter, QPen, QBrush, QFont, QPainterPath,
                         QLinearGradient, QRadialGradient, QFontMetrics)

# ----------------------------------------------------------------- RENKLER
BG = QColor("#010a06")
PANEL_BG = QColor("#02140a")
GREEN = QColor("#19ff4d")
GREEN_M = QColor("#2fae52")
GREEN_D = QColor("#0c7a2a")
GREEN_DD = QColor("#06381a")
YELLOW = QColor("#e8ff3a")
BLUE = QColor("#2f8cff")
RED = QColor("#ff3b3b")
ORANGE = QColor("#ffb020")
CYAN = QColor("#27e8ff")
PALETTE = [QColor("#19ff4d"), QColor("#27e8ff"), QColor("#e8ff3a"),
           QColor("#5aa8ff"), QColor("#9dff8a"), QColor("#ffb020"),
           QColor("#ff6ad5")]

DBM_NEAR = -30.0   # radar merkezi
DBM_FAR = -100.0   # radar kenari


def mono(px, bold=False):
    f = QFont("DejaVu Sans Mono")
    f.setStyleHint(QFont.Monospace)
    f.setPixelSize(px)
    f.setBold(bold)
    return f


def alpha(c, a):
    c = QColor(c)
    c.setAlpha(max(0, min(255, int(a))))
    return c


# ----------------------------------------------------------------- YARDIMCI
class OuiDB:
    """MAC ureticisi sorgulama (nmap / ieee-data dosyalarindan)."""
    PATHS = ["/usr/share/nmap/nmap-mac-prefixes",
             "/usr/share/ieee-data/oui.txt",
             "/var/lib/ieee-data/oui.txt",
             "/usr/share/hwdata/oui.txt"]

    def __init__(self):
        self.map = {}
        for path in self.PATHS:
            if not os.path.exists(path):
                continue
            try:
                with open(path, "r", encoding="utf-8", errors="ignore") as f:
                    for line in f:
                        if "(hex)" in line:
                            a, b = line.split("(hex)", 1)
                            self.map[a.strip().replace("-", "").upper()] = b.strip()
                        elif (len(line) > 7 and line[6] == " "
                              and re.match(r"^[0-9A-Fa-f]{6}$", line[:6])):
                            self.map.setdefault(line[:6].upper(), line[7:].strip())
            except Exception:
                pass

    def lookup(self, mac):
        try:
            first = int(mac[:2], 16)
        except ValueError:
            return "?"
        if first & 2:
            return "Rastgele / yerel MAC"
        return self.map.get(mac.replace(":", "")[:6].upper(), "Bilinmiyor")


OUI = OuiDB()


def freq_to_chan(f):
    if f == 2484:
        return 14
    if f < 2484:
        return (f - 2407) // 5
    if f < 5925:
        return (f - 5000) // 5
    return (f - 5950) // 5


def band_index(freq):
    return 0 if freq < 3000 else (1 if freq < 5925 else 2)


BAND_NAMES = ["2.4 GHz", "5 GHz", "6 GHz"]


def pct_from_dbm(dbm):
    return max(0, min(100, int(round((dbm + 100) * 2))))


def bar_color(pct):
    if pct >= 66:
        return GREEN
    if pct >= 40:
        return YELLOW
    if pct >= 20:
        return ORANGE
    return RED


# ----------------------------------------------------------------- AP MODELI
class AP:
    def __init__(self, d, fresh):
        self.bssid = d["bssid"]
        h = int(hashlib.md5(self.bssid.encode()).hexdigest(), 16)
        self.angle = (h % 3600) / 10.0
        self.color = PALETTE[(h >> 16) % len(PALETTE)]
        self.vendor = OUI.lookup(self.bssid)
        self.first_seen = time.time()
        self.new = fresh
        self.glow = 0.3
        self.ripple = -1.0
        self.history = deque(maxlen=200)
        self.rssi = float(d["dbm"])
        self.update(d, first=True)

    def update(self, d, first=False):
        self.ssid = d.get("ssid", "")
        self.chan = d.get("chan", 0)
        self.freq = d.get("freq", 0)
        self.rate = d.get("rate", 0)
        self.sec = (d.get("sec", "") or "").strip()
        self.mode = d.get("mode", "Infra")
        self.inuse = d.get("inuse", False)
        self.raw = float(d["dbm"])
        if not first:
            self.rssi = self.rssi * 0.6 + self.raw * 0.4
        self.last_seen = time.time()
        self.history.append((self.last_seen, self.raw))

    @property
    def band(self):
        return band_index(self.freq)

    @property
    def kind(self):
        s = self.sec
        if s in ("", "--"):
            return "open"
        if "WEP" in s and "WPA" not in s:
            return "wep"
        return "wpa"

    @property
    def sec_txt(self):
        return "AÇIK" if self.kind == "open" else self.sec

    @property
    def disp_ssid(self):
        return self.ssid if self.ssid else "<GİZLİ>"

    @property
    def pct(self):
        return pct_from_dbm(self.rssi)

    @property
    def dist(self):
        a = -40.0 if self.freq < 3000 else -47.0
        return 10 ** ((a - self.rssi) / 28.0)

    @property
    def is_new(self):
        return self.new and (time.time() - self.first_seen) < 10

    def blip_color(self):
        if self.inuse:
            return BLUE
        return {"open": RED, "wep": ORANGE}.get(self.kind, GREEN)


class State:
    def __init__(self):
        self.aps = {}
        self.selected = None
        self.iface = ""
        self.err = ""


# ----------------------------------------------------------------- TARAMA
def split_terse(line):
    out, cur, esc = [], [], False
    for ch in line:
        if esc:
            cur.append(ch)
            esc = False
        elif ch == "\\":
            esc = True
        elif ch == ":":
            out.append("".join(cur))
            cur = []
        else:
            cur.append(ch)
    out.append("".join(cur))
    return out


def first_int(s, default=0):
    m = re.search(r"\d+", s or "")
    return int(m.group()) if m else default


def get_iface():
    env = dict(os.environ, LC_ALL="C", LANG="C")
    try:
        if shutil.which("nmcli"):
            r = subprocess.run(["nmcli", "-t", "-f", "DEVICE,TYPE", "dev"],
                               capture_output=True, text=True, timeout=8, env=env)
            for line in r.stdout.splitlines():
                p = split_terse(line)
                if len(p) >= 2 and p[1] == "wifi":
                    return p[0]
        if shutil.which("iw"):
            r = subprocess.run(["iw", "dev"], capture_output=True, text=True,
                               timeout=8, env=env)
            m = re.search(r"Interface\s+(\S+)", r.stdout)
            if m:
                return m.group(1)
    except Exception:
        pass
    return ""


def scan_nmcli():
    env = dict(os.environ, LC_ALL="C", LANG="C")
    cmd = ["nmcli", "-t", "-e", "yes", "-f",
           "IN-USE,BSSID,SSID,MODE,CHAN,FREQ,RATE,SIGNAL,SECURITY",
           "dev", "wifi", "list", "--rescan", "yes"]
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=25, env=env)
    except Exception as e:
        return [], str(e)
    if r.returncode != 0:
        return [], (r.stderr.strip() or "nmcli hatası")
    aps = []
    for line in r.stdout.splitlines():
        p = split_terse(line)
        if len(p) < 9:
            continue
        bssid = p[1].upper()
        if not re.match(r"^([0-9A-F]{2}:){5}[0-9A-F]{2}$", bssid):
            continue
        sig = first_int(p[7])
        aps.append({
            "inuse": p[0].strip() == "*",
            "bssid": bssid,
            "ssid": p[2],
            "mode": p[3],
            "chan": first_int(p[4]),
            "freq": first_int(p[5]),
            "rate": first_int(p[6]),
            "dbm": sig / 2.0 - 100.0,
            "sec": p[8],
        })
    return aps, ""


def scan_iw_dump(iface):
    """iw 'scan dump' root gerektirmez; gercek dBm degerini verir."""
    res = {}
    try:
        r = subprocess.run(["iw", "dev", iface, "scan", "dump"],
                           capture_output=True, text=True, timeout=10,
                           env=dict(os.environ, LC_ALL="C"))
    except Exception:
        return res
    cur = None
    for line in r.stdout.splitlines():
        m = re.match(r"^BSS ([0-9a-fA-F:]{17})", line)
        if m:
            cur = m.group(1).upper()
            res[cur] = {"rsn": False, "wpa": False, "sae": False, "priv": False}
            continue
        if cur is None:
            continue
        s = line.strip()
        if s.startswith("signal:"):
            try:
                res[cur]["dbm"] = float(s.split()[1])
            except Exception:
                pass
        elif s.startswith("freq:"):
            res[cur]["freq"] = int(float(s.split()[1]))
        elif s.startswith("SSID:"):
            res[cur]["ssid"] = s[5:].strip()
        elif s.startswith("last seen:"):
            res[cur]["age_ms"] = first_int(s)
        elif s.startswith("RSN:"):
            res[cur]["rsn"] = True
        elif s.startswith("WPA:"):
            res[cur]["wpa"] = True
        elif s.startswith("capability:") and "Privacy" in s:
            res[cur]["priv"] = True
        elif "Authentication suites" in s and "SAE" in s:
            res[cur]["sae"] = True
    return res


def real_scan():
    iface = get_iface()
    aps, err = [], ""
    if shutil.which("nmcli"):
        aps, err = scan_nmcli()
    iwd = scan_iw_dump(iface) if (iface and shutil.which("iw")) else {}
    if aps:
        for a in aps:
            x = iwd.get(a["bssid"])
            if x and "dbm" in x and x.get("age_ms", 0) < 15000:
                a["dbm"] = x["dbm"]
        return aps, iface, ""
    out = []
    for b, x in iwd.items():
        if "dbm" not in x or "freq" not in x or x.get("age_ms", 0) > 15000:
            continue
        sec = ""
        if x["rsn"]:
            sec = "WPA3" if x["sae"] else "WPA2"
        elif x["wpa"]:
            sec = "WPA1"
        elif x["priv"]:
            sec = "WEP"
        out.append({"inuse": False, "bssid": b, "ssid": x.get("ssid", ""),
                    "mode": "Infra", "chan": freq_to_chan(x["freq"]),
                    "freq": x["freq"], "rate": 0, "dbm": x["dbm"], "sec": sec})
    if out:
        return out, iface, ""
    return [], iface, err or "Wi-Fi adaptörü / tarama verisi bulunamadı"


_DEMO = [
    ("TTNET_Fiber_A1B2", "A4:2B:B0:11:22:33", 6, 2437, -44, "WPA2", True),
    ("TTNET_Fiber_A1B2_5G", "A4:2B:B0:11:22:34", 36, 5180, -52, "WPA2", False),
    ("Kafe_Misafir", "DC:9F:DB:5A:10:01", 1, 2412, -63, "", False),
    ("iPhone", "6E:21:4F:0C:99:AA", 11, 2462, -58, "WPA2", False),
    ("Superonline_Ev", "F8:1A:67:3C:4D:5E", 11, 2462, -71, "WPA2 WPA3", False),
    ("", "00:1A:2B:3C:4D:5E", 6, 2437, -77, "WPA2", False),
    ("EskiModem", "00:14:6C:88:99:AB", 3, 2422, -82, "WEP", False),
    ("DIRECT-roku-1F2", "02:11:22:33:44:55", 1, 2412, -69, "WPA2", False),
    ("Komsu_5G", "B0:BE:76:AA:BB:CC", 100, 5500, -66, "WPA2", False),
    ("AndroidAP_9X", "9A:12:34:56:78:9B", 9, 2452, -74, "WPA2", False),
    ("Hotel_Lobby", "C8:3A:35:11:22:77", 149, 5745, -79, "", False),
    ("Zyxel_Office", "5C:F4:AB:12:34:56", 44, 5220, -61, "WPA2", False),
    ("HUAWEI-B535", "E8:CD:2D:AB:CD:EF", 13, 2472, -85, "WPA2", False),
    ("Printer-Setup", "3C:2A:F4:00:11:22", 6, 2437, -90, "", False),
]


def demo_scan():
    out = []
    for ssid, bssid, ch, fr, dbm, sec, inuse in _DEMO:
        out.append({"inuse": inuse, "bssid": bssid, "ssid": ssid, "mode": "Infra",
                    "chan": ch, "freq": fr, "rate": 130 if fr < 3000 else 433,
                    "dbm": dbm + random.gauss(0, 2.0), "sec": sec})
    return out


class Scanner(QtCore.QThread):
    result = pyqtSignal(list, str, str)

    def __init__(self, interval=3.0, demo=False):
        super().__init__()
        self.interval = interval
        self.demo = demo
        self._stop = False

    def stop(self):
        self._stop = True

    def run(self):
        while not self._stop:
            t0 = time.time()
            if self.demo:
                aps, iface, err = demo_scan(), "demo0", ""
            else:
                aps, iface, err = real_scan()
            self.result.emit(aps, iface, err)
            while not self._stop and time.time() - t0 < self.interval:
                self.msleep(100)


# ----------------------------------------------------------------- PANEL
class Panel(QtWidgets.QWidget):
    def __init__(self, st, title="", parent=None):
        super().__init__(parent)
        self.st = st
        self.title = title

    def inner(self):
        top = 30 if self.title else 10
        return QRectF(10, top, self.width() - 20, self.height() - top - 10)

    def paint_frame(self, p):
        w, h = self.width(), self.height()
        p.fillRect(0, 0, w, h, PANEL_BG)
        p.setBrush(Qt.NoBrush)
        p.setPen(QPen(GREEN, 2))
        p.drawRect(QRectF(1, 1, w - 2, h - 2))
        p.setPen(QPen(GREEN_DD, 1))
        p.drawRect(QRectF(4.5, 4.5, w - 9, h - 9))
        if self.title:
            p.setFont(mono(13, True))
            p.setPen(GREEN)
            p.drawText(QRectF(12, 7, w - 24, 20), Qt.AlignLeft | Qt.AlignVCenter, self.title)


# ----------------------------------------------------------------- HEADER
class Header(Panel):
    def __init__(self, st):
        super().__init__(st)
        self.setFixedHeight(78)

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        self.paint_frame(p)
        w = self.width()
        p.setFont(mono(27, True))
        p.setPen(GREEN)
        p.drawText(QRectF(18, 6, 420, 40), Qt.AlignLeft | Qt.AlignVCenter, "◉ WI-FI RADAR")
        p.setFont(mono(11))
        p.setPen(GREEN_M)
        p.drawText(QRectF(20, 46, 560, 20), Qt.AlignLeft | Qt.AlignVCenter,
                   "AÇI: SABİT (MAC'TEN)   MESAFE: SİNYAL GÜCÜNE GÖRE")

        aps = list(self.st.aps.values())
        n24 = sum(1 for a in aps if a.band == 0)
        n5 = sum(1 for a in aps if a.band == 1)
        n6 = sum(1 for a in aps if a.band == 2)
        nopen = sum(1 for a in aps if a.kind == "open")
        p.setFont(mono(15, True))
        p.setPen(GREEN)
        txt = "ARAYÜZ {}    AĞ {}    2.4G {}    5G {}    6G {}    AÇIK {}".format(
            self.st.iface or "-", len(aps), n24, n5, n6, nopen)
        p.drawText(QRectF(w * 0.27, 8, w * 0.46, 30), Qt.AlignCenter, txt)

        p.setFont(mono(12, True))
        blink = int(time.time() * 2) % 2 == 0
        if self.st.err:
            p.setPen(RED)
            p.drawText(QRectF(w * 0.27, 40, w * 0.46, 26), Qt.AlignCenter,
                       "● " + self.st.err[:90])
        else:
            p.setPen(GREEN if blink else GREEN_D)
            p.drawText(QRectF(w * 0.27, 40, w * 0.46, 26), Qt.AlignCenter, "● CANLI TARAMA")

        p.setFont(mono(36, True))
        p.setPen(YELLOW)
        p.drawText(QRectF(w - 330, 2, 314, 48), Qt.AlignRight | Qt.AlignVCenter,
                   time.strftime("%H:%M:%S"))
        p.setFont(mono(11))
        p.setPen(GREEN_M)
        p.drawText(QRectF(w - 330, 50, 314, 20), Qt.AlignRight | Qt.AlignVCenter,
                   time.strftime("%d.%m.%Y"))


# ----------------------------------------------------------------- RADAR
class RadarWidget(Panel):
    picked = pyqtSignal(str)

    def __init__(self, st):
        super().__init__(st)
        self.sweep = 0.0
        self.speed = 70.0
        self.last = time.monotonic()
        self.blips = []
        self.setMinimumSize(420, 420)
        self.timer = QtCore.QTimer(self)
        self.timer.timeout.connect(self.tick)
        self.timer.start(30)

    @staticmethod
    def rfrac(dbm):
        return max(0.04, min(1.0, (DBM_NEAR - dbm) / (DBM_NEAR - DBM_FAR)))

    def tick(self):
        now = time.monotonic()
        dt = min(now - self.last, 0.1)
        self.last = now
        step = self.speed * dt
        self.sweep = (self.sweep + step) % 360
        for ap in self.st.aps.values():
            diff = (self.sweep - ap.angle) % 360
            if diff < step:
                ap.glow = 1.0
                ap.ripple = 0.0
            else:
                ap.glow = max(0.25, ap.glow - dt * 0.35)
            if ap.ripple >= 0:
                ap.ripple += dt
                if ap.ripple > 1.2:
                    ap.ripple = -1.0
        self.update()

    def mousePressEvent(self, ev):
        best, bd = None, 18
        for x, y, b in self.blips:
            d = math.hypot(ev.x() - x, ev.y() - y)
            if d < bd:
                best, bd = b, d
        if best:
            self.picked.emit(best)

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        self.paint_frame(p)
        r = self.inner()
        R = min(r.width(), r.height()) / 2 - 40
        if R < 40:
            return
        cx, cy = r.center().x(), r.center().y()

        def pt(bearing, rad):
            a = math.radians(bearing)
            return QPointF(cx + rad * math.sin(a), cy - rad * math.cos(a))

        # zemin
        g = QRadialGradient(QPointF(cx, cy), R)
        g.setColorAt(0, QColor("#04301a"))
        g.setColorAt(1, QColor("#021208"))
        p.setPen(Qt.NoPen)
        p.setBrush(QBrush(g))
        p.drawEllipse(QPointF(cx, cy), R, R)

        # dis halka + derece cetveli
        p.setBrush(Qt.NoBrush)
        p.setPen(QPen(GREEN, 3))
        p.drawEllipse(QPointF(cx, cy), R, R)
        p.setPen(QPen(GREEN_M, 1))
        p.drawEllipse(QPointF(cx, cy), R + 12, R + 12)
        for deg in range(0, 360, 5):
            ln = 12 if deg % 30 == 0 else (8 if deg % 10 == 0 else 4)
            p.setPen(QPen(GREEN if deg % 30 == 0 else GREEN_M, 1))
            p.drawLine(pt(deg, R + 12 - ln + 12 - 12), pt(deg, R + 12))
        names = {0: "N", 90: "E", 180: "S", 270: "W"}
        for deg in range(0, 360, 30):
            q = pt(deg, R + 28)
            if deg in names:
                p.setFont(mono(16, True))
                p.setPen(YELLOW)
                t = names[deg]
            else:
                p.setFont(mono(13, True))
                p.setPen(GREEN)
                t = str(deg)
            p.drawText(QRectF(q.x() - 22, q.y() - 11, 44, 22), Qt.AlignCenter, t)

        # mesafe halkalari (dBm)
        span = DBM_NEAR - DBM_FAR
        for dbm in (-40, -50, -60, -70, -80, -90):
            rr = R * (DBM_NEAR - dbm) / span
            p.setPen(QPen(GREEN_D, 1.4))
            p.setBrush(Qt.NoBrush)
            p.drawEllipse(QPointF(cx, cy), rr, rr)
            p.setFont(mono(10))
            p.setPen(GREEN_M)
            p.drawText(QPointF(cx + 5, cy - rr + 12), str(dbm))

        # capraz cizgiler
        p.setPen(QPen(GREEN_DD, 1))
        for deg in range(30, 180, 30):
            if deg in (90,):
                continue
            p.drawLine(pt(deg, R), pt(deg + 180, R))
        p.setPen(QPen(GREEN, 1.6))
        p.drawLine(pt(0, R), pt(180, R))
        p.drawLine(pt(90, R), pt(270, R))
        p.setBrush(QBrush(GREEN))
        p.setPen(Qt.NoPen)
        p.drawEllipse(QPointF(cx, cy), 3, 3)

        # tarama izi
        rect = QRectF(cx - R, cy - R, 2 * R, 2 * R)
        n, step = 55, 1.6
        p.setPen(Qt.NoPen)
        for i in range(n):
            b1 = self.sweep - i * step
            a = 120 * (1 - i / n) ** 2
            p.setBrush(QColor(25, 255, 77, int(a)))
            p.drawPie(rect, int((90 - b1) * 16), int((step + 0.3) * 16))
        p.setPen(QPen(alpha(GREEN, 70), 7))
        p.drawLine(QPointF(cx, cy), pt(self.sweep, R))
        p.setPen(QPen(QColor(170, 255, 190), 2))
        p.drawLine(QPointF(cx, cy), pt(self.sweep, R))

        # hedefler
        self.blips = []
        sel = self.st.selected
        for ap in sorted(self.st.aps.values(), key=lambda a: a.rssi):
            q = pt(ap.angle, R * self.rfrac(ap.rssi))
            self.blips.append((q.x(), q.y(), ap.bssid))
            col = YELLOW if ap.is_new else ap.blip_color()
            if ap.ripple >= 0:
                k = ap.ripple / 1.2
                p.setBrush(Qt.NoBrush)
                p.setPen(QPen(alpha(col, 200 * (1 - k)), 1.5))
                p.drawEllipse(q, 6 + k * 26, 6 + k * 26)
            p.setPen(Qt.NoPen)
            p.setBrush(alpha(col, 70 * ap.glow))
            p.drawEllipse(q, 11, 11)
            p.setBrush(alpha(col, 90 + 165 * ap.glow))
            p.drawEllipse(q, 4 + 2 * ap.glow, 4 + 2 * ap.glow)
            if ap.bssid == sel:
                p.setBrush(Qt.NoBrush)
                p.setPen(QPen(YELLOW, 1.5))
                s = 13
                p.drawRect(QRectF(q.x() - s, q.y() - s, 2 * s, 2 * s))
                p.setPen(QPen(alpha(YELLOW, 90), 1, Qt.DashLine))
                p.drawLine(QPointF(cx, cy), q)
            if ap.glow > 0.6 or ap.bssid == sel:
                p.setFont(mono(11, True))
                p.setPen(YELLOW if ap.bssid == sel else alpha(col, 120 + 135 * ap.glow))
                label = ap.disp_ssid[:16]
                p.drawText(QPointF(q.x() + 10, q.y() - 8), label)

        # kose yazilari
        p.setFont(mono(17, True))
        p.setPen(GREEN)
        p.drawText(QPointF(r.left() + 6, r.top() + 18), "CANLI Wi-Fi")
        p.setFont(mono(17, True))
        p.drawText(QPointF(r.left() + 6, r.top() + 38), "AP: {}".format(len(self.st.aps)))

        legend = [(GREEN, "WPA/WPA2/WPA3"), (ORANGE, "WEP"), (RED, "AÇIK (korumasız)"),
                  (BLUE, "BAĞLI"), (YELLOW, "YENİ")]
        y = r.bottom() - 12 - 15 * (len(legend) - 1)
        p.setFont(mono(11))
        for col, t in legend:
            p.setPen(Qt.NoPen)
            p.setBrush(col)
            p.drawEllipse(QPointF(r.left() + 12, y - 4), 4, 4)
            p.setPen(GREEN_M)
            p.drawText(QPointF(r.left() + 24, y), t)
            y += 15

        p.setFont(mono(12, True))
        p.setPen(GREEN)
        p.drawText(QRectF(r.right() - 170, r.bottom() - 24, 166, 20),
                   Qt.AlignRight | Qt.AlignVCenter, "TARAMA {:03d}°".format(int(self.sweep)))


# ----------------------------------------------------------------- SPEKTRUM
BANDS = [
    ("2.4 GHz", 2400, 2495, 11, [(2407 + 5 * c, str(c)) for c in range(1, 14)]),
    ("5 GHz", 5150, 5850, 14,
     [(5000 + 5 * c, str(c)) for c in (36, 40, 44, 48, 52, 56, 60, 64, 100, 108,
                                      116, 124, 132, 140, 149, 157, 165)]),
    ("6 GHz", 5925, 7125, 14,
     [(5950 + 5 * c, str(c)) for c in (1, 33, 65, 97, 129, 161, 193, 225)]),
]


class Spectrum(Panel):
    def __init__(self, st):
        super().__init__(st, "KANAL SPEKTRUMU")
        self.mode = 0
        self.setMinimumHeight(200)
        self.setCursor(Qt.PointingHandCursor)

    def mousePressEvent(self, ev):
        self.mode = (self.mode + 1) % 3
        self.update()

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        self.title = "KANAL SPEKTRUMU  [{}]  (tıkla: bant değiştir)".format(BANDS[self.mode][0])
        self.paint_frame(p)
        name, f0, f1, bw, ticks = BANDS[self.mode]
        r = self.inner()
        plot = QRectF(r.left() + 30, r.top() + 4, r.width() - 36, r.height() - 24)

        def X(f):
            return plot.left() + (f - f0) / (f1 - f0) * plot.width()

        def Y(d):
            return plot.bottom() - (d + 100) / 70.0 * plot.height()

        p.setFont(mono(9))
        for d in (-40, -50, -60, -70, -80, -90):
            p.setPen(QPen(GREEN_DD, 1))
            p.drawLine(QPointF(plot.left(), Y(d)), QPointF(plot.right(), Y(d)))
            p.setPen(GREEN_M)
            p.drawText(QPointF(r.left(), Y(d) + 3), str(d))
        for f, lbl in ticks:
            p.setPen(QPen(GREEN_DD, 1))
            p.drawLine(QPointF(X(f), plot.top()), QPointF(X(f), plot.bottom()))
            p.setPen(GREEN_M)
            p.drawText(QRectF(X(f) - 14, plot.bottom() + 3, 28, 14), Qt.AlignCenter, lbl)
        p.setPen(QPen(GREEN, 1.5))
        p.drawRect(plot)

        p.save()
        p.setClipRect(plot.adjusted(-1, -1, 1, 1))
        aps = [a for a in self.st.aps.values() if a.band == self.mode]
        aps.sort(key=lambda a: a.rssi)
        labels = []
        for ap in aps:
            sel = ap.bssid == self.st.selected
            yt = Y(max(-100, min(-30, ap.rssi)))
            yb = Y(-100)
            path = QPainterPath()
            path.moveTo(X(ap.freq - bw), yb)
            path.quadTo(QPointF(X(ap.freq), 2 * yt - yb), QPointF(X(ap.freq + bw), yb))
            col = YELLOW if sel else ap.color
            p.setBrush(alpha(col, 70 if sel else 40))
            p.setPen(QPen(alpha(col, 255 if sel else 220), 2.2 if sel else 1.4))
            p.drawPath(path)
            if ap.rssi > -85 or sel:
                labels.append((X(ap.freq), yt, ap, col))
        p.setFont(mono(9, True))
        for x, y, ap, col in labels:
            p.setPen(col)
            p.drawText(QPointF(x - 24, y - 3), ap.disp_ssid[:12])
        p.restore()
        if not aps:
            p.setPen(GREEN_M)
            p.setFont(mono(12))
            p.drawText(plot, Qt.AlignCenter, "Bu bantta ağ yok")


# ----------------------------------------------------------------- GECMIS
class History(Panel):
    WINDOW = 300.0

    def __init__(self, st):
        super().__init__(st, "SİNYAL GEÇMİŞİ (5 dk)")
        self.setMinimumHeight(200)

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        self.paint_frame(p)
        r = self.inner()
        plot = QRectF(r.left() + 30, r.top() + 18, r.width() - 36, r.height() - 36)
        ap = self.st.aps.get(self.st.selected)

        def Y(d):
            return plot.bottom() - (d + 100) / 70.0 * plot.height()

        p.setFont(mono(9))
        for d in (-40, -50, -60, -70, -80, -90):
            p.setPen(QPen(GREEN_DD, 1))
            p.drawLine(QPointF(plot.left(), Y(d)), QPointF(plot.right(), Y(d)))
            p.setPen(GREEN_M)
            p.drawText(QPointF(r.left(), Y(d) + 3), str(d))
        now = time.time()
        for s in range(0, 301, 60):
            x = plot.right() - s / self.WINDOW * plot.width()
            p.setPen(QPen(GREEN_DD, 1))
            p.drawLine(QPointF(x, plot.top()), QPointF(x, plot.bottom()))
            p.setPen(GREEN_M)
            p.drawText(QRectF(x - 20, plot.bottom() + 3, 40, 14), Qt.AlignCenter,
                       "şimdi" if s == 0 else "-{}dk".format(s // 60))
        p.setPen(QPen(GREEN, 1.5))
        p.setBrush(Qt.NoBrush)
        p.drawRect(plot)
        if not ap:
            p.setPen(GREEN_M)
            p.setFont(mono(12))
            p.drawText(plot, Qt.AlignCenter, "HEDEF SEÇİLMEDİ")
            return
        pts = [(t, d) for t, d in ap.history if now - t <= self.WINDOW]
        if len(pts) < 1:
            return
        qpts = [QPointF(plot.right() - (now - t) / self.WINDOW * plot.width(),
                        Y(max(-100, min(-30, d)))) for t, d in pts]
        p.save()
        p.setClipRect(plot)
        fill = QPainterPath()
        fill.moveTo(qpts[0].x(), plot.bottom())
        for q in qpts:
            fill.lineTo(q)
        fill.lineTo(qpts[-1].x(), plot.bottom())
        fill.closeSubpath()
        gr = QLinearGradient(0, plot.top(), 0, plot.bottom())
        gr.setColorAt(0, QColor(25, 255, 77, 120))
        gr.setColorAt(1, QColor(25, 255, 77, 0))
        p.setPen(Qt.NoPen)
        p.setBrush(QBrush(gr))
        p.drawPath(fill)
        line = QPainterPath()
        line.moveTo(qpts[0])
        for q in qpts[1:]:
            line.lineTo(q)
        p.setBrush(Qt.NoBrush)
        p.setPen(QPen(alpha(GREEN, 70), 6))
        p.drawPath(line)
        p.setPen(QPen(GREEN, 1.8))
        p.drawPath(line)
        p.setBrush(GREEN)
        p.setPen(Qt.NoPen)
        for q in qpts:
            p.drawEllipse(q, 2, 2)
        p.restore()
        vals = [d for _, d in pts]
        p.setFont(mono(10, True))
        p.setPen(GREEN_M)
        p.drawText(QPointF(plot.left(), r.top() + 12),
                   "{}  MİN {:.0f}  ORT {:.0f}  MAX {:.0f}".format(
                       ap.disp_ssid[:14], min(vals), sum(vals) / len(vals), max(vals)))
        p.setFont(mono(14, True))
        p.setPen(YELLOW)
        p.drawText(QRectF(plot.right() - 120, r.top() - 2, 120, 18),
                   Qt.AlignRight | Qt.AlignVCenter, "{:.0f} dBm".format(vals[-1]))


# ----------------------------------------------------------------- HEDEF
class Target(Panel):
    def __init__(self, st):
        super().__init__(st, "HEDEF BİLGİSİ")
        self.setMinimumHeight(200)

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        self.paint_frame(p)
        r = self.inner()
        ap = self.st.aps.get(self.st.selected)
        if not ap:
            p.setPen(GREEN_M)
            p.setFont(mono(12))
            p.drawText(r, Qt.AlignCenter, "Radardan veya listeden\nbir ağ seçin")
            return
        age = time.time() - ap.last_seen
        rows = [
            ("SSID", ap.disp_ssid),
            ("BSSID", ap.bssid),
            ("ÜRETİCİ", ap.vendor),
            ("KANAL", "{}  ({} MHz)".format(ap.chan, ap.freq)),
            ("BANT / HIZ", "{}  /  {}".format(
                BAND_NAMES[ap.band], "{} Mbit/s".format(ap.rate) if ap.rate else "-")),
            ("GÜVENLİK", ap.sec_txt),
            ("MOD", ap.mode or "-"),
            ("SİNYAL", "{:.0f} dBm  ({}%)".format(ap.rssi, ap.pct)),
            ("MESAFE", "~ {:.1f} m (tahmini)".format(ap.dist)),
            ("İLK GÖRÜLME", time.strftime("%H:%M:%S", time.localtime(ap.first_seen))),
            ("SON GÖRÜLME", "{:.0f} sn önce".format(age)),
            ("DURUM", "BAĞLI" if ap.inuse else "-"),
        ]
        fm = QFontMetrics(mono(11, True))
        kw = 86
        y = r.top() + 12
        for k, v in rows:
            p.setFont(mono(11))
            p.setPen(GREEN_M)
            p.drawText(QPointF(r.left() + 2, y), k)
            p.setFont(mono(11, True))
            col = GREEN
            if k == "GÜVENLİK":
                col = {"open": RED, "wep": ORANGE}.get(ap.kind, GREEN)
            if k == "SİNYAL":
                col = bar_color(ap.pct)
            p.setPen(col)
            p.drawText(QPointF(r.left() + kw, y),
                       fm.elidedText(v, Qt.ElideRight, int(r.width() - kw)))
            y += 17


# ----------------------------------------------------------------- TABLO
class BarDelegate(QtWidgets.QStyledItemDelegate):
    def paint(self, painter, opt, idx):
        pct = idx.data(Qt.UserRole) or 0
        painter.save()
        painter.setRenderHint(QPainter.Antialiasing, False)
        painter.fillRect(opt.rect, QColor("#0b4a20") if opt.state & QtWidgets.QStyle.State_Selected else BG)
        rc = opt.rect.adjusted(4, 5, -4, -5)
        n, gap = 20, 2
        w = (rc.width() - gap * (n - 1)) / float(n)
        col = bar_color(pct)
        for i in range(n):
            on = (i + 0.5) / n * 100 <= pct
            painter.fillRect(QRectF(rc.left() + i * (w + gap), rc.top(), w, rc.height()),
                             col if on else GREEN_DD)
        painter.restore()


class TablePanel(Panel):
    COLS = ["SSID", "MAC (BSSID)", "KNL", "BANT", "GÜVENLİK", "dBm", "MESAFE", "SİNYAL"]

    def __init__(self, st):
        super().__init__(st, "TESPİT EDİLEN AĞLAR")
        lay = QtWidgets.QVBoxLayout(self)
        lay.setContentsMargins(10, 30, 10, 10)
        t = self.table = QtWidgets.QTableWidget(0, len(self.COLS))
        t.setHorizontalHeaderLabels(self.COLS)
        t.verticalHeader().setVisible(False)
        t.verticalHeader().setDefaultSectionSize(24)
        t.setShowGrid(False)
        t.setEditTriggers(QtWidgets.QAbstractItemView.NoEditTriggers)
        t.setSelectionBehavior(QtWidgets.QAbstractItemView.SelectRows)
        t.setSelectionMode(QtWidgets.QAbstractItemView.SingleSelection)
        t.setFocusPolicy(Qt.NoFocus)
        t.setFont(mono(12))
        t.setItemDelegateForColumn(7, BarDelegate(t))
        hh = t.horizontalHeader()
        hh.setStretchLastSection(False)
        hh.setSectionResizeMode(0, QtWidgets.QHeaderView.Stretch)
        for c in range(1, 7):
            hh.setSectionResizeMode(c, QtWidgets.QHeaderView.ResizeToContents)
        hh.setSectionResizeMode(7, QtWidgets.QHeaderView.Fixed)
        t.setColumnWidth(7, 150)
        t.setStyleSheet("""
            QTableWidget { background:#010a06; color:#19ff4d; border:none;
                selection-background-color:#0b4a20; selection-color:#e8ff3a; }
            QHeaderView::section { background:#031a0d; color:#19ff4d; border:none;
                border-bottom:1px solid #19ff4d; padding:4px; font-weight:bold; }
            QScrollBar:vertical { background:#010a06; width:8px; }
            QScrollBar::handle:vertical { background:#0c7a2a; min-height:20px; }
            QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical { height:0; }
        """)
        lay.addWidget(t)
        self.sort_col, self.sort_rev = 5, True

    def paintEvent(self, e):
        p = QPainter(self)
        self.title = "TESPİT EDİLEN AĞLAR  [{}]".format(len(self.st.aps))
        self.paint_frame(p)

    def sorted_aps(self):
        keys = {0: lambda a: a.disp_ssid.lower(), 1: lambda a: a.bssid,
                2: lambda a: a.chan, 3: lambda a: a.freq, 4: lambda a: a.sec_txt,
                5: lambda a: a.rssi, 6: lambda a: a.rssi, 7: lambda a: a.rssi}
        return sorted(self.st.aps.values(), key=keys[self.sort_col], reverse=self.sort_rev)

    def header_clicked(self, col):
        if col == self.sort_col:
            self.sort_rev = not self.sort_rev
        else:
            self.sort_col = col
            self.sort_rev = col in (5, 6, 7)
        self.refresh()

    def refresh(self):
        t = self.table
        t.blockSignals(True)
        aps = self.sorted_aps()
        t.setRowCount(len(aps))
        sel_row = -1
        now = time.time()
        for row, ap in enumerate(aps):
            if ap.is_new:
                col = YELLOW
            elif ap.inuse:
                col = CYAN
            elif ap.kind == "open":
                col = RED
            elif ap.kind == "wep":
                col = ORANGE
            else:
                col = GREEN
            if now - ap.last_seen > 8 and not ap.is_new:
                col = GREEN_D
            ssid = ("▶ " if ap.inuse else "") + ap.disp_ssid
            cells = [ssid, ap.bssid, str(ap.chan), BAND_NAMES[ap.band].replace(" GHz", "G"),
                     ap.sec_txt, "{:.0f}".format(ap.rssi), "~{:.0f} m".format(ap.dist), ""]
            for c, txt in enumerate(cells):
                it = QtWidgets.QTableWidgetItem(txt)
                it.setForeground(QBrush(col))
                if c in (2, 3, 5, 6):
                    it.setTextAlignment(Qt.AlignCenter)
                if c == 0:
                    it.setData(Qt.UserRole, ap.bssid)
                if c == 7:
                    it.setData(Qt.UserRole, ap.pct)
                t.setItem(row, c, it)
            if ap.bssid == self.st.selected:
                sel_row = row
        if sel_row >= 0:
            t.selectRow(sel_row)
        else:
            t.clearSelection()
        t.blockSignals(False)

    def select_bssid(self, bssid):
        t = self.table
        t.blockSignals(True)
        for row in range(t.rowCount()):
            it = t.item(row, 0)
            if it and it.data(Qt.UserRole) == bssid:
                t.selectRow(row)
                t.scrollToItem(it)
                break
        t.blockSignals(False)


# ----------------------------------------------------------------- ANA PENCERE
class Main(QtWidgets.QMainWindow):
    TTL = 20.0

    def __init__(self, demo=False, interval=3.0):
        super().__init__()
        self.setWindowTitle("Wi-Fi Radar")
        self.st = State()
        self.first = True
        self.setStyleSheet("QMainWindow { background:#000; }")

        self.header = Header(self.st)
        self.radar = RadarWidget(self.st)
        self.tpanel = TablePanel(self.st)
        self.spec = Spectrum(self.st)
        self.hist = History(self.st)
        self.target = Target(self.st)

        central = QtWidgets.QWidget()
        self.setCentralWidget(central)
        v = QtWidgets.QVBoxLayout(central)
        v.setContentsMargins(10, 10, 10, 10)
        v.setSpacing(8)
        v.addWidget(self.header)
        h = QtWidgets.QHBoxLayout()
        h.setSpacing(8)
        h.addWidget(self.radar, 5)
        right = QtWidgets.QVBoxLayout()
        right.setSpacing(8)
        right.addWidget(self.tpanel, 1)
        bottom = QtWidgets.QHBoxLayout()
        bottom.setSpacing(8)
        bottom.addWidget(self.spec, 3)
        bottom.addWidget(self.hist, 3)
        bottom.addWidget(self.target, 3)
        bw = QtWidgets.QWidget()
        bw.setLayout(bottom)
        bw.setFixedHeight(250)
        bottom.setContentsMargins(0, 0, 0, 0)
        right.addWidget(bw)
        h.addLayout(right, 7)
        v.addLayout(h, 1)

        self.radar.picked.connect(self.select)
        self.tpanel.table.itemSelectionChanged.connect(self.on_table_sel)
        self.tpanel.table.horizontalHeader().sectionClicked.connect(self.tpanel.header_clicked)

        QtWidgets.QShortcut(QtGui.QKeySequence("F11"), self, activated=self.toggle_fs)
        QtWidgets.QShortcut(QtGui.QKeySequence("Esc"), self, activated=self.exit_fs)
        QtWidgets.QShortcut(QtGui.QKeySequence("Ctrl+Q"), self, activated=self.close)

        self.clock = QtCore.QTimer(self)
        self.clock.timeout.connect(self.on_clock)
        self.clock.start(1000)

        self.scanner = Scanner(interval, demo)
        self.scanner.result.connect(self.on_scan)
        self.scanner.start()
        self.resize(1560, 900)
        self.setMinimumSize(1100, 680)

    def toggle_fs(self):
        self.showNormal() if self.isFullScreen() else self.showFullScreen()

    def exit_fs(self):
        if self.isFullScreen():
            self.showNormal()

    def on_clock(self):
        self.header.update()
        self.hist.update()
        self.target.update()

    def on_table_sel(self):
        rows = self.tpanel.table.selectionModel().selectedRows()
        if rows:
            it = self.tpanel.table.item(rows[0].row(), 0)
            if it:
                self.select(it.data(Qt.UserRole), from_table=True)

    def select(self, bssid, from_table=False):
        self.st.selected = bssid
        if not from_table:
            self.tpanel.select_bssid(bssid)
        for w in (self.spec, self.hist, self.target):
            w.update()

    def on_scan(self, aps, iface, err):
        now = time.time()
        self.st.iface = iface
        self.st.err = err
        for d in aps:
            b = d["bssid"]
            if b in self.st.aps:
                self.st.aps[b].update(d)
            else:
                self.st.aps[b] = AP(d, fresh=not self.first)
        if aps or not err:
            self.first = False
        for b in list(self.st.aps):
            if now - self.st.aps[b].last_seen > self.TTL:
                del self.st.aps[b]
                if self.st.selected == b:
                    self.st.selected = None
        if (self.st.selected is None or self.st.selected not in self.st.aps) and self.st.aps:
            self.st.selected = max(self.st.aps.values(), key=lambda a: a.rssi).bssid
        self.tpanel.refresh()
        self.header.update()
        self.spec.update()
        self.hist.update()
        self.target.update()

    def closeEvent(self, ev):
        self.scanner.stop()
        self.scanner.wait(3000)
        ev.accept()


def main():
    ap = argparse.ArgumentParser(description="Yeşil askeri radar tarzı Wi-Fi tarayıcı")
    ap.add_argument("--demo", action="store_true", help="Sahte verilerle demo modu")
    ap.add_argument("--interval", type=float, default=3.0, help="Tarama aralığı (sn)")
    ap.add_argument("--fullscreen", action="store_true", help="Tam ekran başlat")
    args, qt_args = ap.parse_known_args()

    QtWidgets.QApplication.setAttribute(Qt.AA_EnableHighDpiScaling, True)
    app = QtWidgets.QApplication([sys.argv[0]] + qt_args)
    w = Main(demo=args.demo, interval=max(1.5, args.interval))
    if args.fullscreen:
        w.showFullScreen()
    else:
        w.show()
    sys.exit(app.exec_())


if __name__ == "__main__":
    main()
