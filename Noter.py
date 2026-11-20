#!/usr/bin/env python3
"""aNoter - notes on the left, any file on the right, with a file explorer.

Layout (like a commander):
    [ explorer / calendar / reminders ] [ notes: .noter files ] [ any other file ]

Notes are .noter files (rich text) that open on the left; every other file opens on the
right. Optional daily notes live in ~/.local/share/noter/notes/YYYY-MM-DD.html
(override the location with the NOTER_HOME environment variable).
Run it with:  python3 Noter.py [files...]

Reminders keep working while the window is closed: enable "Background reminders"
in the Notes menu (or run `Noter.py --daemon`) to start a tiny headless service
at login that sends the desktop notifications.
"""
import fcntl
import glob
import html as htmllib
import json
import math
import os
import re
import shlex
import shutil
import signal
import subprocess
import sys
import threading
import traceback
import unicodedata
import uuid
import wave
from datetime import datetime, timedelta
from pathlib import Path
from urllib.parse import quote

from PyQt5.QtCore import (QCoreApplication, QDate, QDateTime, QDir, QEvent, QLocale, QPoint, QSettings, QSize, Qt, QThread,
                          QTimer, QUrl, pyqtSignal)
from PyQt5.QtGui import (QBrush, QColor, QDesktopServices, QFont,
                         QCursor, QFontDatabase, QIcon, QImageReader, QKeySequence,
                         QImage, QMovie, QPainter, QPalette, QPixmap, QPolygon, QSyntaxHighlighter, QTextCharFormat,
                         QTextCursor, QTextDocument, QTextListFormat, QTextLength,
                         QTextTableCellFormat, QTextTableFormat)
from PyQt5.QtWidgets import (QAbstractItemView, QAction, QApplication,
                             QCalendarWidget, QCheckBox, QComboBox, QDateTimeEdit,
                             QDialog, QDialogButtonBox, QFileDialog, QFileSystemModel,
                             QFormLayout, QFrame, QHBoxLayout, QInputDialog,
                             QLabel, QLineEdit, QListWidget, QListWidgetItem,
                             QMainWindow, QMenu, QMessageBox, QPlainTextEdit,
                             QPushButton, QScrollArea, QSpinBox, QSplitter,
                             QStackedLayout, QSystemTrayIcon, QTabWidget,
                             QTextEdit, QToolBar, QToolButton, QTreeView,
                             QVBoxLayout, QWidget)

try:  # HTML "browser mode" (optional; apt install python3-pyqt5.qtwebkit)
    from PyQt5.QtWebKit import QWebSettings
    from PyQt5.QtWebKitWidgets import QWebPage, QWebView
    HAVE_WEBKIT = True
except ImportError:
    HAVE_WEBKIT = False
HTML_EXTS = (".html", ".htm", ".xhtml")
try:  # crisp SVG zooming (optional)
    from PyQt5.QtSvg import QSvgRenderer
except ImportError:
    QSvgRenderer = None
try:  # extra image formats (WebP, TIFF, JPEG 2000, ...) through Pillow (optional)
    from PIL import Image as PILImage
    PIL_EXTS = {"webp", "tif", "tiff", "jfif", "jp2", "j2k", "tga", "dds", "icns", "pcx", "ppm",
                "avif", "heic", "heif"}
except ImportError:
    PILImage, PIL_EXTS = None, set()

try:  # syntax highlighting is optional: `pip install pygments` (or apt install python3-pygments)
    from pygments.lexers import get_lexer_by_name, get_lexer_for_filename
    from pygments.token import Token
    from pygments.util import ClassNotFound
    HAVE_PYGMENTS = True
except ImportError:
    HAVE_PYGMENTS = False

APP_NAME = "aNoter"
ACCENT = "#3b82f6"
BASE_PT = 11
NOTER_EXT = ".noter"
STAMP_DATE, STAMP_TIME = "\u25A6", "\u25F7"   # calendar grid, clock face: marks inserted date/time
# (emoji such as U+1F4C5 are drawn as empty boxes by Qt 5 on many systems, so plain symbols are used)
CHECK_OFF, CHECK_ON = "\u2610", "\u2611"  # ballot boxes

PALETTE = [
    ("Red", "#e53935"), ("Orange", "#fb8c00"), ("Yellow", "#fdd835"),
    ("Green", "#43a047"), ("Teal", "#00acc1"), ("Blue", "#1e88e5"),
    ("Purple", "#8e24aa"), ("Pink", "#d81b60"), ("Gray", "#9e9e9e"),
]
HIGHLIGHTS = [
    ("Yellow", "#fff59d"), ("Green", "#c8e6c9"), ("Blue", "#bbdefb"),
    ("Pink", "#f8bbd0"), ("Orange", "#ffe0b2"), ("Purple", "#e1bee7"),
    ("Gray", "#e0e0e0"),
]


# --------------------------------------------------------------------------
# helpers
# --------------------------------------------------------------------------
def color_icon(color, size=16):
    pm = QPixmap(size, size)
    pm.fill(QColor(color))
    return QIcon(pm)


# light green (mint, not lemon): used by the icon and the "N" of the title
GREEN_ON_DARK, GREEN_ON_LIGHT = "#62e07a", "#25a548"

# pixel font for the N on the cube: 9 x 11
_N_GLYPH = [(c, r) for r in range(11) for c in range(9)
            if c < 2 or c > 6 or (r * 5 // 10 + 2 <= c <= r * 5 // 10 + 3)]


def _pixel_icon_image():
    """The aNoter icon: a light-green isometric cube with an N on its front face, in
    16-bit console style (hand-placed pixels on a 32x32 grid, hard outline, dithered shade)."""
    S = 32
    img = QImage(S, S, QImage.Format_ARGB32)
    img.fill(Qt.transparent)
    p = QPainter(img)
    p.setRenderHint(QPainter.Antialiasing, False)

    def poly(pts, fill, line=None):
        p.setBrush(QColor(fill))
        p.setPen(QColor(line) if line else Qt.NoPen)
        p.drawPolygon(QPolygon([QPoint(x, y) for x, y in pts]))

    def px(x, y, col):
        img.setPixelColor(x, y, QColor(col))

    outline = "#073a17"
    top = [(16, 2), (29, 8), (16, 14), (3, 8)]
    left = [(3, 8), (16, 14), (16, 29), (3, 23)]
    right = [(16, 14), (29, 8), (29, 23), (16, 29)]
    for x in range(8, 25):            # soft ground shadow
        px(x, 30, "#00000040")
    poly(left, "#58d56f")
    poly(right, "#2ba449")
    poly(top, "#c5f7cb")
    # dithered shade on the right face
    for y in range(15, 29):
        for x in range(17, 29):
            if (x + y) % 2 == 0 and img.pixelColor(x, y) == QColor("#2ba449"):
                px(x, y, "#238f3f")
    # bright rim along the two upper edges (light from the top-left)
    for (x0, y0, x1, y1) in ((3, 8, 16, 2), (16, 2, 29, 8)):
        n = abs(x1 - x0)
        for i in range(n + 1):
            px(x0 + (x1 - x0) * i // n, y0 + (y1 - y0) * i // n, "#ffffff")
    for x in range(4, 16):            # light edge on the left face's top
        px(x, 9 + (x - 3) * 6 // 13, "#a2f0b0")
    # the N, sheared to follow the left face: dark drop-shadow first, then white
    def glyph(dx, dy, col):
        for c, r in _N_GLYPH:
            x = 5 + c + dx
            px(x, 12 + r + dy + (x - 3) * 6 // 13 - 1, col)
    glyph(1, 1, "#0f6a2c")
    glyph(0, 0, "#ffffff")
    for (x, y) in ((27, 3), (5, 3)):   # sparkles
        px(x, y, "#ffffff")
        for dx, dy in ((-1, 0), (1, 0), (0, -1), (0, 1)):
            px(x + dx, y + dy, "#dcffe2")
    for pts in (top, left, right):     # pixel outline
        poly(pts, "#00000000", outline)
    p.end()
    return img


_ICON_IMG = None


def app_icon_image(size):
    """aNoter icon as a QImage: integer-scaled with hard pixel edges for big sizes."""
    global _ICON_IMG
    if _ICON_IMG is None:
        _ICON_IMG = _pixel_icon_image()
    if size >= 32:
        return _ICON_IMG.scaled(size, size, Qt.KeepAspectRatio, Qt.FastTransformation)
    return _ICON_IMG.scaled(size, size, Qt.KeepAspectRatio, Qt.SmoothTransformation)


class TitleBar(QWidget):
    """Centered header: the icon next to the bold app name, its capital N in green."""

    def __init__(self):
        super().__init__()
        lay = QHBoxLayout(self)
        lay.setContentsMargins(0, 3, 0, 3)
        lay.setSpacing(8)
        self.icon = QLabel()
        self.icon.setPixmap(QPixmap.fromImage(app_icon_image(32)))
        self.icon.setFixedSize(32, 32)
        self.label = QLabel()
        f = self.label.font()
        f.setPointSize(17)
        f.setBold(True)
        self.label.setFont(f)
        lay.addStretch(1)
        lay.addWidget(self.icon)
        lay.addWidget(self.label)
        lay.addStretch(1)
        self._paint()

    def _paint(self):
        base = QApplication.palette().color(QPalette.Base)
        green = GREEN_ON_DARK if base.lightness() < 128 else GREEN_ON_LIGHT
        i = next((k for k, c in enumerate(APP_NAME) if c.isupper()), 0)   # a[N]oter
        self.label.setText(f'<b>{APP_NAME[:i]}<span style="color:{green}">{APP_NAME[i]}</span>'
                           f'{APP_NAME[i + 1:]}</b>')

    def event(self, e):
        ok = super().event(e)
        if e.type() == QEvent.ApplicationPaletteChange:   # theme switch
            self._paint()
        return ok


def make_app_icon():
    icon = QIcon()
    for size in (16, 24, 32, 48, 64, 128, 256):
        icon.addPixmap(QPixmap.fromImage(app_icon_image(size)))
    return icon


LAUNCHER_FILE = Path.home() / ".local/share/applications/aNoter.desktop"
ICON_DIR = Path.home() / ".local/share/icons/hicolor"


def install_launcher():
    """Create the application-menu / dock entry 'aNoter' with its icon."""
    for size in (64, 128, 256):
        d = ICON_DIR / f"{size}x{size}" / "apps"
        d.mkdir(parents=True, exist_ok=True)
        app_icon_image(size).save(str(d / "noter.png"))
    LAUNCHER_FILE.parent.mkdir(parents=True, exist_ok=True)
    LAUNCHER_FILE.write_text(
        "[Desktop Entry]\nType=Application\nName=aNoter\n"
        "GenericName=Notes and file commander\n"
        "Comment=Notes on the left, any files on the right\n"
        f'Exec="{sys.executable}" "{os.path.abspath(__file__)}" %F\n'
        "Icon=noter\nTerminal=false\nCategories=Utility;TextEditor;Office;\n"
        "StartupWMClass=aNoter\nStartupNotify=true\n", encoding="utf-8")
    try:  # let the shell notice the new entry right away
        subprocess.run(["update-desktop-database", str(LAUNCHER_FILE.parent)],
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=10)
    except (OSError, subprocess.SubprocessError):
        pass
    return LAUNCHER_FILE


def apply_theme(app, dark):
    app.setStyle("Fusion")
    if not dark:
        app.setPalette(app.style().standardPalette())
        return
    p = QPalette()
    win, base, btn = QColor(60, 63, 70), QColor(46, 49, 56), QColor(76, 80, 89)
    text, dim = QColor(236, 238, 242), QColor(140, 145, 155)
    p.setColor(QPalette.Window, win)
    p.setColor(QPalette.WindowText, text)
    p.setColor(QPalette.Base, base)
    p.setColor(QPalette.AlternateBase, win)
    p.setColor(QPalette.ToolTipBase, btn)
    p.setColor(QPalette.ToolTipText, text)
    p.setColor(QPalette.Text, text)
    p.setColor(QPalette.Button, btn)
    p.setColor(QPalette.ButtonText, text)
    p.setColor(QPalette.BrightText, QColor(255, 107, 107))
    p.setColor(QPalette.Link, QColor(110, 168, 254))
    p.setColor(QPalette.Highlight, QColor(ACCENT))
    p.setColor(QPalette.HighlightedText, Qt.white)
    p.setColor(QPalette.Light, QColor(100, 105, 116))
    p.setColor(QPalette.Midlight, QColor(86, 90, 100))
    p.setColor(QPalette.Mid, QColor(52, 55, 62))
    p.setColor(QPalette.Dark, QColor(38, 40, 46))
    p.setColor(QPalette.Shadow, QColor(25, 26, 30))
    if hasattr(QPalette, "PlaceholderText"):
        p.setColor(QPalette.PlaceholderText, dim)
    for role in (QPalette.Text, QPalette.ButtonText, QPalette.WindowText):
        p.setColor(QPalette.Disabled, role, dim)
    app.setPalette(p)


def iso(qdate):
    return qdate.toString(Qt.ISODate)


def html_to_text(src):
    """Cheap HTML -> plain text (used to grep .noter files off the GUI thread)."""
    src = re.sub(r"(?is)<(style|head|script).*?</\1>", "", src)
    src = re.sub(r"(?i)<br\s*/?>|</(p|li|tr|div|h\d)>", "\n", src)
    src = re.sub(r"(?s)<[^>]+>", "", src)
    return re.sub(r"\n{2,}", "\n", htmllib.unescape(src))


# --------------------------------------------------------------------------
# readable colors: keep saved/pasted text colors legible on the current theme
# --------------------------------------------------------------------------
MIN_CONTRAST = 3.5


def _lum(c):
    def ch(v):
        v /= 255.0
        return v / 12.92 if v <= 0.03928 else ((v + 0.055) / 1.055) ** 2.4
    return 0.2126 * ch(c.red()) + 0.7152 * ch(c.green()) + 0.0722 * ch(c.blue())


def mix(a, b, t):
    """Colour t of the way from a to b."""
    return QColor(*(round(x + (y - x) * t) for x, y in
                    zip((a.red(), a.green(), a.blue()), (b.red(), b.green(), b.blue()))))


def contrast(a, b):
    la, lb = _lum(a), _lum(b)
    if la < lb:
        la, lb = lb, la
    return (la + 0.05) / (lb + 0.05)


def adjust_fg(fg, explicit, bg, default):
    """-> (changed, color). color None means 'use the default text color'."""
    if contrast(fg, bg) >= MIN_CONTRAST:
        return False, None
    if explicit:
        h, s, l, _a = fg.getHslF()
        if s < 0.15 and contrast(default, bg) >= MIN_CONTRAST:
            return True, None  # black/gray on dark (or white on light)
        step = 0.04 if _lum(bg) < 0.4 else -0.04
        for _ in range(25):  # keep the hue, move the lightness
            l = min(1.0, max(0.0, l + step))
            col = QColor.fromHslF(max(h, 0.0), s, l)
            if contrast(col, bg) >= MIN_CONTRAST:
                return True, col
    black, white = QColor("#000000"), QColor("#ffffff")
    return True, black if contrast(black, bg) >= contrast(white, bg) else white


def fix_contrast(doc, default, base, join=False):
    """Repair unreadable text colors in a QTextDocument. Returns True if changed."""
    todo = []
    blk = doc.begin()
    while blk.isValid():
        cell_bg = base
        c0 = QTextCursor(blk)
        tbl = c0.currentTable()
        if tbl:
            cb = tbl.cellAt(c0).format().background()
            if cb.style() != Qt.NoBrush:
                cell_bg = cb.color()
        it = blk.begin()
        while not it.atEnd():
            frag = it.fragment()
            it += 1
            if not frag.isValid():
                continue
            fmt = frag.charFormat()
            hb = fmt.background()
            bg = hb.color() if hb.style() != Qt.NoBrush else cell_bg
            fb = fmt.foreground()
            explicit = fb.style() != Qt.NoBrush
            fg = fb.color() if explicit else default
            changed, col = adjust_fg(fg, explicit, bg, default)
            if changed:
                new = QTextCharFormat(fmt)
                if col is None:
                    new.clearForeground()
                else:
                    new.setForeground(col)
                todo.append((frag.position(), frag.length(), new))
        blk = blk.next()
    if not todo:
        return False
    cur = QTextCursor(doc)
    cur.joinPreviousEditBlock() if join else cur.beginEditBlock()
    for pos, ln, fmt in reversed(todo):
        cur.setPosition(pos)
        cur.setPosition(pos + ln, QTextCursor.KeepAnchor)
        cur.setCharFormat(fmt)
    cur.endEditBlock()
    return True


# --------------------------------------------------------------------------
# storage
# --------------------------------------------------------------------------
class Store:
    def __init__(self):
        root = os.environ.get("NOTER_HOME")
        self.root = Path(root) if root else Path.home() / ".local/share/noter"
        self.notes_dir = self.root / "notes"
        self.notes_dir.mkdir(parents=True, exist_ok=True)
        self.rem_file = self.root / "reminders.json"
        self.cfg_file = self.root / "config.json"

    # small settings file shared by the app and the background service
    def config(self):
        cfg = {"sound": True, "sound_file": ""}
        try:
            cfg.update(json.loads(self.cfg_file.read_text(encoding="utf-8")))
        except (OSError, ValueError):
            pass
        return cfg

    def set_config(self, **kw):
        cfg = self.config()
        cfg.update(kw)
        tmp = self.cfg_file.with_suffix(".tmp")
        tmp.write_text(json.dumps(cfg, indent=2), encoding="utf-8")
        tmp.replace(self.cfg_file)

    def note_path(self, qdate):
        return self.notes_dir / (iso(qdate) + ".html")

    def note_dates(self):
        return {p.stem for p in self.notes_dir.glob("*.html")}

    def load_note(self, qdate):
        p = self.note_path(qdate)
        try:
            return p.read_text(encoding="utf-8")
        except FileNotFoundError:
            return ""

    def save_note(self, qdate, html, empty):
        p = self.note_path(qdate)
        if empty:
            p.unlink(missing_ok=True)
            return
        tmp = p.with_suffix(".tmp")
        tmp.write_text(html, encoding="utf-8")
        tmp.replace(p)

    def load_reminders(self):
        try:
            return json.loads(self.rem_file.read_text(encoding="utf-8"))
        except (FileNotFoundError, ValueError):
            return []

    def save_reminders(self, items):
        tmp = self.rem_file.with_suffix(".tmp")
        tmp.write_text(json.dumps(items, indent=2, ensure_ascii=False),
                       encoding="utf-8")
        tmp.replace(self.rem_file)

    def rem_mtime(self):
        try:
            return self.rem_file.stat().st_mtime_ns
        except OSError:
            return 0

    def fire_due(self, notify):
        """Notify for every due reminder, then reschedule/remove it.
        Always works on the file on disk so the app and the background
        service never overwrite each other. Returns True if the file changed."""
        items, now, changed = self.load_reminders(), datetime.now(), False
        for r in list(items):
            try:
                when = datetime.fromisoformat(r["when"])
            except (KeyError, ValueError, TypeError):
                items.remove(r)
                changed = True
                continue
            if when > now:
                continue
            body = r.get("text", "")
            if now - when > timedelta(minutes=2):
                body += f"   (was due {when:%a %d %b %H:%M})"
            notify("Reminder", body)
            step = {"daily": timedelta(days=1), "weekly": timedelta(days=7)}.get(
                r.get("repeat", "none"))
            if step:
                while when <= now:
                    when += step
                r["when"] = when.strftime("%Y-%m-%dT%H:%M:00")
            else:
                items.remove(r)
            changed = True
        if changed:
            self.save_reminders(items)
        return changed


# --------------------------------------------------------------------------
# background reminder service (works while the window is closed)
# --------------------------------------------------------------------------
AUTOSTART_FILE = Path.home() / ".config/autostart/noter-reminders.desktop"


def send_notification(title, body):
    """Desktop notification via notify-send. Returns False if unavailable."""
    if not shutil.which("notify-send"):
        return False
    subprocess.Popen(["notify-send", "-a", APP_NAME, "-u", "normal",
                      "-i", "appointment-soon", title, body])
    return True


SOUND_DIRS = ["/usr/share/sounds/freedesktop/stereo", "/usr/share/sounds/ubuntu/stereo",
              "/usr/share/sounds/gnome/default/alerts", "/usr/share/sounds"]
SOUND_NAMES = ["alarm-clock-elapsed", "complete", "bell", "message", "message-new-instant"]


def _fallback_wav(store):
    """Generate a short three-tone chime, used when no sound theme is installed."""
    path = store.root / "reminder.wav"
    if path.exists():
        return str(path)
    rate, frames = 44100, bytearray()
    for freq, dur in ((880, 0.16), (1175, 0.16), (1319, 0.32)):
        n = int(rate * dur)
        for i in range(n):
            env = min(1.0, i / 400, (n - i) / 1500)  # fade in/out, no clicks
            v = int(14000 * env * math.sin(2 * math.pi * freq * i / rate))
            frames += v.to_bytes(2, "little", signed=True)
        frames += bytes(int(rate * 0.05) * 2)
    with wave.open(str(path), "wb") as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(rate)
        w.writeframes(bytes(frames))
    return str(path)


def sound_candidates(store):
    files = []
    custom = store.config().get("sound_file") or ""
    if custom and os.path.isfile(custom):
        files.append(custom)
    for d in SOUND_DIRS:
        for name in SOUND_NAMES:
            for ext in (".oga", ".ogg", ".wav"):
                f = os.path.join(d, name + ext)
                if os.path.isfile(f) and f not in files:
                    files.append(f)
                    break
        if len(files) > 2:
            break
    files.append(_fallback_wav(store))
    return files


def _player_cmds(path):
    cmds = []
    for exe, args in (("pw-play", []), ("paplay", []), ("canberra-gtk-play", ["-f"]),
                      ("ffplay", ["-nodisp", "-autoexit", "-loglevel", "quiet"]),
                      ("mpv", ["--no-video", "--really-quiet"]), ("play", ["-q"])):
        if shutil.which(exe):
            cmds.append([exe, *args, path])
    if path.lower().endswith(".wav") and shutil.which("aplay"):
        cmds.append(["aplay", "-q", path])
    return cmds


def play_sound(store, wait=False):
    """Play the reminder sound in the background; tries players/files until one works."""
    def work():
        for path in sound_candidates(store):
            for cmd in _player_cmds(path):
                try:
                    r = subprocess.run(cmd, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                                       stderr=subprocess.DEVNULL, timeout=30)
                except (OSError, subprocess.TimeoutExpired):
                    continue
                if r.returncode == 0:
                    return
    t = threading.Thread(target=work, daemon=True)
    t.start()
    if wait:
        t.join()


def alert(store, title, body):
    """Desktop notification + sound. Returns True if a notification was shown."""
    shown = send_notification(title, body)
    if store.config().get("sound", True):
        play_sound(store)
    return shown


def _lock_path(store):
    return store.root / "daemon.lock"


def daemon_running(store):
    """True if the background service holds its lock."""
    with open(_lock_path(store), "a+") as f:
        try:
            fcntl.flock(f, fcntl.LOCK_SH | fcntl.LOCK_NB)
            fcntl.flock(f, fcntl.LOCK_UN)
            return False
        except OSError:
            return True


def run_daemon():
    store = Store()
    lock = open(_lock_path(store), "a+")
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        print("aNoter reminder service is already running.")
        return 0
    lock.seek(0)
    lock.truncate()
    lock.write(str(os.getpid()))
    lock.flush()

    app = QCoreApplication(sys.argv)
    signal.signal(signal.SIGTERM, lambda *_: app.quit())
    signal.signal(signal.SIGINT, lambda *_: app.quit())

    def notify(title, body):
        if not alert(store, title, body):
            print(f"{title}: {body}", file=sys.stderr, flush=True)

    def tick():
        try:
            store.fire_due(notify)
        except Exception:
            traceback.print_exc()

    timer = QTimer(interval=10_000)
    timer.timeout.connect(tick)
    timer.start()
    # lets Python signal handlers run while Qt's loop is idle
    keepalive = QTimer(interval=500)
    keepalive.timeout.connect(lambda: None)
    keepalive.start()
    QTimer.singleShot(0, tick)
    code = app.exec_()
    lock.close()
    return code


def start_daemon():
    subprocess.Popen([sys.executable, os.path.abspath(__file__), "--daemon"],
                     stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                     stderr=subprocess.DEVNULL, start_new_session=True)


def autostart_enabled():
    return AUTOSTART_FILE.exists()


def stop_daemon(store):
    try:
        pid = int(_lock_path(store).read_text().strip())
        if daemon_running(store):
            os.kill(pid, signal.SIGTERM)
    except (OSError, ValueError):
        pass


def enable_background(store):
    AUTOSTART_FILE.parent.mkdir(parents=True, exist_ok=True)
    AUTOSTART_FILE.write_text(
        "[Desktop Entry]\nType=Application\nName=aNoter reminders\n"
        "Comment=Sends aNoter reminder notifications while the app is closed\n"
        f'Exec="{sys.executable}" "{os.path.abspath(__file__)}" --daemon\n'
        "X-GNOME-Autostart-enabled=true\nNoDisplay=true\n", encoding="utf-8")
    if not daemon_running(store):
        start_daemon()


def disable_background(store):
    AUTOSTART_FILE.unlink(missing_ok=True)
    stop_daemon(store)


# --------------------------------------------------------------------------
# calendar with note / reminder marks
# --------------------------------------------------------------------------
class MarkedCalendar(QCalendarWidget):
    def __init__(self):
        super().__init__()
        self.note_dates = set()
        self.reminder_dates = set()
        self.setGridVisible(False)
        self.setFirstDayOfWeek(Qt.Monday)
        self.setVerticalHeaderFormat(QCalendarWidget.ISOWeekNumbers)
        self.setHorizontalHeaderFormat(QCalendarWidget.ShortDayNames)

    def paintCell(self, painter, rect, date):
        super().paintCell(painter, rect, date)
        key = iso(date)
        painter.save()
        painter.setRenderHint(QPainter.Antialiasing)
        painter.setPen(Qt.NoPen)
        if key in self.note_dates:
            painter.setBrush(QColor(ACCENT))
            painter.drawRoundedRect(rect.left() + 6, rect.bottom() - 5,
                                    rect.width() - 12, 3, 1.5, 1.5)
        if key in self.reminder_dates:
            painter.setBrush(QColor("#fb8c00"))
            painter.drawEllipse(rect.right() - 10, rect.top() + 3, 6, 6)
        painter.restore()


# --------------------------------------------------------------------------
# find-in-text bar (used for the note and for files in the side pane)
# --------------------------------------------------------------------------
class FindEdit(QLineEdit):
    nextRequested = pyqtSignal()
    prevRequested = pyqtSignal()
    escapePressed = pyqtSignal()

    def keyPressEvent(self, e):
        if e.key() == Qt.Key_Escape:
            self.escapePressed.emit()
        elif e.key() in (Qt.Key_Return, Qt.Key_Enter):
            (self.prevRequested if e.modifiers() & Qt.ShiftModifier
             else self.nextRequested).emit()
        else:
            super().keyPressEvent(e)


class FindBar(QWidget):
    """Find / highlight-all bar bound to a QTextEdit or QPlainTextEdit."""
    MAX_MARKS = 5000

    def __init__(self):
        super().__init__()
        self.edit = None
        lay = QHBoxLayout(self)
        lay.setContentsMargins(4, 2, 4, 2)
        lay.setSpacing(3)
        self.input = FindEdit()
        self.input.setPlaceholderText("Find...  (Enter = next, Shift+Enter = previous, Esc = close)")
        self.input.setClearButtonEnabled(True)
        self.case = QToolButton(text="Aa")
        self.case.setCheckable(True)
        self.case.setToolTip("Match case")
        prev = QToolButton(text="\u25B2")
        prev.setToolTip("Previous match (Shift+F3)")
        nxt = QToolButton(text="\u25BC")
        nxt.setToolTip("Next match (F3)")
        close = QToolButton(text="\u2715")
        close.setToolTip("Close (Esc)")
        self.count = QLabel()
        self.count.setMinimumWidth(70)
        for w in (self.input, self.case, prev, nxt, self.count, close):
            lay.addWidget(w, 1 if w is self.input else 0)
        self.timer = QTimer(self, singleShot=True, interval=150)
        self.timer.timeout.connect(self.refresh)
        self.input.textChanged.connect(self._typed)
        self.input.nextRequested.connect(lambda: self.step(True))
        self.input.prevRequested.connect(lambda: self.step(False))
        self.input.escapePressed.connect(self.dismiss)
        self.case.toggled.connect(lambda _: self._typed())
        nxt.clicked.connect(lambda: self.step(True))
        prev.clicked.connect(lambda: self.step(False))
        close.clicked.connect(self.dismiss)
        self.hide()

    # ---- target handling
    def set_target(self, edit):
        if edit is self.edit:
            return
        self._clear_marks()
        if self.edit is not None:
            try:
                self.edit.textChanged.disconnect(self._doc_changed)
            except (TypeError, RuntimeError):
                pass
        self.edit = edit
        if edit is not None:
            edit.textChanged.connect(self._doc_changed)
        self.refresh()

    def _doc_changed(self):
        if self.isVisible():
            self.timer.start()

    def _clear_marks(self):
        if self.edit is not None:
            try:
                self.edit.setExtraSelections([])
            except RuntimeError:
                self.edit = None

    def hideEvent(self, e):
        self._clear_marks()
        super().hideEvent(e)

    def showEvent(self, e):
        super().showEvent(e)
        self.refresh()

    # ---- public API
    def open(self, text=None, from_start=False):
        self.show()
        if text is not None and self.edit is not None:
            self.input.blockSignals(True)
            self.input.setText(text)
            self.input.blockSignals(False)
            c = self.edit.textCursor()
            c.setPosition(0 if from_start else c.selectionStart())
            self.edit.setTextCursor(c)
            self.step(True)
        else:
            self.refresh()
        self.input.setFocus()
        self.input.selectAll()

    def dismiss(self):
        self.hide()
        if self.edit is not None:
            self.edit.setFocus()

    # ---- searching
    def _flags(self):
        return QTextDocument.FindCaseSensitively if self.case.isChecked() \
            else QTextDocument.FindFlags()

    def _typed(self, *_):
        if self.edit is None:
            return
        if not self.input.text():
            self.refresh()
            return
        c = self.edit.textCursor()
        if c.hasSelection():  # incremental search restarts at the current match
            c.setPosition(c.selectionStart())
            self.edit.setTextCursor(c)
        self.step(True)

    def step(self, forward=True):
        text = self.input.text()
        if self.edit is None or not text:
            return
        doc, flags = self.edit.document(), self._flags()
        if not forward:
            flags |= QTextDocument.FindBackward
        found = doc.find(text, self.edit.textCursor(), flags)
        if found.isNull():  # wrap around
            wrap = QTextCursor(doc)
            wrap.movePosition(QTextCursor.Start if forward else QTextCursor.End)
            found = doc.find(text, wrap, flags)
        if found.isNull():
            self.refresh()
            return
        self.edit.setTextCursor(found)
        self.edit.ensureCursorVisible()
        self.refresh()

    def refresh(self):
        if self.edit is None or not self.isVisible():
            return
        text = self.input.text()
        if not text:
            self._clear_marks()
            self.count.setText("")
            return
        doc, flags = self.edit.document(), self._flags()
        cur_c = self.edit.textCursor()
        cur_start = cur_c.selectionStart() if cur_c.hasSelection() else -1
        sels, current, c = [], -1, QTextCursor(doc)
        while len(sels) < self.MAX_MARKS:
            c = doc.find(text, c, flags)
            if c.isNull():
                break
            sel = QTextEdit.ExtraSelection()
            sel.cursor = c
            is_cur = c.selectionStart() == cur_start
            if is_cur:
                current = len(sels)
            sel.format.setBackground(QColor("#ff9800" if is_cur else "#ffe082"))
            sel.format.setForeground(QColor("#000000"))
            sels.append(sel)
        self.edit.setExtraSelections(sels)
        if not sels:
            self.count.setText("No results")
            self.count.setStyleSheet("color:#e53935")
        else:
            self.count.setStyleSheet("")
            n = f"{len(sels)}+" if len(sels) >= self.MAX_MARKS else str(len(sels))
            self.count.setText(f"{current + 1} / {n}" if current >= 0 else f"{n} found")


# --------------------------------------------------------------------------
# rich-text note editor
# --------------------------------------------------------------------------
# ---------------------------------------------------------------- Ask AI (agent in a terminal)
AI_PRESETS = (
    ("Explain", "Explain the following text clearly and briefly."),
    ("Summarize", "Summarize the following text in a few bullet points."),
    ("Improve writing", "Improve the wording of the following text. Keep the meaning and the language."),
    ("Find problems / ask questions", "Review the following text: point out mistakes, gaps or unclear parts."),
    ("Make a to-do list", "Turn the following text into a concise, actionable to-do list."),
)
AI_EXECUTE = (
    "The text below is a request from my notes. Treat it as a task and carry it out, "
    "do not just comment on it. Work out what action it asks for (for example: create a "
    "ticket, review changes, write or fix code, send a message, look something up) and do it "
    "with the tools you have (shell, files, git, and any MCP integrations you have set up, such "
    "as an issue tracker, wiki, chat or code hosting). If anything needed is missing or ambiguous (project, assignee, "
    "repository, branch, wording...), ask me short clarifying questions first, then proceed. "
    "Before any action that creates or changes something outside this folder (tickets, "
    "messages, pull requests), show me what you are going to do and ask for confirmation. "
    "When finished, report briefly what was done and give links or ids."
)
AI_MAX_CHARS = 20000


def agent_settings():
    """Settings shared by every 'run the agent' action (File > Cursor Agent settings)."""
    cfg = QSettings("noter", "noter")
    return {"target": cfg.value("agent_target", "auto", type=str),   # auto | ide | terminal
            "ide": cfg.value("cursor_path", "", type=str).strip(),
            "agent": cfg.value("agent_path", "", type=str).strip()}


def _exe(path):
    return bool(path) and os.path.isfile(path) and os.access(path, os.X_OK)


def _is_cursor_shim(path):
    """~/.local/bin/cursor (installed with the agent CLI) is only a shim that fails without an IDE."""
    try:
        with open(path, "rb") as f:
            return b"No Cursor IDE installation found" in f.read(4096)
    except OSError:
        return False


def find_cursor_ide(custom=""):
    """Path of the Cursor IDE launcher, or None. A path from the settings wins (a folder or the
    executable itself); otherwise: `cursor` in PATH (skipping the agent shim), the usual install
    folders, AppImages, and the Exec= line of Cursor's .desktop file."""
    if custom:
        pth = os.path.expanduser(custom)
        if os.path.isdir(pth):
            for name in ("cursor", "Cursor", "AppRun"):
                if _exe(os.path.join(pth, name)):
                    return os.path.join(pth, name)
            return None
        return pth if _exe(pth) and not _is_cursor_shim(pth) else None
    home = str(Path.home())
    cands = []
    for d in ("/usr/share/applications", "/usr/local/share/applications",
              home + "/.local/share/applications"):   # the real launcher, as the desktop uses it
        for df in sorted(glob.glob(d + "/[Cc]ursor*.desktop")):
            if "url-handler" in df:
                continue
            try:
                for line in open(df, encoding="utf-8", errors="replace"):
                    if line.startswith("Exec="):
                        parts = shlex.split(line[5:].strip())
                        if parts:
                            cands.append(parts[0])
                        break
            except (OSError, ValueError):
                pass
    cands += ["/usr/share/cursor/cursor", "/opt/Cursor/cursor", "/opt/cursor/cursor"]
    cands += [os.path.join(d, "cursor") for d in os.environ.get("PATH", "").split(os.pathsep) if d]
    cands += ["/usr/local/bin/cursor", "/snap/bin/cursor"]
    for pat in (home + "/Applications/[Cc]ursor*.AppImage", home + "/[Cc]ursor*.AppImage",
                home + "/.local/bin/[Cc]ursor*.AppImage", "/opt/[Cc]ursor*.AppImage"):
        cands += sorted(glob.glob(pat))
    for c in cands:
        if _exe(c) and not _is_cursor_shim(c):
            return c
    return None


def find_agent():
    """Cursor's CLI agent: the path from the settings, else `agent` (or `cursor-agent`)."""
    custom = os.path.expanduser(agent_settings()["agent"])
    if _exe(custom):
        return custom
    extra = os.pathsep.join([os.environ.get("PATH", ""), str(Path.home() / ".local" / "bin")])
    for name in ("agent", "cursor-agent"):
        exe = shutil.which(name, path=extra)
        if exe:
            return exe
    return None


# (executable, flag that precedes the command to run)
TERMINALS = (("gnome-terminal", "--"), ("kgx", "--"), ("tilix", "-e"), ("terminator", "-x"),
             ("konsole", "-e"), ("xfce4-terminal", "-x"), ("kitty", ""), ("alacritty", "-e"),
             ("wezterm", "start"), ("foot", ""), ("x-terminal-emulator", "-e"), ("xterm", "-e"))


def terminal_command(inner):
    for exe, flag in TERMINALS:
        path = shutil.which(exe)
        if path:
            return [path] + ([flag] if flag else []) + inner
    return None


def ai_prompt(instruction, selection, source="", label="Selected text"):
    where = f" (from {os.path.basename(source)})" if source else ""
    return f"{instruction}\n\n{label}{where}:\n\"\"\"\n{selection}\n\"\"\""


IDE_DEEPLINK = "cursor://anysphere.cursor-deeplink/prompt"
IDE_URL_LIMIT = 9900   # the IDE refuses deep-link prompts longer than 10000 (URL-encoded)
_IDE_BLOCKED = [re.compile(x, re.I) for x in (
    r"\.env(\b|\W)", r"read.*\.env.*print", r"cat.*\.ssh/id_rsa", r"upload.*passwords\.txt",
    r"dump.*token", r"dump.*password", r"exfiltrate.*credential", r"leak.*secret",
    r"how.*extract.*credential")]


def ide_prompt_problem(prompt):
    """Why the IDE would not accept this prompt through its deep link (None = fine)."""
    if 21 + len(quote(prompt, safe="!~*'()")) > IDE_URL_LIMIT:
        return "The request is too long for the Cursor IDE link."
    for ch in prompt:
        if ch not in "\r\n\t" and unicodedata.category(ch)[0] not in "LMNPSZ":
            return "The request contains characters the Cursor IDE link does not accept."
    if any(rx.search(prompt) for rx in _IDE_BLOCKED):
        return "The Cursor IDE refuses prompts that mention .env files or credentials."
    return None


def tell(parent, text, ms=9000):
    try:
        parent.window().statusBar().showMessage(text, ms)
    except Exception:
        pass


def run_in_ide(parent, ide, prompt):
    """Ask the Cursor IDE to start a new chat in Agent mode with this prompt. The IDE shows a
    'Create Chat' confirmation first - that is its own safety check, we do not bypass it."""
    url = f"{IDE_DEEPLINK}?text={quote(prompt, safe='!~*' + chr(39) + '()')}&mode=agent"
    env = {k: v for k, v in os.environ.items() if k != "ELECTRON_RUN_AS_NODE"}
    try:
        subprocess.Popen([ide, "--open-url", url], env=env, stdin=subprocess.DEVNULL,
                         stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                         start_new_session=True)
    except OSError as e:
        QMessageBox.warning(parent, "Cursor Agent", f"Could not start the Cursor IDE:\n{e}")
        return False
    tell(parent, "Sent to the Cursor IDE: confirm \"Create Chat\" in its window (Agent mode)")
    return True


def run_agent(parent, prompt, cwd=None):
    """Send a request to Cursor. Target (File > Cursor Agent settings): the Cursor IDE (a new
    Agent chat with the prompt) or the `agent` CLI in a terminal. 'Automatic' = IDE if installed,
    and the terminal agent when the IDE is missing or will not take the prompt."""
    cfg = agent_settings()
    if cfg["target"] in ("auto", "ide"):
        ide = find_cursor_ide(cfg["ide"])
        if ide is None and cfg["target"] == "ide":
            QMessageBox.warning(parent, "Cursor Agent",
                                "The Cursor IDE was not found.\nSet its location in "
                                "File > Cursor Agent settings...")
            return False
        if ide is not None:
            problem = ide_prompt_problem(prompt)
            if problem is None:
                if run_in_ide(parent, ide, prompt):
                    return True
            elif cfg["target"] == "ide" and QMessageBox.question(
                    parent, "Cursor Agent", problem + "\n\nRun it in a terminal with the "
                    "agent instead?") != QMessageBox.Yes:
                return False
            else:
                tell(parent, problem + " Using the terminal agent.")
    return run_agent_terminal(parent, prompt, cwd)


def run_agent_terminal(parent, prompt, cwd=None):
    """Open a terminal window running `agent` with `prompt` as the first message."""
    agent = find_agent()
    if not agent:
        QMessageBox.warning(parent, "Ask AI", "Could not find the Cursor `agent` command in PATH.")
        return False
    if not cwd or not os.path.isdir(cwd):
        cwd = str(Path.home())
    # the prompt is passed as a positional argument ("$2"): no shell quoting problems
    script = ('cd "$3" 2>/dev/null; "$1" "$2"; '
              'echo; echo "[agent finished - this shell stays open, type exit to close]"; '
              'exec "${SHELL:-bash}"')
    cmd = terminal_command(["bash", "-c", script, "noter-ai", agent, prompt, cwd])
    if not cmd:
        QMessageBox.warning(parent, "Ask AI", "No terminal emulator found (tried gnome-terminal, "
                            "konsole, xterm, ...).")
        return False
    try:
        subprocess.Popen(cmd, cwd=cwd, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                         stderr=subprocess.DEVNULL, start_new_session=True)
    except OSError as e:
        QMessageBox.warning(parent, "Ask AI", f"Could not start the terminal: {e}")
        return False
    return True


def selected_plain(edit):
    sel = edit.textCursor().selectedText()
    return sel.replace("\u2029", "\n").replace("\u2028", "\n").replace("\xa0", " ").strip()


def request_text(edit):
    """-> (text, what): the selection, else the line the cursor is on."""
    sel = selected_plain(edit)
    if sel:
        return sel, "selected text"
    line = edit.textCursor().block().text().replace("\xa0", " ").strip()
    return line, "current line"


def add_agent_request(menu, edit, source=""):
    """'Request to Cursor Agent' at the bottom of a context menu: sends the selected text (or the
    current line) to Cursor as a task. It can ask for missing details and confirms before
    external changes."""
    text, what = request_text(edit)
    act = QAction("Request to Cursor Agent", menu)
    act.setToolTip(f"Send the {what} to Cursor as a task (Agent mode). Where it runs: "
                   "File > Cursor Agent settings")
    act.setEnabled(bool(text))
    if text:
        if len(text) > AI_MAX_CHARS:
            text = text[:AI_MAX_CHARS] + "\n[...truncated]"
        prompt = ai_prompt(AI_EXECUTE, text, source, "Request")
        if source:
            prompt += f"\n\nThe full note is the file: {source}"
        act.triggered.connect(lambda: run_agent(edit, prompt, os.path.dirname(source) if source else None))
    menu.setToolTipsVisible(True)
    menu.addAction(act)


def add_ask_ai(menu, edit, source=""):
    """Append an 'Ask AI' submenu (acts on the selected text) to a context menu."""
    sel = selected_plain(edit)
    menu.addSeparator()
    sub = menu.addMenu("Ask AI")
    sub.setEnabled(bool(sel))
    if not sel:
        sub.setToolTip("Select some text first")
        return
    if len(sel) > AI_MAX_CHARS:
        sel = sel[:AI_MAX_CHARS] + "\n[...truncated]"
    cwd = os.path.dirname(source) if source else None

    def go(instruction, label="Selected text"):
        run_agent(edit, ai_prompt(instruction, sel, source, label), cwd)

    def custom():
        text, ok = QInputDialog.getMultiLineText(
            edit, "Ask AI", "What should the agent do with the selected text?")
        if ok and text.strip():
            go(text.strip())

    run = sub.addAction("Request to execute", lambda: go(AI_EXECUTE, "Request"))
    run.setToolTip("The agent does what the selected text asks (create a ticket, review "
                   "changes, ...) and asks for any missing details")
    sub.setToolTipsVisible(True)
    sub.addSeparator()
    for name, instruction in AI_PRESETS:
        sub.addAction(name, lambda i=instruction: go(i))
    sub.addSeparator()
    sub.addAction("Ask your own question...", custom)


URL_RE = re.compile(r"(?:https?://|ftp://|www\.)[^\s<>\"]+", re.I)


def find_urls(text):
    """-> [(start, end, url)] for every web address in text (trailing punctuation excluded)."""
    out = []
    for m in URL_RE.finditer(text):
        end = m.end()
        while end > m.start() and text[end - 1] in ".,;:!?'\u2019\u201d)]}>":
            if text[end - 1] == ")" and text[m.start():end].count("(") >= text[m.start():end].count(")"):
                break   # a balanced (...) belongs to the address
            end -= 1
        url = text[m.start():end]
        if len(url) > 4 and ("://" in url or "." in url):
            out.append((m.start(), end, ("http://" + url) if url.lower().startswith("www.") else url))
    return out


class LinkHighlighter(QSyntaxHighlighter):
    """Colours and underlines web addresses. Display only - nothing is written to the file."""
    def __init__(self, doc, edit):
        super().__init__(doc)
        self.edit = edit

    def highlightBlock(self, text):
        if "://" not in text and "www." not in text.lower():
            return
        pal = self.edit.palette()
        dark = pal.color(QPalette.Base).lightness() < 128
        fmt = QTextCharFormat()
        fmt.setForeground(QColor("#6ea8fe" if dark else "#0b5fd6"))
        fmt.setFontUnderline(True)
        for a, b, _u in find_urls(text):
            self.setFormat(a, b - a, fmt)


class NoteEditor(QTextEdit):
    def __init__(self):
        super().__init__()
        self.links = LinkHighlighter(self.document(), self)
        self.viewport().setMouseTracking(True)
        self.setAcceptRichText(True)
        f = self.font()
        f.setPointSize(BASE_PT)
        self.setFont(f)
        self.document().setDefaultFont(f)
        self.setTabStopDistance(32)
        self.setPlaceholderText("Write today's notes here...")
        self._tune_palette()
        self.stamp_actions = []
        for label, kind, key in ((f"{STAMP_DATE} Date  (2026-11-19)", "iso", "Ctrl+;"),
                                 (f"{STAMP_DATE} Date, long  (Thursday, 19 November 2026)", "long", ""),
                                 (f"{STAMP_TIME} Time  (18:30)", "time", "Ctrl+Shift+;"),
                                 (f"{STAMP_DATE}{STAMP_TIME} Date and time  (2026-11-19 18:30)", "both", "F5")):
            a = QAction(label, self)
            if key:
                a.setShortcut(QKeySequence(key))
                a.setShortcutContext(Qt.WidgetShortcut)
            a.triggered.connect(lambda _=False, k=kind: self.insert_stamp(k))
            self.addAction(a)
            self.stamp_actions.append(a)

    MAX_LIST_LEVEL, MAX_INDENT = 8, 12

    def _selected_blocks(self):
        c = self.textCursor()
        a, b = c.selectionStart(), c.selectionEnd()
        doc = self.document()
        blk, last = doc.findBlock(a), doc.findBlock(b)
        if b > a and b == last.position():   # selection ends at the start of a line: not included
            last = last.previous()
        out = []
        while blk.isValid():
            out.append(blk)
            if blk.position() >= last.position():
                break
            blk = blk.next()
        return out

    def change_indent(self, delta):
        """Indent (+1) or outdent (-1) the selected lines. List items change nesting level
        (outdenting a top-level item takes it out of the list); other paragraphs move by one
        indent step."""
        blocks = self._selected_blocks()
        if not blocks:
            return
        cur = QTextCursor(self.textCursor())
        cur.beginEditBlock()
        for blk in blocks:
            bc = QTextCursor(blk)
            lst = blk.textList()
            if lst is None:
                bf = bc.blockFormat()
                bf.setIndent(max(0, min(self.MAX_INDENT, bf.indent() + delta)))
                bc.setBlockFormat(bf)
                continue
            fmt = lst.format()
            level = fmt.indent() + delta
            if level < 1:   # outdenting a top-level item takes it out of the list
                lst.remove(blk)
                bf = bc.blockFormat()
                bf.setIndent(0)
                bc.setBlockFormat(bf)
                continue
            level = min(level, self.MAX_LIST_LEVEL)
            if level == fmt.indent():
                continue
            target = self._neighbour_list(blk, level, fmt.style())
            if target is not None:   # join the list next to it, so numbering stays continuous
                target.add(blk)
            else:
                nf = QTextListFormat(fmt)
                nf.setIndent(level)
                bc.createList(nf)
        cur.endEditBlock()
        self.setFocus()

    @staticmethod
    def _neighbour_list(blk, level, style):
        """The list of the nearest item above (else below) at this level and style. Items
        nested deeper in between do not break the search."""
        for step in ("previous", "next"):
            nb = getattr(blk, step)()
            while nb.isValid():
                lst = nb.textList()
                if lst is None:
                    break
                if lst.format().indent() == level and lst.format().style() == style:
                    return lst
                if lst.format().indent() < level:   # reached a shallower item: stop
                    break
                nb = getattr(nb, step)()
        return None

    def _can_outdent(self):
        return any(b.textList() is not None or b.blockFormat().indent() > 0
                   for b in self._selected_blocks())

    def url_at(self, pos):
        """The web address under a viewport position (typed text or a real <a href>), else None."""
        a = self.anchorAt(pos)
        if a:
            return a
        c = self.cursorForPosition(pos)
        rect = self.cursorRect(c)
        if abs(pos.y() - rect.center().y()) > rect.height():   # clicked below the last line
            return None
        blk, col = c.block(), c.positionInBlock()
        for a, b, url in find_urls(blk.text()):
            if a <= col < b or (col == b and pos.x() < rect.x() + 2 and col > a):
                return url
        return None

    def open_url(self, url):
        q = QUrl.fromUserInput(url)
        if q.isValid():
            QDesktopServices.openUrl(q)

    def _hover(self, pos, ctrl):
        over = ctrl and self.url_at(pos) is not None
        self.viewport().setCursor(Qt.PointingHandCursor if over else Qt.IBeamCursor)

    def mouseMoveEvent(self, e):
        super().mouseMoveEvent(e)
        if not e.buttons():
            self._hover(e.pos(), bool(e.modifiers() & Qt.ControlModifier))
            u = self.url_at(e.pos())
            self.viewport().setToolTip(f"Ctrl+click to open\n{u}" if u else "")


    def keyReleaseEvent(self, e):
        super().keyReleaseEvent(e)
        if e.key() == Qt.Key_Control:
            self._hover(self.viewport().mapFromGlobal(QCursor.pos()), False)

    def _add_reminder(self):
        """Reminder text = the selected line of text, else the note's name."""
        sel = selected_plain(self)
        name = os.path.splitext(os.path.basename(self.source_path))[0]
        day = QDate.fromString(name, Qt.ISODate)   # a daily note: default to its day
        if sel:
            text = " ".join(sel.split())[:200]
        else:
            text = day.toString("d MMM yyyy") if day.isValid() else name
        win = self.window()
        if hasattr(win, "add_reminder"):
            win.add_reminder(text, day if day.isValid() else None)

    def insert_stamp(self, kind):
        """Insert the current date / time at the cursor (replaces the selection)."""
        now, loc = QDateTime.currentDateTime(), QLocale()
        # the icon makes a stamp easy to spot (and to search for) in a long note
        text = {"iso": f"{STAMP_DATE} " + now.toString("yyyy-MM-dd"),
                "long": f"{STAMP_DATE} " + loc.toString(now.date(), QLocale.LongFormat),
                "time": f"{STAMP_TIME} " + now.toString("HH:mm"),
                "both": f"{STAMP_DATE} " + now.toString("yyyy-MM-dd") + f" {STAMP_TIME} "
                        + now.toString("HH:mm")}[kind]
        self.textCursor().insertText(text)
        self.setFocus()

    def _tune_palette(self):
        """Qt draws horizontal lines (<hr>) with the palette's Dark role, which is almost the
        background colour in the dark theme. Lift that one role, for this editor only."""
        app_pal = QApplication.palette()
        base, text = app_pal.color(QPalette.Base), app_pal.color(QPalette.Text)
        pal = QPalette()  # only the Dark role is overridden; everything else follows the app
        pal.setColor(QPalette.Dark, mix(base, text, 0.5) if base.lightness() < 128
                     else app_pal.color(QPalette.Dark))
        self.setPalette(pal)

    def event(self, e):
        ok = super().event(e)
        if e.type() == QEvent.ApplicationPaletteChange:  # theme switch
            self._tune_palette()
            self.links.rehighlight()
        return ok

    def fix_contrast(self, join=True):
        pal = self.palette()
        return fix_contrast(self.document(), pal.color(QPalette.Text),
                            pal.color(QPalette.Base), join)

    def insertFromMimeData(self, src):
        super().insertFromMimeData(src)
        QTimer.singleShot(0, self.fix_contrast)  # pasted text may carry bad colors

    # ---- checklist & table keyboard behaviour
    def keyPressEvent(self, e):
        key, mods = e.key(), e.modifiers()
        if key == Qt.Key_Control:   # show the hand cursor over links
            self._hover(self.viewport().mapFromGlobal(QCursor.pos()), True)
        if key in (Qt.Key_Return, Qt.Key_Enter) and not mods & Qt.ShiftModifier:
            c = self.textCursor()
            txt = c.block().text()
            if txt[:1] in (CHECK_OFF, CHECK_ON) and not c.hasSelection():
                if not txt[2:].strip() and c.atBlockEnd():
                    c.beginEditBlock()  # empty item: end the checklist
                    c.movePosition(QTextCursor.StartOfBlock)
                    c.movePosition(QTextCursor.EndOfBlock, QTextCursor.KeepAnchor)
                    c.removeSelectedText()
                    c.endEditBlock()
                    return
                if c.atBlockEnd():
                    super().keyPressEvent(e)
                    self.textCursor().insertText(CHECK_OFF + " ", self.currentCharFormat())
                    return
        if key in (Qt.Key_Tab, Qt.Key_Backtab) and not mods & Qt.ControlModifier \
                and not self.textCursor().currentTable():
            c = self.textCursor()
            multi = len(self._selected_blocks()) > 1
            if key == Qt.Key_Tab and (multi or c.currentList() is not None):
                self.change_indent(1)   # Tab indents list items and multi-line selections
                return
            if key == Qt.Key_Backtab and self._can_outdent():
                self.change_indent(-1)
                return
        if key in (Qt.Key_Tab, Qt.Key_Backtab) and not mods & Qt.ControlModifier:
            c = self.textCursor()
            table = c.currentTable()
            if table:
                cell = table.cellAt(c)
                idx = cell.row() * table.columns() + cell.column()
                idx += 1 if key == Qt.Key_Tab else -1
                if idx < 0:
                    return
                if idx >= table.rows() * table.columns():
                    table.appendRows(1)
                r, col = divmod(idx, table.columns())
                self.setTextCursor(table.cellAt(r, col).firstCursorPosition())
                return
        super().keyPressEvent(e)

    def mouseReleaseEvent(self, e):
        if e.button() == Qt.LeftButton and e.modifiers() & Qt.ControlModifier:
            u = self.url_at(e.pos())
            if u:   # Ctrl+click opens a web link
                self.open_url(u)
                e.accept()
                return
        super().mouseReleaseEvent(e)
        if e.button() != Qt.LeftButton or self.textCursor().hasSelection():
            return
        c = self.cursorForPosition(e.pos())
        block = c.block()
        if block.text()[:1] not in (CHECK_OFF, CHECK_ON):
            return
        start = QTextCursor(block)
        end = QTextCursor(block)
        end.setPosition(block.position() + 1)
        x0, x1 = self.cursorRect(start).x(), self.cursorRect(end).x()
        if x0 <= e.pos().x() <= x1 and self.cursorRect(start).top() <= e.pos().y() \
                <= self.cursorRect(start).bottom():
            c = QTextCursor(block)
            c.movePosition(QTextCursor.Right, QTextCursor.KeepAnchor)
            fmt = c.charFormat()
            new = CHECK_OFF if block.text()[0] == CHECK_ON else CHECK_ON
            c.insertText(new, fmt)

    # ---- table helpers / context menu
    source_path = ""  # file this editor shows (set by the tab), used as the agent's folder

    def contextMenuEvent(self, e):
        menu = self.createStandardContextMenu()
        url = self.url_at(e.pos())
        if url:
            first = menu.actions()[0] if menu.actions() else None
            a1 = QAction("Open link in browser", menu, triggered=lambda: self.open_url(url))
            a2 = QAction("Copy link address", menu, triggered=lambda: QApplication.clipboard().setText(url))
            menu.insertAction(first, a1)
            menu.insertAction(first, a2)
            menu.insertSeparator(first)
        c = self.cursorForPosition(e.pos())
        table = c.currentTable()
        if table:
            cell = table.cellAt(c)
            menu.addSeparator()
            sub = menu.addMenu("Table")
            sub.addAction("Insert row above", lambda: table.insertRows(cell.row(), 1))
            sub.addAction("Insert row below", lambda: table.insertRows(cell.row() + 1, 1))
            sub.addAction("Insert column left", lambda: table.insertColumns(cell.column(), 1))
            sub.addAction("Insert column right", lambda: table.insertColumns(cell.column() + 1, 1))
            sub.addSeparator()
            a = sub.addAction("Delete row", lambda: table.removeRows(cell.row(), 1))
            a.setEnabled(table.rows() > 1)
            a = sub.addAction("Delete column", lambda: table.removeColumns(cell.column(), 1))
            a.setEnabled(table.columns() > 1)
            sub.addAction("Delete table", lambda: table.removeRows(0, table.rows()))
            shade = menu.addMenu("Cell color")
            shade.addAction("None", lambda: self._cell_color(table, cell, None))
            for name, col in HIGHLIGHTS:
                shade.addAction(color_icon(col), name,
                                lambda col=col: self._cell_color(table, cell, col))
        menu.addSeparator()
        menu.addAction("Add reminder...", self._add_reminder)
        ins = menu.addMenu("Insert")
        for a in self.stamp_actions:
            ins.addAction(a)
        add_ask_ai(menu, self, self.source_path)
        add_agent_request(menu, self, self.source_path)
        menu.exec_(e.globalPos())

    def _cell_color(self, table, cell, color):
        fmt = QTextTableCellFormat()
        if color:
            fmt.setBackground(QColor(color))
        cell.setFormat(fmt)
        self.fix_contrast()  # keep text readable on the new background

    def insert_table(self, rows, cols):
        fmt = QTextTableFormat()
        fmt.setBorder(1)
        fmt.setBorderStyle(QTextTableFormat.BorderStyle_Solid)
        fmt.setBorderBrush(QBrush(QColor("#9e9e9e")))
        fmt.setCellPadding(5)
        fmt.setCellSpacing(0)
        fmt.setWidth(QTextLength(QTextLength.PercentageLength, 100))
        c = self.textCursor()
        table = c.insertTable(rows, cols, fmt)
        c.insertBlock()  # keep a line to type below the table
        self.setTextCursor(table.cellAt(0, 0).firstCursorPosition())


class TableDialog(QDialog):
    def __init__(self, parent):
        super().__init__(parent)
        self.setWindowTitle("Insert table")
        form = QFormLayout(self)
        self.rows = QSpinBox()
        self.rows.setRange(1, 100)
        self.rows.setValue(3)
        self.cols = QSpinBox()
        self.cols.setRange(1, 20)
        self.cols.setValue(3)
        form.addRow("Rows", self.rows)
        form.addRow("Columns", self.cols)
        bb = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        bb.accepted.connect(self.accept)
        bb.rejected.connect(self.reject)
        form.addRow(bb)


class NotePanel(QWidget):
    """Formatting toolbars + rich-text editor + find bar."""

    def __init__(self):
        super().__init__()
        lay = QVBoxLayout(self)
        lay.setContentsMargins(4, 4, 4, 4)
        lay.setSpacing(2)

        self.editor = NoteEditor()
        self._build_toolbars(lay)
        lay.addWidget(self.editor, 1)
        self.findbar = FindBar()
        self.findbar.set_target(self.editor)
        lay.addWidget(self.findbar)
        self.editor.currentCharFormatChanged.connect(self._sync_format)
        self.editor.cursorPositionChanged.connect(self._sync_blocks)

    # ---- toolbars
    def _action(self, bar, text, tip, slot, checkable=False, shortcut=None):
        a = QAction(text, self)
        a.setToolTip(tip + (f" ({shortcut})" if shortcut else ""))
        a.setCheckable(checkable)
        if shortcut:
            a.setShortcut(QKeySequence(shortcut))
            a.setShortcutContext(Qt.WidgetWithChildrenShortcut)
        a.triggered.connect(slot)
        bar.addAction(a)
        return a

    def _color_button(self, bar, label, tip, colors, apply_fn, reset_fn):
        btn = QToolButton()
        btn.setText(label)
        btn.setToolTip(tip)
        btn.setPopupMode(QToolButton.InstantPopup)
        menu = QMenu(btn)
        for name, col in colors:
            menu.addAction(color_icon(col), name, lambda col=col: apply_fn(QColor(col)))
        menu.addAction("Custom...", lambda: self._pick_custom(apply_fn))
        menu.addSeparator()
        menu.addAction("Reset", reset_fn)
        btn.setMenu(menu)
        bar.addWidget(btn)

    def _pick_custom(self, apply_fn):
        from PyQt5.QtWidgets import QColorDialog
        col = QColorDialog.getColor(parent=self)
        if col.isValid():
            apply_fn(col)

    def _build_toolbars(self, lay):
        bar1, bar2, bar3 = QToolBar(), QToolBar(), QToolBar()
        for b in (bar1, bar2, bar3):
            b.setIconSize(QSize(16, 16))
            b.layout().setSpacing(2)   # no stylesheets: they freeze colours across theme switches
            b.layout().setContentsMargins(0, 0, 0, 0)
            lay.addWidget(b)

        self.heading = QComboBox()
        self.heading.addItems(["Normal", "Heading 1", "Heading 2", "Heading 3"])
        self.heading.activated.connect(self.set_heading)
        bar1.addWidget(self.heading)

        self.act_bold = self._action(bar1, "B", "Bold", self.toggle_bold, True, "Ctrl+B")
        self.act_italic = self._action(bar1, "I", "Italic", self.toggle_italic, True, "Ctrl+I")
        self.act_under = self._action(bar1, "U", "Underline", self.toggle_under, True, "Ctrl+U")
        self.act_strike = self._action(bar1, "S", "Strikethrough", self.toggle_strike, True)
        for act, attr in ((self.act_bold, "setBold"), (self.act_italic, "setItalic"),
                          (self.act_under, "setUnderline"), (self.act_strike, "setStrikeOut")):
            w = bar1.widgetForAction(act)
            f = w.font()
            getattr(f, attr)(True)
            w.setFont(f)
            w.setMinimumWidth(24)
        bar1.addSeparator()
        self._color_button(bar1, "A Color", "Text color", PALETTE,
                           self.set_text_color, self.reset_text_color)
        self._color_button(bar1, "Highlight", "Highlight color", HIGHLIGHTS,
                           self.set_highlight, self.reset_highlight)
        self._action(bar1, "Clear", "Clear formatting", self.clear_format)

        self.act_bullet = self._action(bar2, "\u2022 List", "Bullet list",
                                       lambda: self.toggle_list(QTextListFormat.ListDisc), True)
        self.act_number = self._action(bar2, "1. List", "Numbered list",
                                       lambda: self.toggle_list(QTextListFormat.ListDecimal), True)
        self._action(bar2, "\u2611 Checklist", "Toggle checklist (click a box to tick it)",
                     self.toggle_checklist, False, "Ctrl+L")
        bar2.addSeparator()
        self._action(bar2, "\u25A6 Table", "Insert table", self.insert_table)
        self._action(bar2, "\u2014 Line", "Insert horizontal line",
                     lambda: self.editor.textCursor().insertHtml("<hr>"))
        ins = QToolButton()
        ins.setText(STAMP_DATE + " Insert")
        ins.setToolTip("Insert date / time (Ctrl+; date, Ctrl+Shift+; time, F5 date and time)")
        ins.setPopupMode(QToolButton.InstantPopup)
        ins_menu = QMenu(ins)
        for a in self.editor.stamp_actions:
            ins_menu.addAction(a)
        ins.setMenu(ins_menu)
        bar2.addWidget(ins)
        self._action(bar3, "\u21E4 Outdent", "Outdent: move the line or list item out (also Shift+Tab)",
                     lambda: self.editor.change_indent(-1), False, "Ctrl+[")
        self._action(bar3, "\u21E5 Indent", "Indent: move the line or list item in (also Tab in a list)",
                     lambda: self.editor.change_indent(1), False, "Ctrl+]")
        bar3.addSeparator()
        self._action(bar3, "\u2190", "Align left", lambda: self.editor.setAlignment(Qt.AlignLeft))
        self._action(bar3, "\u2194", "Center", lambda: self.editor.setAlignment(Qt.AlignHCenter))
        self._action(bar3, "\u2192", "Align right", lambda: self.editor.setAlignment(Qt.AlignRight))

    def show_find(self, text=None, from_start=False):
        if text is None:
            sel = self.editor.textCursor().selectedText()
            if sel and "\u2029" not in sel and len(sel) <= 100:
                text = sel
        self.findbar.open(text, from_start)

    # ---- formatting actions
    def _merge(self, fmt):
        self.editor.mergeCurrentCharFormat(fmt)
        self.editor.setFocus()

    def toggle_bold(self, on):
        f = QTextCharFormat()
        f.setFontWeight(QFont.Bold if on else QFont.Normal)
        self._merge(f)

    def toggle_italic(self, on):
        f = QTextCharFormat()
        f.setFontItalic(on)
        self._merge(f)

    def toggle_under(self, on):
        f = QTextCharFormat()
        f.setFontUnderline(on)
        self._merge(f)

    def toggle_strike(self, on):
        f = QTextCharFormat()
        f.setFontStrikeOut(on)
        self._merge(f)

    def set_text_color(self, color):
        f = QTextCharFormat()
        f.setForeground(color)
        self._merge(f)

    def _reset_attr(self, clear):
        c = self.editor.textCursor()
        f = c.charFormat()
        clear(f)
        if c.hasSelection():
            c.setCharFormat(f)
        else:
            self.editor.setCurrentCharFormat(f)
        self.editor.setFocus()

    def reset_text_color(self):
        self._reset_attr(lambda f: f.clearForeground())

    def set_highlight(self, color):
        f = QTextCharFormat()
        f.setBackground(color)
        self._merge(f)
        self.editor.fix_contrast()

    def reset_highlight(self):
        self._reset_attr(lambda f: f.clearBackground())

    def clear_format(self):
        c = self.editor.textCursor()
        base = QTextCharFormat()
        base.setFontPointSize(BASE_PT)
        if c.hasSelection():
            c.setCharFormat(base)
        else:
            self.editor.setCurrentCharFormat(base)
        self.editor.setFocus()

    def set_heading(self, idx):
        sizes = {0: BASE_PT, 1: 22, 2: 17, 3: 14}
        c = self.editor.textCursor()
        c.beginEditBlock()
        if not c.hasSelection():
            c.select(QTextCursor.LineUnderCursor)
        f = QTextCharFormat()
        f.setFontPointSize(sizes[idx])
        f.setFontWeight(QFont.Bold if idx else QFont.Normal)
        c.mergeCharFormat(f)
        if hasattr(c.blockFormat(), "setHeadingLevel"):
            bf = c.blockFormat()
            bf.setHeadingLevel(idx)
            c.setBlockFormat(bf)
        c.endEditBlock()
        self.editor.setFocus()

    def toggle_list(self, style):
        c = self.editor.textCursor()
        cur = c.currentList()
        c.beginEditBlock()
        if cur and cur.format().style() == style:
            for i in range(cur.count() - 1, -1, -1):
                blk = cur.item(i)
                if c.selectionStart() <= blk.position() + blk.length() and \
                        blk.position() <= max(c.selectionEnd(), c.position()):
                    cur.remove(blk)
                    bc = QTextCursor(blk)
                    bf = bc.blockFormat()
                    bf.setIndent(0)
                    bc.setBlockFormat(bf)
        else:
            fmt = QTextListFormat()
            fmt.setStyle(style)
            fmt.setIndent(1)
            c.createList(fmt)
        c.endEditBlock()
        self._sync_blocks()
        self.editor.setFocus()

    def toggle_checklist(self):
        c = self.editor.textCursor()
        start, end = sorted((c.position(), c.anchor()))
        doc = self.editor.document()
        first, last = doc.findBlock(start), doc.findBlock(end)
        blocks = []
        b = first
        while b.isValid():
            blocks.append(b)
            if b == last:
                break
            b = b.next()
        remove = all(b.text()[:1] in (CHECK_OFF, CHECK_ON) for b in blocks)
        c.beginEditBlock()
        for b in blocks:
            bc = QTextCursor(b)
            if remove:
                bc.movePosition(QTextCursor.Right, QTextCursor.KeepAnchor,
                                2 if b.text()[1:2] == " " else 1)
                bc.removeSelectedText()
            else:
                bc.insertText(CHECK_OFF + " ")
        c.endEditBlock()
        self.editor.setFocus()

    def insert_table(self):
        dlg = TableDialog(self)
        if dlg.exec_():
            self.editor.insert_table(dlg.rows.value(), dlg.cols.value())
            self.editor.setFocus()

    # ---- toolbar state follows the cursor
    def _sync_format(self, fmt):
        for act, val in ((self.act_bold, fmt.fontWeight() > QFont.Normal),
                         (self.act_italic, fmt.fontItalic()),
                         (self.act_under, fmt.fontUnderline()),
                         (self.act_strike, fmt.fontStrikeOut())):
            act.setChecked(val)

    def _sync_blocks(self):
        lst = self.editor.textCursor().currentList()
        style = lst.format().style() if lst else None
        self.act_bullet.setChecked(style == QTextListFormat.ListDisc)
        self.act_number.setChecked(style == QTextListFormat.ListDecimal)
        bf = self.editor.textCursor().blockFormat()
        lvl = bf.headingLevel() if hasattr(bf, "headingLevel") else 0
        self.heading.setCurrentIndex(min(lvl, 3))


# --------------------------------------------------------------------------
# reminders
# --------------------------------------------------------------------------
class AgentSettingsDialog(QDialog):
    """Where 'Request to Cursor Agent' / 'Ask AI' run, and where Cursor is installed."""

    def __init__(self, parent):
        super().__init__(parent)
        self.setWindowTitle("Cursor Agent settings")
        self.setMinimumWidth(560)
        cfg = agent_settings()
        form = QFormLayout(self)
        self.target = QComboBox()
        for key, label in (("auto", "Automatic: Cursor IDE if installed, else terminal agent"),
                           ("ide", "Cursor IDE: new Agent chat with the prompt"),
                           ("terminal", "Terminal: run the `agent` CLI")):
            self.target.addItem(label, key)
        self.target.setCurrentIndex(max(0, self.target.findData(cfg["target"])))
        form.addRow("Run in", self.target)
        self.ide, ide_row = self._path_row(cfg["ide"], "Cursor IDE: folder or executable")
        form.addRow("Cursor IDE", ide_row)
        self.ide_found = QLabel()
        form.addRow("", self.ide_found)
        self.agent, agent_row = self._path_row(cfg["agent"], "agent CLI executable")
        form.addRow("Agent CLI", agent_row)
        self.agent_found = QLabel()
        form.addRow("", self.agent_found)
        note = QLabel("The IDE asks you to confirm \"Create Chat\" before it starts the agent. "
                      "Very long requests do not fit the IDE link and use the terminal agent. "
                      "Leave the paths empty to detect them automatically.")
        note.setWordWrap(True)
        note.setMinimumHeight(60)
        form.addRow(note)
        for e in (self.ide, self.agent):
            e.textChanged.connect(self._detect)
        self._detect()
        bb = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        bb.accepted.connect(self.accept)
        bb.rejected.connect(self.reject)
        form.addRow(bb)
        self.setMinimumHeight(self.sizeHint().height() + 30)

    def _path_row(self, value, placeholder):
        row = QHBoxLayout()
        edit = QLineEdit(value)
        edit.setPlaceholderText(placeholder + " (empty = automatic)")
        btn = QPushButton("Browse...")
        btn.clicked.connect(lambda: self._browse(edit))
        row.addWidget(edit, 1)
        row.addWidget(btn)
        box = QWidget()
        box.setLayout(row)
        row.setContentsMargins(0, 0, 0, 0)
        return edit, box

    def _browse(self, edit):
        path, _ = QFileDialog.getOpenFileName(self, "Choose the executable", edit.text() or "/usr")
        if path:
            edit.setText(path)

    def _detect(self):
        ide = find_cursor_ide(self.ide.text().strip())
        self.ide_found.setText(f"Found: {ide}" if ide else "Not found")
        cli = os.path.expanduser(self.agent.text().strip())
        cli = cli if _exe(cli) else (None if cli else find_agent())
        self.agent_found.setText(f"Found: {cli}" if cli else "Not found")

    def save(self):
        cfg = QSettings("noter", "noter")
        cfg.setValue("agent_target", self.target.currentData())
        cfg.setValue("cursor_path", self.ide.text().strip())
        cfg.setValue("agent_path", self.agent.text().strip())


class ReminderDialog(QDialog):
    def __init__(self, parent, when, text="", repeat="none"):
        super().__init__(parent)
        self.setWindowTitle("Reminder")
        self.setMinimumWidth(360)
        form = QFormLayout(self)
        self.text = QLineEdit(text)
        self.when = QDateTimeEdit(when)
        self.when.setCalendarPopup(True)
        self.when.setDisplayFormat("ddd d MMM yyyy  HH:mm")
        self.repeat = QComboBox()
        self.repeat.addItems(["none", "daily", "weekly"])
        self.repeat.setCurrentText(repeat)
        form.addRow("What", self.text)
        form.addRow("When", self.when)
        form.addRow("Repeat", self.repeat)
        bb = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        bb.accepted.connect(self.accept)
        bb.rejected.connect(self.reject)
        form.addRow(bb)
        self.text.setFocus()


# --------------------------------------------------------------------------
# file explorer
# --------------------------------------------------------------------------
class ExplorerPanel(QWidget):
    fileActivated = pyqtSignal(str)   # default open (notes go left, everything else right)
    openSide = pyqtSignal(str)        # force the right pane
    reminderRequested = pyqtSignal(str)   # "Add reminder..." on a .noter file

    def __init__(self, start):
        super().__init__()
        lay = QVBoxLayout(self)
        lay.setContentsMargins(4, 4, 4, 4)
        lay.setSpacing(2)

        top = QHBoxLayout()
        home = QToolButton(text="\u2302")
        home.setToolTip("Home folder")
        up = QToolButton(text="\u2191")
        up.setToolTip("Parent folder")
        self.hidden = QToolButton(text=".*")
        self.hidden.setCheckable(True)
        self.hidden.setToolTip("Show hidden files")
        self.path = QLineEdit()
        self.path.setPlaceholderText("Path...")
        top.addWidget(home)
        top.addWidget(up)
        top.addWidget(self.path, 1)
        top.addWidget(self.hidden)
        lay.addLayout(top)

        self.model = QFileSystemModel(self)
        self.model.setReadOnly(False)
        self._set_filter(False)
        self.model.setRootPath("")
        self.tree = QTreeView()
        self.tree.setModel(self.model)
        for col in (1, 2, 3):
            self.tree.hideColumn(col)
        self.tree.setHeaderHidden(True)
        self.tree.setAnimated(True)
        self.tree.setUniformRowHeights(True)
        self.tree.setSortingEnabled(True)
        self.tree.sortByColumn(0, Qt.AscendingOrder)
        self.tree.setEditTriggers(QAbstractItemView.EditKeyPressed)
        self.tree.setContextMenuPolicy(Qt.CustomContextMenu)
        self.tree.customContextMenuRequested.connect(self._menu)
        self.tree.activated.connect(self._activated)
        self.tree.doubleClicked.connect(self._activated)
        lay.addWidget(self.tree, 1)

        home.clicked.connect(lambda: self.set_root(str(Path.home())))
        up.clicked.connect(lambda: self.set_root(str(Path(self.root).parent)))
        self.path.returnPressed.connect(lambda: self.set_root(self.path.text()))
        self.hidden.toggled.connect(self._set_filter)
        self.root = ""
        self.set_root(start)

    def _set_filter(self, hidden):
        flags = QDir.AllEntries | QDir.NoDotAndDotDot | QDir.AllDirs
        if hidden:
            flags |= QDir.Hidden
        self.model.setFilter(flags)

    def set_root(self, path):
        path = os.path.expanduser(path.strip())
        if not os.path.isdir(path):
            return
        self.root = os.path.abspath(path)
        self.tree.setRootIndex(self.model.index(self.root))
        self.path.setText(self.root)

    def _path_of(self, index):
        return self.model.filePath(index)

    def _activated(self, index):
        p = self._path_of(index)
        if os.path.isfile(p):
            self.fileActivated.emit(p)

    def _target_dir(self):
        idx = self.tree.currentIndex()
        if not idx.isValid():
            return self.root
        p = self._path_of(idx)
        return p if os.path.isdir(p) else os.path.dirname(p)

    def _menu(self, pos):
        idx = self.tree.indexAt(pos)
        menu = QMenu(self)
        if idx.isValid():
            p = self._path_of(idx)
            isfile = os.path.isfile(p)
            if isfile:
                menu.addAction("Open", lambda: self.fileActivated.emit(p))
                if p.lower().endswith(NOTER_EXT):
                    menu.addAction("Open in right pane", lambda: self.openSide.emit(p))
                    menu.addAction("Add reminder...", lambda: self.reminderRequested.emit(p))
            menu.addAction("Open with system app",
                           lambda: QDesktopServices.openUrl(QUrl.fromLocalFile(p)))
            if not isfile:
                menu.addAction("Set as root", lambda: self.set_root(p))
            menu.addSeparator()
        menu.addAction("New note...", self.new_noter)
        menu.addAction("New file...", self.new_file)
        menu.addAction("New folder...", self.new_folder)
        if idx.isValid():
            menu.addAction("Rename (F2)", lambda: self.tree.edit(idx))
            menu.addAction("Copy path", lambda: QApplication.clipboard().setText(p))
            menu.addAction("Move to trash", lambda: self.trash(p))
        menu.exec_(self.tree.viewport().mapToGlobal(pos))

    def new_noter(self):
        name, ok = QInputDialog.getText(self, "New note", "Note name:")
        name = name.strip().replace("/", "-")
        if not ok or not name:
            return
        if not name.lower().endswith(NOTER_EXT):
            name += NOTER_EXT
        p = os.path.join(self._target_dir(), name)
        if os.path.exists(p):
            QMessageBox.warning(self, "New note", f"{name} already exists.")
        else:
            try:
                Path(p).touch()
            except OSError as e:
                QMessageBox.warning(self, "New note", str(e))
                return
        self.fileActivated.emit(p)

    def new_file(self):
        name, ok = QInputDialog.getText(self, "New file", "File name:")
        if ok and name.strip():
            p = os.path.join(self._target_dir(), name.strip())
            try:
                Path(p).touch(exist_ok=False)
            except OSError as e:
                QMessageBox.warning(self, "New file", str(e))
                return
            self.fileActivated.emit(p)

    def new_folder(self):
        name, ok = QInputDialog.getText(self, "New folder", "Folder name:")
        if ok and name.strip():
            try:
                os.makedirs(os.path.join(self._target_dir(), name.strip()))
            except OSError as e:
                QMessageBox.warning(self, "New folder", str(e))

    def trash(self, path):
        if QMessageBox.question(self, "Trash", f"Move to trash?\n{path}") != QMessageBox.Yes:
            return
        if shutil.which("gio"):
            r = subprocess.run(["gio", "trash", path], capture_output=True, text=True)
            if r.returncode != 0:
                QMessageBox.warning(self, "Trash", r.stderr or "Failed")
        else:
            QMessageBox.information(self, "Trash", "`gio` not found - cannot trash safely.")


# --------------------------------------------------------------------------
# side pane with arbitrary files
# --------------------------------------------------------------------------
# --------------------------------------------------------------------------
# syntax highlighting for code files (Pygments does the lexing: ~500 languages)
# --------------------------------------------------------------------------
HL_MAX_CHARS = 600_000   # bigger files are shown without highlighting (keeps typing fast)

# category -> (dark theme color, light theme color, bold, italic)
HL_STYLE = {
    "comment":  ("#7f9a6a", "#3f7f2f", False, True),
    "keyword":  ("#c792ea", "#8f2fb8", True, False),
    "type":     ("#4ec9b0", "#127a78", False, False),
    "builtin":  ("#6cb6ff", "#0b64c0", False, False),
    "function": ("#e6d98f", "#7a5a12", False, False),
    "class":    ("#4ec9b0", "#127a78", True, False),
    "string":   ("#f0a57e", "#b3361b", False, False),
    "number":   ("#b5e0a0", "#0a7a4b", False, False),
    "const":    ("#7cc4ff", "#1f45b8", False, False),
    "decorator": ("#e6d98f", "#7a5a12", False, False),
    "preproc":  ("#d89cdc", "#a03a9a", False, False),
    "tag":      ("#6cb6ff", "#a31515", False, False),
    "attr":     ("#9cdcfe", "#c2410c", False, False),
    "operator": ("#d0d4dc", "#444444", False, False),
    "heading":  ("#6cb6ff", "#0b64c0", True, False),
    "strong":   (None, None, True, False),
    "emph":     (None, None, False, True),
    "deleted":  ("#ff8b8b", "#b01919", False, False),
    "inserted": ("#8fe08f", "#17701c", False, False),
}


def _token_category(t):
    """Map a Pygments token type to one of our categories (None = leave plain)."""
    if not HAVE_PYGMENTS:
        return None
    T = Token
    if t in T.Comment.Preproc or t in T.Comment.PreprocFile:
        return "preproc"
    if t in T.Comment:
        return "comment"
    if t in T.Literal.String.Doc:
        return "comment"
    if t in T.Literal.String:
        return "string"
    if t in T.Literal.Number:
        return "number"
    if t in T.Keyword.Type:
        return "type"
    if t in T.Keyword.Constant or t in T.Name.Constant or t in T.Name.Builtin.Pseudo:
        return "const"
    if t in T.Keyword or t in T.Operator.Word:
        return "keyword"
    if t in T.Name.Decorator:
        return "decorator"
    if t in T.Name.Builtin:
        return "builtin"
    if t in T.Name.Function or t in T.Name.Function.Magic:
        return "function"
    if t in T.Name.Class or t in T.Name.Namespace or t in T.Name.Exception:
        return "class"
    if t in T.Name.Tag:
        return "tag"
    if t in T.Name.Attribute:
        return "attr"
    if t in T.Operator:
        return "operator"
    if t in T.Generic.Heading or t in T.Generic.Subheading:
        return "heading"
    if t in T.Generic.Strong:
        return "strong"
    if t in T.Generic.Emph:
        return "emph"
    if t in T.Generic.Deleted:
        return "deleted"
    if t in T.Generic.Inserted:
        return "inserted"
    return None


_SHEBANG = {"python": "python", "bash": "bash", "sh": "bash", "zsh": "bash", "node": "javascript",
            "ruby": "ruby", "perl": "perl", "php": "php", "lua": "lua"}


def pick_lexer(path, text):
    """Pygments lexer for a file (by name, then by #! line), or None for plain text."""
    if not HAVE_PYGMENTS:
        return None
    lexer = None
    try:
        lexer = get_lexer_for_filename(path)
        if path.lower().endswith(".sql"):   # Pygments' first guess is Transact-SQL
            lexer = get_lexer_by_name("sql")
    except ClassNotFound:
        m = re.match(r"#!\s*(?:/usr/bin/env\s+(?:-\S+\s+)*)?\S*?([a-z]+)\d*(?:\s|$)", text[:200])
        if m and m.group(1) in _SHEBANG:
            try:
                lexer = get_lexer_by_name(_SHEBANG[m.group(1)])
            except ClassNotFound:
                lexer = None
    except Exception:
        lexer = None
    if lexer is not None and lexer.name.lower() in ("text only", "text"):
        return None
    return lexer


class SyntaxHighlighter(QSyntaxHighlighter):
    """Colours blocks from token spans computed by lexing the whole document
    (so multi-line strings/comments are right); relex() is called after edits stop."""

    def __init__(self, doc, lexer):
        super().__init__(doc)
        self.lexer = lexer
        self.spans = {}      # block number -> [(start, length, QTextCharFormat)]
        self._fmt = {}
        self.dark = True
        self.set_theme()

    def set_theme(self):
        self.dark = QApplication.palette().color(QPalette.Base).lightness() < 128
        self._fmt = {}
        for cat, (d, l, bold, italic) in HL_STYLE.items():
            f = QTextCharFormat()
            col = d if self.dark else l
            if col:
                f.setForeground(QColor(col))
            if bold:
                f.setFontWeight(QFont.Bold)
            f.setFontItalic(italic)
            self._fmt[cat] = f

    def relex(self, text):
        spans, cache = {}, {}
        if len(text) > HL_MAX_CHARS:
            self.spans = spans
            return
        starts, pos = [], 0
        lines = text.split("\n")
        for ln in lines:
            starts.append(pos)
            pos += len(ln) + 1
        astral = {i for i, ln in enumerate(lines) if any(ord(c) > 0xFFFF for c in ln)}
        from bisect import bisect_right

        def u16(i, col):  # code-point column -> UTF-16 column (Qt) on lines with emoji etc.
            return col + sum(1 for c in lines[i][:col] if ord(c) > 0xFFFF) if i in astral else col

        try:
            for idx, ttype, val in self.lexer.get_tokens_unprocessed(text):
                cat = cache.get(ttype, 0)
                if cat == 0:
                    cat = cache[ttype] = _token_category(ttype)
                if cat is None or not val:
                    continue
                fmt = self._fmt[cat]
                ln = bisect_right(starts, idx) - 1
                col = idx - starts[ln]
                for part in val.split("\n"):
                    if part.strip():
                        a = u16(ln, col)
                        spans.setdefault(ln, []).append((a, u16(ln, col + len(part)) - a, fmt))
                    ln, col = ln + 1, 0
        except Exception:   # a lexer may choke on odd input: keep what we have
            pass
        self.spans = spans

    def highlightBlock(self, _text):
        for start, length, fmt in self.spans.get(self.currentBlock().blockNumber(), ()):
            self.setFormat(start, length, fmt)


class TextTab(QPlainTextEdit):
    edited = pyqtSignal()   # real text edits only (not re-highlighting)

    def __init__(self, path, text, encoding):
        super().__init__()
        self.path, self.encoding = path, encoding
        self._rehl = False
        self.setFont(QFontDatabase.systemFont(QFontDatabase.FixedFont))
        self.setLineWrapMode(QPlainTextEdit.NoWrap)
        self.setTabStopDistance(self.fontMetrics().horizontalAdvance(" ") * 4)
        self.setPlainText(text)
        self.document().setModified(False)
        self.language = ""
        self.hl = None
        lexer = pick_lexer(path, text)
        if lexer is not None:
            self.language = lexer.name
            self.hl = SyntaxHighlighter(self.document(), lexer)
            self.hl_timer = QTimer(self, singleShot=True, interval=250)
            self.hl_timer.timeout.connect(self._rehighlight)
            self._rehighlight()
        self.document().contentsChanged.connect(self._contents_changed)

    def _contents_changed(self):
        if self._rehl:   # re-highlighting also "changes" the document - ignore that
            return
        self.edited.emit()
        if self.hl is not None:
            self.hl_timer.start()

    def _rehighlight(self):
        mod = self.document().isModified()
        self._rehl = True
        try:
            self.hl.relex(self.toPlainText())
            self.hl.rehighlight()
        finally:
            self._rehl = False
        self.document().setModified(mod)

    def event(self, e):
        ok = super().event(e)
        if e.type() == QEvent.ApplicationPaletteChange and self.hl is not None:  # theme switch
            self.hl.set_theme()
            self._rehighlight()
        return ok

    def contextMenuEvent(self, e):
        menu = self.createStandardContextMenu()
        add_ask_ai(menu, self, self.path)
        add_agent_request(menu, self, self.path)
        menu.exec_(e.globalPos())

    def goto_line(self, line):
        blk = self.document().findBlockByNumber(max(0, line - 1))
        self.setTextCursor(QTextCursor(blk))
        self.centerCursor()

    def save(self):
        with open(self.path, "w", encoding=self.encoding, newline="") as f:
            f.write(self.toPlainText())
        self.document().setModified(False)

    def is_modified(self):
        return self.document().isModified()


if HAVE_WEBKIT:
    class PreviewView(QWebView):
        """Web view with Ctrl+wheel zoom."""
        def wheelEvent(self, e):
            if e.modifiers() & Qt.ControlModifier:
                z = self.zoomFactor() * (1.15 if e.angleDelta().y() > 0 else 1 / 1.15)
                self.setZoomFactor(min(5.0, max(0.25, z)))
                e.accept()
            else:
                super().wheelEvent(e)


class HtmlTab(QWidget):
    """An HTML file with three views: Source (editor), Browser (rendered page) and Split
    (editor and live page side by side). The editor is a normal TextTab."""
    modeChanged = pyqtSignal(str)
    openRequested = pyqtSignal(str)

    def __init__(self, editor):
        super().__init__()
        self.editor, self.path, self.mode = editor, editor.path, "source"
        self.web = None
        self._scroll = None
        self.timer = QTimer(self, singleShot=True, interval=400)
        self.timer.timeout.connect(self._render)
        editor.edited.connect(self._text_changed)

        bar = QHBoxLayout()
        bar.setContentsMargins(4, 2, 4, 2)
        self.buttons = {}
        for key, label, tip in (("source", "Source", "Edit the HTML"),
                                ("split", "Split", "Source and live page side by side"),
                                ("browser", "Browser", "Show the rendered page")):
            b = QToolButton(text=label, checkable=True, autoRaise=True, toolTip=tip)
            b.clicked.connect(lambda _c, k=key: self.set_mode(k))
            bar.addWidget(b)
            self.buttons[key] = b
        self.reload_btn = QToolButton(text="\u27F3", autoRaise=True, toolTip="Reload  (F5)")
        self.reload_btn.clicked.connect(self._render)
        self.scripts = QCheckBox("Scripts")
        self.scripts.setToolTip("Allow JavaScript in the page (off by default)")
        self.scripts.toggled.connect(self._scripts_toggled)
        self.find = QLineEdit(placeholderText="Find in page (Enter = next)")
        self.find.setClearButtonEnabled(True)
        self.find.setMaximumWidth(220)
        self.find.returnPressed.connect(lambda: self._find(True))
        self.find.textChanged.connect(lambda _t: self._find(True, from_start=True))
        ext = QToolButton(text="\u2197", autoRaise=True, toolTip="Open in the system browser")
        ext.clicked.connect(lambda: QDesktopServices.openUrl(QUrl.fromLocalFile(self.path)))
        bar.addSpacing(8)
        for w in (self.reload_btn, self.scripts, self.find):
            bar.addWidget(w)
        bar.addStretch(1)
        bar.addWidget(ext)
        self.barw = QWidget()
        self.barw.setLayout(bar)

        self.split = QSplitter(Qt.Horizontal)
        self.split.setChildrenCollapsible(False)
        self.split.addWidget(editor)
        lay = QVBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(0)
        lay.addWidget(self.barw)
        lay.addWidget(self.split, 1)
        self.set_mode("source")

    # ---- TextTab-like interface used by FilePane
    def is_modified(self):
        return self.editor.is_modified()

    def save(self):
        self.editor.save()

    # ---- web view
    def _ensure_web(self):
        if self.web is not None:
            return
        self.web = PreviewView()
        pg = self.web.page()
        pg.setLinkDelegationPolicy(QWebPage.DelegateAllLinks)
        self.web.linkClicked.connect(self._link)
        self.web.loadFinished.connect(self._restore_scroll)
        self.web.setContextMenuPolicy(Qt.CustomContextMenu)
        self.web.customContextMenuRequested.connect(self._web_menu)
        st = self.web.settings()
        st.setAttribute(QWebSettings.PluginsEnabled, False)
        st.setAttribute(QWebSettings.JavaEnabled, False)
        st.setAttribute(QWebSettings.LocalContentCanAccessRemoteUrls, True)
        st.setAttribute(QWebSettings.JavascriptEnabled, self.scripts.isChecked())
        self.split.addWidget(self.web)

    def set_mode(self, mode):
        self.mode = mode
        for k, b in self.buttons.items():
            b.setChecked(k == mode)
        if mode != "source":
            self._ensure_web()
        self.editor.setVisible(mode != "browser")
        if self.web is not None:
            self.web.setVisible(mode != "source")
        self.find.setVisible(mode != "source")
        self.reload_btn.setVisible(mode != "source")
        self.scripts.setVisible(mode != "source")
        if mode == "split":   # side by side when wide, stacked when the pane is narrow
            self.split.setOrientation(Qt.Horizontal if self.width() >= 900 else Qt.Vertical)
            QTimer.singleShot(0, self._halve)
        if mode != "source":
            self._render()
        self.setFocusProxy(self.web if mode == "browser" else self.editor)
        self.modeChanged.emit(mode)

    def _halve(self):
        total = self.split.width() if self.split.orientation() == Qt.Horizontal else self.split.height()
        self.split.setSizes([total // 2, total - total // 2])

    def cycle_mode(self):
        order = ("source", "split", "browser")
        self.set_mode(order[(order.index(self.mode) + 1) % 3])

    def _text_changed(self):
        if self.mode != "source":
            self.timer.start()

    def _render(self):
        if self.web is None or self.mode == "source":
            return
        self._scroll = self.web.page().mainFrame().scrollPosition()
        self.web.setHtml(self.editor.toPlainText(), QUrl.fromLocalFile(self.path))

    def _restore_scroll(self, _ok):
        if self._scroll is not None:
            self.web.page().mainFrame().setScrollPosition(self._scroll)
            self._scroll = None

    def _scripts_toggled(self, on):
        if self.web is not None:
            self.web.settings().setAttribute(QWebSettings.JavascriptEnabled, on)
            self._render()

    def _find(self, forward, from_start=False):
        if self.web is None:
            return
        flags = QWebPage.FindWrapsAroundDocument
        if not forward:
            flags |= QWebPage.FindBackward
        if from_start:  # clear the previous highlight, then search again
            self.web.findText("")
        self.web.findText(self.find.text(), flags)

    def focus_find(self):
        self.find.setFocus()
        self.find.selectAll()

    def _link(self, url):
        if url.isLocalFile():
            target = os.path.abspath(url.toLocalFile())
            if target == self.path:
                if url.hasFragment():
                    self.web.page().mainFrame().scrollToAnchor(url.fragment())
                return
            if os.path.exists(target):
                self.openRequested.emit(target)
                return
        QDesktopServices.openUrl(url)

    def _web_menu(self, pos):
        m = QMenu(self)
        pg = self.web.page()
        for act, text in ((QWebPage.Copy, "Copy"), (QWebPage.SelectAll, "Select all")):
            a = pg.action(act)
            a.setText(text)
            m.addAction(a)
        m.addSeparator()
        m.addAction("Reload", self._render)
        m.addAction("Actual size", lambda: self.web.setZoomFactor(1.0))
        m.addAction("View source", lambda: self.set_mode("source"))
        m.addAction("Open in system browser",
                    lambda: QDesktopServices.openUrl(QUrl.fromLocalFile(self.path)))
        m.exec_(self.web.mapToGlobal(pos))

    def keyPressEvent(self, e):
        if e.key() == Qt.Key_F5:
            self._render()
        else:
            super().keyPressEvent(e)


def is_image_path(path):
    ext = Path(path).suffix.lstrip(".").lower()
    return bool(ext) and (ext.encode() in QImageReader.supportedImageFormats() or ext in PIL_EXTS)


class ImageTab(QScrollArea):
    """Image viewer: fit-to-window by default, zoom (Ctrl+wheel, + / - / 0 / 1), drag to pan,
    animated GIFs, crisp SVG, EXIF rotation, and more formats through Pillow."""
    ZMIN, ZMAX = 0.05, 32.0
    MAX_SIDE = 12000

    def __init__(self, path):
        super().__init__()
        self.path = path
        self.fit, self.zoom = True, 1.0
        self.src = None        # QImage (raster formats)
        self.svg = None        # QSvgRenderer (vector)
        self.movie = None      # QMovie (animated GIF)
        self.pix = None
        self.size0 = QSize()   # natural size
        self.error = ""
        self._drag = None
        self.setFocusPolicy(Qt.StrongFocus)
        self.setAlignment(Qt.AlignCenter)
        self.label = QLabel(alignment=Qt.AlignCenter)
        self.setWidget(self.label)
        self.setWidgetResizable(True)
        self.info = QLabel(self.viewport())
        self.info.setStyleSheet("background:rgba(0,0,0,150);color:white;padding:2px 8px;"
                                "border-radius:3px;font-size:11px")
        self.info.setAttribute(Qt.WA_TransparentForMouseEvents)
        self._load()
        self._apply()

    # ---- loading
    def _load(self):
        ext = Path(self.path).suffix.lstrip(".").lower()
        try:
            if ext in ("svg", "svgz") and QSvgRenderer is not None:
                r = QSvgRenderer(self.path)
                if r.isValid():
                    self.svg, self.size0 = r, r.defaultSize()
                    if self.size0.isEmpty():
                        self.size0 = QSize(512, 512)
                    return
            reader = QImageReader(self.path)
            reader.setAutoTransform(True)   # honour EXIF orientation
            if reader.supportsAnimation() and reader.imageCount() > 1:
                mv = QMovie(self.path)
                if mv.isValid():
                    mv.jumpToFrame(0)
                    self.movie, self.size0 = mv, mv.currentImage().size()
                    mv.setCacheMode(QMovie.CacheAll)
                    mv.start()
                    return
            img = reader.read()
            if img.isNull() and PILImage is not None:
                img = self._pil_image()
            if img.isNull():
                self.error = reader.errorString() or "unsupported or damaged image"
                return
            self.src, self.size0 = img, img.size()
            self.pix = QPixmap.fromImage(img)
        except Exception as e:  # damaged file, decompression bomb, ...
            self.error = str(e)

    def _pil_image(self):
        try:
            from PIL import ImageOps
            with PILImage.open(self.path) as im:
                im = ImageOps.exif_transpose(im).convert("RGBA")
                data = im.tobytes("raw", "RGBA")
                qi = QImage(data, im.width, im.height, im.width * 4, QImage.Format_RGBA8888)
                return qi.copy()   # detach from the python buffer
        except Exception:
            return QImage()

    # ---- display
    def _scale(self):
        if self.fit:
            vp = self.viewport().size()
            w, h = max(self.size0.width(), 1), max(self.size0.height(), 1)
            return min(1.0, max(vp.width() - 2, 16) / w, max(vp.height() - 2, 16) / h)
        return self.zoom

    def _apply(self):
        if self.error:
            self.label.setText(f"Cannot display this image\n\n{os.path.basename(self.path)}\n"
                               f"{self.error}\n\nRight-click to open it with the system app.")
            self.info.hide()
            return
        sc = self._scale()
        w = max(1, min(self.MAX_SIDE, round(self.size0.width() * sc)))
        h = max(1, min(self.MAX_SIDE, round(self.size0.height() * sc)))
        if self.svg is not None:
            img = QImage(w, h, QImage.Format_ARGB32_Premultiplied)
            img.fill(Qt.transparent)
            pt = QPainter(img)
            self.svg.render(pt)
            pt.end()
            self.label.setPixmap(QPixmap.fromImage(img))
        elif self.movie is not None:
            self.movie.setScaledSize(QSize(w, h))
            if self.label.movie() is not self.movie:
                self.label.setMovie(self.movie)
        else:
            mode = Qt.FastTransformation if sc >= 2 else Qt.SmoothTransformation
            if (w, h) == (self.size0.width(), self.size0.height()):
                self.label.setPixmap(self.pix)
            else:
                self.label.setPixmap(self.pix.scaled(w, h, Qt.IgnoreAspectRatio, mode))
        size = ""
        try:
            n = os.path.getsize(self.path)
            size = f"  \u00b7  {n} B" if n < 1024 else f"  \u00b7  {n / 1024:,.0f} KB"
        except OSError:
            pass
        self.info.setText(f"{self.size0.width()}\u00d7{self.size0.height()}{size}  \u00b7  "
                          f"{sc * 100:.0f}%" + ("  (fit)" if self.fit else ""))
        self.info.adjustSize()
        self._place_info()

    def _place_info(self):
        self.info.move(8, self.viewport().height() - self.info.height() - 8)
        self.info.raise_()

    def resizeEvent(self, e):
        super().resizeEvent(e)
        if not self.error:
            if self.fit:
                self._apply()
            else:
                self._place_info()

    def set_zoom(self, z=None, factor=None, fit=False):
        if self.error:
            return
        cur = self._scale()
        hb, vb = self.horizontalScrollBar(), self.verticalScrollBar()
        fx = (hb.value() + hb.pageStep() / 2) / max(hb.maximum() + hb.pageStep(), 1)
        fy = (vb.value() + vb.pageStep() / 2) / max(vb.maximum() + vb.pageStep(), 1)
        self.fit = fit
        if not fit:
            self.zoom = min(self.ZMAX, max(self.ZMIN, z if z is not None else cur * factor))
        self._apply()
        QApplication.processEvents()   # let the scroll ranges update, then keep the same centre
        hb.setValue(round(fx * (hb.maximum() + hb.pageStep()) - hb.pageStep() / 2))
        vb.setValue(round(fy * (vb.maximum() + vb.pageStep()) - vb.pageStep() / 2))

    # ---- interaction
    def wheelEvent(self, e):
        if e.modifiers() & Qt.ControlModifier:
            self.set_zoom(factor=1.25 if e.angleDelta().y() > 0 else 0.8)
            e.accept()
        else:
            super().wheelEvent(e)

    def keyPressEvent(self, e):
        k = e.key()
        if k in (Qt.Key_Plus, Qt.Key_Equal):
            self.set_zoom(factor=1.25)
        elif k == Qt.Key_Minus:
            self.set_zoom(factor=0.8)
        elif k == Qt.Key_0:
            self.set_zoom(fit=True)
        elif k == Qt.Key_1:
            self.set_zoom(1.0)
        else:
            super().keyPressEvent(e)

    def mousePressEvent(self, e):
        if e.button() == Qt.LeftButton:
            self._drag = e.pos()
            self.setCursor(Qt.ClosedHandCursor)
        super().mousePressEvent(e)

    def mouseMoveEvent(self, e):
        if self._drag is not None:
            d = e.pos() - self._drag
            self._drag = e.pos()
            self.horizontalScrollBar().setValue(self.horizontalScrollBar().value() - d.x())
            self.verticalScrollBar().setValue(self.verticalScrollBar().value() - d.y())
        super().mouseMoveEvent(e)

    def mouseReleaseEvent(self, e):
        self._drag = None
        self.unsetCursor()
        super().mouseReleaseEvent(e)

    def mouseDoubleClickEvent(self, e):   # toggle fit <-> 100%
        self.set_zoom(fit=True) if not self.fit else self.set_zoom(1.0)

    def _copy_image(self):
        if self.src is not None:
            QApplication.clipboard().setImage(self.src)
        elif self.movie is not None:
            QApplication.clipboard().setImage(self.movie.currentImage())
        elif self.svg is not None:
            img = QImage(self.size0, QImage.Format_ARGB32_Premultiplied)
            img.fill(Qt.transparent)
            pt = QPainter(img)
            self.svg.render(pt)
            pt.end()
            QApplication.clipboard().setImage(img)

    def contextMenuEvent(self, e):
        m = QMenu(self)
        m.addAction("Fit to window  (0)", lambda: self.set_zoom(fit=True))
        m.addAction("Actual size  (1)", lambda: self.set_zoom(1.0))
        m.addAction("Zoom in  (+)", lambda: self.set_zoom(factor=1.25))
        m.addAction("Zoom out  (-)", lambda: self.set_zoom(factor=0.8))
        m.addSeparator()
        if not self.error:
            m.addAction("Copy image", self._copy_image)
        m.addAction("Copy path", lambda: QApplication.clipboard().setText(self.path))
        m.addAction("Open with system app",
                    lambda: QDesktopServices.openUrl(QUrl.fromLocalFile(self.path)))
        m.exec_(e.globalPos())

    def is_modified(self):
        return False

    def save(self):
        pass


class RichNoteTab(QWidget):
    """A rich-text note stored as an HTML file (.noter, or a daily note).
    Saves itself automatically. A daily note that is left empty has no file."""
    autosave = True
    dirtyChanged = pyqtSignal(bool)
    saved = pyqtSignal()

    def __init__(self, path, daily=False):
        super().__init__()
        self.path = path
        self.daily = daily
        self._dirty = False
        self._loading = True
        lay = QVBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        self.panel = NotePanel()
        lay.addWidget(self.panel)
        ed = self.panel.editor
        ed.source_path = path
        ed.setPlaceholderText("Daily note - write here..." if daily else
                              "Write here... (saved automatically to " + os.path.basename(path) + ")")
        try:
            with open(path, "r", encoding="utf-8", errors="replace") as f:
                text = f.read()
        except FileNotFoundError:
            text = ""
        if text.strip() and Qt.mightBeRichText(text):
            ed.setHtml(text)
        elif text.strip():
            ed.setPlainText(text)
        else:
            fmt = QTextCharFormat()
            fmt.setFontPointSize(BASE_PT)
            ed.setCurrentCharFormat(fmt)
        ed.fix_contrast(join=False)
        ed.document().clearUndoRedoStacks()
        self._loading = False
        self.timer = QTimer(self, singleShot=True, interval=1200)
        self.timer.timeout.connect(self._autosave)
        ed.textChanged.connect(self._changed)
        self.setFocusProxy(ed)

    def _changed(self):
        # Qt also emits textChanged for non-edits (e.g. focus); trust isModified()
        if not self._loading and self.panel.editor.document().isModified():
            self._set_dirty(True)
            self.timer.start()

    def _set_dirty(self, on):
        if on != self._dirty:
            self._dirty = on
            self.dirtyChanged.emit(on)

    def is_modified(self):
        return self._dirty

    def refix_colors(self):
        was, self._loading = self._loading, True
        try:
            self.panel.editor.fix_contrast(join=False)
        finally:
            self._loading = was

    def goto_line(self, line):
        blk = self.panel.editor.document().findBlockByNumber(max(0, line - 1))
        self.panel.editor.setTextCursor(QTextCursor(blk))
        self.panel.editor.ensureCursorVisible()

    def plain_text(self):
        return self.panel.editor.toPlainText()

    def save(self):
        self.timer.stop()
        self._loading = True  # contrast repair must not mark the note dirty again
        try:
            self.panel.editor.fix_contrast()
        finally:
            self._loading = False
        ed = self.panel.editor
        html = ed.toHtml()
        if self.daily and not ed.toPlainText().strip() and "<table" not in html:
            try:
                os.unlink(self.path)
            except FileNotFoundError:
                pass
        else:
            tmp = self.path + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                f.write(html)
            os.replace(tmp, self.path)
        ed.document().setModified(False)
        self._set_dirty(False)
        self.saved.emit()

    def _autosave(self):
        try:
            self.save()
        except OSError as e:
            QMessageBox.warning(self, "Save", f"Could not save {self.path}:\n{e}")


class FilePane(QWidget):
    """Tabbed pane. Used twice: notes (.noter / daily) on the left, any file on the right."""
    MAX_TEXT = 10 * 1024 * 1024
    noteSaved = pyqtSignal()

    def __init__(self, hint, notes_dir):
        super().__init__()
        self.notes_dir = os.path.abspath(str(notes_dir))
        self.stack = QStackedLayout(self)
        if isinstance(hint, str):
            label = QLabel(hint)
            label.setAlignment(Qt.AlignCenter)
            label.setStyleSheet("color: gray; font-size: 14px;")
            hint = label
        self.tabs = QTabWidget()
        self.tabs.setTabsClosable(True)
        self.tabs.setMovable(True)
        self.tabs.setDocumentMode(True)
        self.tabs.tabCloseRequested.connect(self.close_tab)
        self.findbar = FindBar()
        page = QWidget()
        pl = QVBoxLayout(page)
        pl.setContentsMargins(0, 0, 0, 0)
        pl.setSpacing(0)
        pl.addWidget(self.tabs, 1)
        pl.addWidget(self.findbar)
        self.tabs.currentChanged.connect(self._tab_changed)
        self.stack.addWidget(hint)
        self.stack.addWidget(page)

    def _refresh_stack(self):
        self.stack.setCurrentIndex(1 if self.tabs.count() else 0)

    def is_daily(self, path):
        return path.lower().endswith(".html") and os.path.dirname(path) == self.notes_dir

    def _index_of(self, path):
        for i in range(self.tabs.count()):
            if self.tabs.widget(i).path == path:
                return i
        return -1

    def has(self, path):
        return self._index_of(os.path.abspath(path)) >= 0

    def select(self, path):
        i = self._index_of(os.path.abspath(path))
        if i >= 0:
            self.tabs.setCurrentIndex(i)
        return i >= 0

    def close_path(self, path):
        i = self._index_of(os.path.abspath(path))
        return i < 0 or self.close_tab(i)

    def open_paths(self):
        return [self.tabs.widget(i).path for i in range(self.tabs.count())]

    def flush(self):
        """Write every note tab that has pending changes."""
        for i in range(self.tabs.count()):
            w = self.tabs.widget(i)
            if getattr(w, "autosave", False) and w.is_modified():
                try:
                    w.save()
                except OSError as e:
                    QMessageBox.warning(self, "Save", str(e))

    @staticmethod
    def _editor(w):
        """The text editor inside a tab (the tab itself, or the source view of an HTML tab)."""
        if isinstance(w, HtmlTab):
            return w.editor
        return w if isinstance(w, TextTab) else None

    def searchable(self):
        """(path, text) of every open text-like tab, including unsaved edits."""
        out = []
        for i in range(self.tabs.count()):
            w = self.tabs.widget(i)
            ed = self._editor(w)
            if ed is not None:
                out.append((w.path, ed.toPlainText()))
            elif isinstance(w, RichNoteTab):
                out.append((w.path, w.plain_text()))
        return out

    def active_findbar(self):
        w = self.current()
        return w.panel.findbar if isinstance(w, RichNoteTab) else self.findbar

    def _tab_changed(self, i):
        w = self.tabs.widget(i) if i >= 0 else None
        ed = self._editor(w)
        if ed is not None and not (isinstance(w, HtmlTab) and w.mode == "browser"):
            self.findbar.set_target(ed)
        else:
            self.findbar.set_target(None)
            self.findbar.hide()

    def text_tabs(self):
        return [self._editor(self.tabs.widget(i)) for i in range(self.tabs.count())
                if self._editor(self.tabs.widget(i)) is not None]

    def show_find(self, text=None):
        w = self.current()
        if isinstance(w, RichNoteTab):
            w.panel.show_find(text)
            return True
        if isinstance(w, HtmlTab) and w.mode == "browser":
            w.focus_find()
            return True
        w = self._editor(w)
        if w is None:
            return False
        if text is None:
            sel = w.textCursor().selectedText()
            if sel and "\u2029" not in sel and len(sel) <= 100:
                text = sel
        self.findbar.open(text)
        return True

    def reveal(self, path, line, query):
        """Open a file, jump to a line and highlight the query."""
        self.open_file(path)
        w = self.current()
        if isinstance(w, RichNoteTab) and w.path == os.path.abspath(path):
            w.panel.findbar.open(query, from_start=True)
            w.panel.editor.setFocus()
        elif self._editor(w) is not None and w.path == os.path.abspath(path):
            if isinstance(w, HtmlTab) and w.mode == "browser":
                w.set_mode("source")
            ed = self._editor(w)
            ed.goto_line(line)
            self.findbar.open(query)
            ed.setFocus()

    def open_file(self, path):
        path = os.path.abspath(path)
        if self.select(path):
            return
        ext = Path(path).suffix.lstrip(".").lower().encode()
        if path.lower().endswith(NOTER_EXT) or self.is_daily(path):
            try:
                w = RichNoteTab(path, daily=self.is_daily(path))
            except OSError as e:
                QMessageBox.warning(self, "Open", str(e))
                return
        elif is_image_path(path):
            w = ImageTab(path)
        else:
            w = self._text_tab(path)
            if w is None:
                return
            if HAVE_WEBKIT and path.lower().endswith(HTML_EXTS):
                w = HtmlTab(w)
        self.tabs.addTab(w, self._title(w))
        i = self.tabs.indexOf(w)
        self.tabs.setTabToolTip(i, path)
        self.tabs.setCurrentIndex(i)
        if self._editor(w) is not None:
            self._editor(w).document().modificationChanged.connect(lambda _m, w=w: self._retitle(w))
            if isinstance(w, HtmlTab):
                w.modeChanged.connect(lambda _m: self._tab_changed(self.tabs.currentIndex()))
                w.openRequested.connect(self._open_link)
        elif isinstance(w, RichNoteTab):
            w.dirtyChanged.connect(lambda _d, w=w: self._retitle(w))
            w.saved.connect(self.noteSaved)
        self._refresh_stack()

    def _open_link(self, path):
        """A local link clicked in an HTML page: open it here (HTML pages in browser mode)."""
        self.open_file(path)
        w = self.current()
        if isinstance(w, HtmlTab) and w.path == os.path.abspath(path):
            w.set_mode("browser")

    def _text_tab(self, path):
        try:
            size = os.path.getsize(path)
            with open(path, "rb") as f:
                data = f.read(self.MAX_TEXT + 1)
        except OSError as e:
            QMessageBox.warning(self, "Open", str(e))
            return None
        if size > self.MAX_TEXT or b"\0" in data[:8192]:
            self._external(path, "Binary or very large file - open with the system app?")
            return None
        try:
            return TextTab(path, data.decode("utf-8"), "utf-8")
        except UnicodeDecodeError:
            return TextTab(path, data.decode("latin-1"), "latin-1")

    def _external(self, path, msg):
        if QMessageBox.question(self, "Open", msg) == QMessageBox.Yes:
            QDesktopServices.openUrl(QUrl.fromLocalFile(path))

    @staticmethod
    def _title(w):
        name = os.path.basename(w.path)
        if isinstance(w, RichNoteTab):
            if w.daily:  # sun: daily note
                d = QDate.fromString(os.path.splitext(name)[0], Qt.ISODate)
                return "\u2600 " + (d.toString("ddd d MMM yyyy") if d.isValid() else name)
            name = "\u270E " + name[: -len(NOTER_EXT)]  # pencil: note
        return name

    def _retitle(self, w):
        i = self.tabs.indexOf(w)
        if i >= 0:
            self.tabs.setTabText(i, ("\u25CF " if w.is_modified() else "") + self._title(w))

    def current(self):
        return self.tabs.currentWidget()

    def save_current(self):
        w = self.current()
        if w is not None and w.is_modified():
            try:
                w.save()
            except OSError as e:
                QMessageBox.warning(self, "Save", str(e))

    def close_tab(self, i):
        w = self.tabs.widget(i)
        if getattr(w, "autosave", False) and w.is_modified():
            try:
                w.save()  # standalone notes never ask - they just save
            except OSError as e:
                QMessageBox.warning(self, "Save", str(e))
                return False
        if w.is_modified():
            r = QMessageBox.question(
                self, "Unsaved changes", f"Save {os.path.basename(w.path)}?",
                QMessageBox.Save | QMessageBox.Discard | QMessageBox.Cancel)
            if r == QMessageBox.Cancel:
                return False
            if r == QMessageBox.Save:
                try:
                    w.save()
                except OSError as e:
                    QMessageBox.warning(self, "Save", str(e))
                    return False
        self.tabs.removeTab(i)
        w.deleteLater()
        self._refresh_stack()
        return True

    def close_all(self):
        while self.tabs.count():
            if not self.close_tab(self.tabs.count() - 1):
                return False
        return True


# --------------------------------------------------------------------------
# search: all notes / open files / files under the explorer folder
# --------------------------------------------------------------------------
class FolderSearch(QThread):
    """Greps text files under a folder without blocking the UI."""
    hit = pyqtSignal(int, str, int, str)     # token, path, line number, line text
    done = pyqtSignal(int, int, int, bool)   # token, matches, files, truncated
    SKIP_DIRS = {"node_modules", "__pycache__", "venv", "snap", "site-packages"}
    MAX_SIZE = 2 * 1024 * 1024
    MAX_HITS = 1000
    PER_FILE = 25

    def __init__(self, token, root, query, case):
        super().__init__()
        self.token, self.root, self.query, self.case = token, root, query, case

    def run(self):
        needle = self.query if self.case else self.query.lower()
        hits = files = 0
        for dirpath, dirs, names in os.walk(self.root):
            dirs[:] = sorted(d for d in dirs
                             if not d.startswith(".") and d not in self.SKIP_DIRS)
            for name in sorted(names):
                if self.isInterruptionRequested():
                    return
                if name.startswith("."):
                    continue
                path = os.path.join(dirpath, name)
                try:
                    if os.path.islink(path) or os.path.getsize(path) > self.MAX_SIZE:
                        continue
                    with open(path, "rb") as f:
                        data = f.read()
                except OSError:
                    continue
                if b"\0" in data[:4096]:
                    continue
                n = 0
                text = data.decode("utf-8", "replace")
                if name.lower().endswith(NOTER_EXT) and "<" in text:
                    text = html_to_text(text)
                for no, line in enumerate(text.splitlines(), 1):
                    if needle in (line if self.case else line.lower()):
                        self.hit.emit(self.token, path, no, line.strip()[:200])
                        n += 1
                        hits += 1
                        if hits >= self.MAX_HITS:
                            self.done.emit(self.token, hits, files + 1, True)
                            return
                        if n >= self.PER_FILE:
                            break
                files += bool(n)
        self.done.emit(self.token, hits, files, False)


class SearchPanel(QWidget):
    openNote = pyqtSignal(str, str)         # ISO date, query
    openFile = pyqtSignal(str, int, str)    # path, line, query
    SCOPES = ["Daily notes", "Open tabs", "Explorer folder"]

    def __init__(self, store, get_root, get_open_files, flush):
        super().__init__()
        self.store, self.get_root = store, get_root
        self.get_open_files, self.flush = get_open_files, flush
        self.cache = {}
        self.token = 0
        self.workers = set()

        lay = QVBoxLayout(self)
        lay.setContentsMargins(4, 2, 4, 4)
        lay.setSpacing(3)
        row = QHBoxLayout()
        self.scope = QComboBox()
        self.scope.addItems(self.SCOPES)
        self.scope.setToolTip("Where to search")
        self.input = QLineEdit()
        self.input.setPlaceholderText("Search...")
        self.input.setClearButtonEnabled(True)
        self.case = QToolButton(text="Aa")
        self.case.setCheckable(True)
        self.case.setToolTip("Match case")
        row.addWidget(self.scope)
        row.addWidget(self.input, 1)
        row.addWidget(self.case)
        lay.addLayout(row)
        self.results = QListWidget()
        self.results.setUniformItemSizes(True)
        lay.addWidget(self.results, 1)
        self.status = QLabel()
        self.status.setStyleSheet("color: gray")
        lay.addWidget(self.status)

        self.timer = QTimer(self, singleShot=True, interval=300)
        self.timer.timeout.connect(self.run)
        self.input.textChanged.connect(lambda _: self.timer.start())
        self.input.returnPressed.connect(self.run)
        self.scope.currentIndexChanged.connect(lambda _: self.run())
        self.case.toggled.connect(lambda _: self.run())
        self.results.itemClicked.connect(self._open)
        self.results.itemActivated.connect(self._open)

    def focus(self, scope=None, text=None):
        if scope is not None:
            self.scope.setCurrentIndex(scope)
        if text:
            self.input.setText(text)
        self.input.setFocus()
        self.input.selectAll()

    # ---- running a search
    def run(self):
        self.timer.stop()
        self._cancel()
        self.results.clear()
        q = self.input.text()
        if not q.strip():
            self.status.setText("")
            return
        scope = self.scope.currentIndex()
        if scope == 0:
            self._notes(q)
        elif scope == 1:
            self._open_files(q)
        else:
            self._folder(q)

    def _cancel(self):
        self.token += 1
        for w in self.workers:
            w.requestInterruption()

    def shutdown(self):
        self._cancel()
        for w in list(self.workers):
            w.wait(2000)

    def _needle(self, q):
        return q if self.case.isChecked() else q.lower()

    def _hay(self, text):
        return text if self.case.isChecked() else text.lower()

    def _notes(self, q):
        self.flush()  # make sure today's unsaved text is searchable
        needle, found, total = self._needle(q.strip()), 0, 0
        for path in sorted(self.store.notes_dir.glob("*.html"), reverse=True):
            total += 1
            try:
                mtime = path.stat().st_mtime_ns
                ent = self.cache.get(path)
                if not ent or ent[0] != mtime:
                    doc = QTextDocument()
                    doc.setHtml(path.read_text(encoding="utf-8"))
                    ent = self.cache[path] = (mtime, doc.toPlainText())
            except OSError:
                continue
            text = ent[1]
            hay = self._hay(text)
            i = hay.find(needle)
            if i < 0:
                continue
            found += 1
            snippet = " ".join(text[max(0, i - 25): i + len(needle) + 55].split())
            d = QDate.fromString(path.stem, Qt.ISODate)
            label = d.toString("ddd d MMM yyyy") if d.isValid() else path.stem
            n = hay.count(needle)
            it = QListWidgetItem(f"{label}  \u00B7  {snippet}" + (f"   (\u00D7{n})" if n > 1 else ""))
            it.setData(Qt.UserRole, ("note", path.stem, q.strip()))
            it.setToolTip(text[:400])
            self.results.addItem(it)
        self.status.setText(f"{found} of {total} notes match")

    def _open_files(self, q):
        needle, hits, files = self._needle(q), 0, 0
        for path, text in self.get_open_files():
            n = 0
            for no, line in enumerate(text.splitlines(), 1):
                if needle in self._hay(line):
                    self._add_file_hit(path, no, line.strip()[:200], os.path.basename(path), q)
                    n += 1
                    hits += 1
                    if n >= 200 or hits >= 1000:
                        break
            files += bool(n)
        self.status.setText(f"{hits} matches in {files} open tabs")

    def _folder(self, q):
        if len(q.strip()) < 2:
            self.status.setText("Type at least 2 characters")
            return
        root = self.get_root()
        self.status.setText(f"Searching {root} ...")
        w = FolderSearch(self.token, root, q.strip(), self.case.isChecked())
        w.hit.connect(self._folder_hit)
        w.done.connect(self._folder_done)
        w.finished.connect(lambda w=w: self._reap(w))
        self.workers.add(w)
        w.start()

    def _reap(self, w):
        self.workers.discard(w)
        w.deleteLater()

    def _folder_hit(self, token, path, line, text):
        if token != self.token:
            return
        rel = os.path.relpath(path, self.get_root())
        self._add_file_hit(path, line, text, rel, self.input.text().strip())

    def _folder_done(self, token, hits, files, truncated):
        if token == self.token:
            self.status.setText(f"{hits} matches in {files} files"
                                + (" (limit reached, refine the query)" if truncated else ""))

    def _add_file_hit(self, path, line, text, label, query):
        it = QListWidgetItem(f"{label}:{line}   {text}")
        it.setData(Qt.UserRole, ("file", path, line, query))
        it.setToolTip(f"{path}:{line}")
        self.results.addItem(it)

    def _open(self, item):
        d = item.data(Qt.UserRole)
        if d[0] == "note":
            self.openNote.emit(d[1], d[2])
        else:
            self.openFile.emit(d[1], d[2], d[3])


# --------------------------------------------------------------------------
# main window
# --------------------------------------------------------------------------
class MainWindow(QMainWindow):
    def __init__(self, files):
        super().__init__()
        self.setWindowTitle(APP_NAME)
        self.setWindowIcon(make_app_icon())
        self.store = Store()
        self.settings = QSettings("noter", "noter")
        self.reminders = self.store.load_reminders()
        self._rem_mtime = self.store.rem_mtime()

        # panels
        self.explorer = ExplorerPanel(self.settings.value("root", str(Path.home())))
        self.calendar = MarkedCalendar()
        self.reminder_list = QListWidget()
        self.reminder_list.setContextMenuPolicy(Qt.CustomContextMenu)
        self.notes = FilePane(
            "No notes open\n\n"
            "Ctrl+N  create a note (.noter file)\n"
            "Ctrl+T  open today's daily note\n"
            "or double-click a .noter file in the explorer",
            self.store.notes_dir)
        self.files = FilePane(
            "Double-click any file in the explorer\nto open it here.",
            self.store.notes_dir)
        self.notes.setMinimumWidth(240)

        cal_box = QWidget()
        cl = QVBoxLayout(cal_box)
        cl.setContentsMargins(4, 0, 4, 0)
        cl.addWidget(self.calendar)
        daily_btn = QPushButton("Open daily note for selected day")
        daily_btn.setToolTip("Daily notes are optional: double-click a day, or press Ctrl+T for today")
        daily_btn.clicked.connect(lambda: self.open_daily())
        cl.addWidget(daily_btn)

        rem_box = QWidget()
        rl = QVBoxLayout(rem_box)
        rl.setContentsMargins(4, 0, 4, 4)
        rh = QHBoxLayout()
        rh.addWidget(QLabel("<b>Upcoming</b>"), 1)
        add = QToolButton(text="+")
        add.setToolTip("New reminder (Ctrl+Shift+R)")
        add.clicked.connect(self.add_reminder)
        rh.addWidget(add)
        rl.addLayout(rh)
        rl.addWidget(self.reminder_list)

        self.search = SearchPanel(
            self.store, lambda: self.explorer.root,
            lambda: self.notes.searchable() + self.files.searchable(),
            self.notes.flush)
        self.left_tabs = QTabWidget()
        self.left_tabs.setDocumentMode(True)
        self.left_tabs.addTab(rem_box, "Reminders")
        self.left_tabs.addTab(self.search, "Search")

        left = QSplitter(Qt.Vertical)
        left.addWidget(self.explorer)
        left.addWidget(cal_box)
        left.addWidget(self.left_tabs)
        left.setSizes([330, 230, 240])
        left.setChildrenCollapsible(False)
        self.left = left

        self.main_split = QSplitter(Qt.Horizontal)
        self.main_split.addWidget(left)
        self.main_split.addWidget(self.notes)
        self.main_split.addWidget(self.files)
        self.main_split.setSizes([310, 560, 640])
        self.main_split.setStretchFactor(0, 0)
        self.main_split.setStretchFactor(1, 1)
        self.main_split.setStretchFactor(2, 1)
        central = QWidget()
        cl = QVBoxLayout(central)
        cl.setContentsMargins(0, 0, 0, 0)
        cl.setSpacing(0)
        self.titlebar = TitleBar()
        cl.addWidget(self.titlebar)
        cl.addWidget(self.main_split, 1)
        self.setCentralWidget(central)

        self._build_menu()   # also applies the saved theme
        self.titlebar._paint()
        self.tray = QSystemTrayIcon(make_app_icon(), self)
        self.statusBar().showMessage(f"Daily notes folder: {self.store.notes_dir}")

        # wiring
        self.explorer.fileActivated.connect(self.open_path)
        self.explorer.openSide.connect(lambda p: self.open_path(p, side=True))
        self.explorer.reminderRequested.connect(
            lambda p: self.add_reminder(os.path.splitext(os.path.basename(p))[0]))
        self.search.openNote.connect(self.goto_note)
        self.search.openFile.connect(self.reveal_path)
        self.notes.noteSaved.connect(self._refresh_note_marks)
        self.files.noteSaved.connect(self._refresh_note_marks)
        self.calendar.activated.connect(self.open_daily)
        self._last_pane = self.notes
        QApplication.instance().focusChanged.connect(self._focus_changed)
        self.reminder_list.itemDoubleClicked.connect(self.edit_reminder)
        self.reminder_list.customContextMenuRequested.connect(self._reminder_menu)

        self.rem_timer = QTimer(self, interval=10_000)
        self.rem_timer.timeout.connect(self.check_reminders)
        self.rem_timer.start()

        self.calendar.note_dates = self.store.note_dates()
        self.refresh_reminders()
        self.calendar.setSelectedDate(QDate.currentDate())
        self._restore_session()
        for f in files:
            self.open_path(f)

        geo = self.settings.value("geometry")
        if geo:
            self.restoreGeometry(geo)
        else:
            self.resize(1500, 860)
        st = self.settings.value("split")
        if st:
            self.main_split.restoreState(st)
        lst = self.settings.value("left_split")
        if lst:
            self.left.restoreState(lst)
        QTimer.singleShot(1000, self.check_reminders)
        QTimer.singleShot(2500, self._offer_background)
        self._focus_pane(self.notes)

    # ---- menu & shortcuts
    def _build_menu(self):
        mb = self.menuBar()
        m = mb.addMenu("&File")
        m.addAction("&Save", self.save_all, QKeySequence.Save)
        m.addAction("&New note (.noter file)...", self.explorer.new_noter, QKeySequence("Ctrl+N"))
        m.addAction("&Open file...", self._open_dialog, QKeySequence("Ctrl+O"))
        m.addAction("&Close tab", self.close_current_tab, QKeySequence("Ctrl+W"))
        m.addSeparator()
        m.addAction("Cursor &Agent settings...", self.agent_settings_dialog)
        m.addAction("Install app &launcher (aNoter icon in menu / dock)...", self.install_launcher)
        m.addAction("&Quit", self.close, QKeySequence.Quit)

        m = mb.addMenu("&Notes")
        m.addAction("Open &today's daily note", self.go_today, QKeySequence("Ctrl+T"))
        m.addAction("Open daily note of the selected day", lambda: self.open_daily(),
                    QKeySequence("Ctrl+D"))
        m.addAction("Previous day's note", lambda: self.step_daily(-1), QKeySequence("Alt+Left"))
        m.addAction("Next day's note", lambda: self.step_daily(1), QKeySequence("Alt+Right"))
        m.addSeparator()
        m.addAction("New &reminder...", self.add_reminder, QKeySequence("Ctrl+Shift+R"))
        m.addSeparator()
        self.act_sound = QAction("Reminder sound", self, checkable=True)
        self.act_sound.setChecked(self.store.config().get("sound", True))
        self.act_sound.toggled.connect(self.set_sound)
        m.addAction(self.act_sound)
        m.addAction("Choose reminder sound...", self.choose_sound)
        m.addAction("Use default sound", self.reset_sound)
        m.addAction("Play test sound", lambda: play_sound(self.store))
        self.act_background = QAction("Background reminders (work when aNoter is closed)",
                                      self, checkable=True)
        self.act_background.setChecked(autostart_enabled())
        self.act_background.toggled.connect(self.set_background)
        m.addAction(self.act_background)
        m.addAction("Open daily notes folder", lambda: QDesktopServices.openUrl(
            QUrl.fromLocalFile(str(self.store.notes_dir))))

        m = mb.addMenu("&Search")
        m.addAction("&Find in this tab...", self.find_here, QKeySequence.Find)
        m.addAction("Find next", lambda: self._step_find(True), QKeySequence("F3"))
        m.addAction("Find previous", lambda: self._step_find(False), QKeySequence("Shift+F3"))
        m.addSeparator()
        m.addAction("Search in &explorer folder...", lambda: self.focus_search(2), QKeySequence("Ctrl+Shift+F"))
        m.addAction("Search open &tabs...", lambda: self.focus_search(1), QKeySequence("Ctrl+Alt+O"))
        m.addAction("Search &daily notes...", lambda: self.focus_search(0), QKeySequence("Ctrl+Alt+D"))

        m = mb.addMenu("&View")
        dark = QAction("Dark theme", self, checkable=True)
        dark.setChecked(self.settings.value("dark", False, type=bool))
        dark.toggled.connect(self.set_dark)
        m.addAction(dark)
        apply_theme(QApplication.instance(), dark.isChecked())
        m.addSeparator()
        for text, key, fn in (("Focus explorer", "Ctrl+1", lambda: self.explorer.tree.setFocus()),
                              ("Focus notes (left)", "Ctrl+2", lambda: self._focus_pane(self.notes)),
                              ("Focus files (right)", "Ctrl+3", lambda: self._focus_pane(self.files))):
            m.addAction(text, fn, QKeySequence(key))
        m.addSeparator()
        m.addAction("HTML: switch Source / Split / Browser", self.cycle_html_mode, QKeySequence("F6"))
        m.addSeparator()
        m.addAction("Show/hide right pane", lambda: self.files.setVisible(not self.files.isVisible()),
                    QKeySequence("F4"))
        m.addAction("Show/hide explorer column", lambda: self.left.setVisible(not self.left.isVisible()),
                    QKeySequence("F9"))

    def set_dark(self, on):
        self.settings.setValue("dark", on)
        apply_theme(QApplication.instance(), on)
        self.titlebar._paint()
        self._fix_note_colors()

    def _fix_note_colors(self):
        """Make text/cell colors in the open notes readable on the current theme."""
        for pane in (self.notes, self.files):
            for i in range(pane.tabs.count()):
                w = pane.tabs.widget(i)
                if isinstance(w, RichNoteTab):
                    w.refix_colors()

    # ---- panes
    def _pane_of(self, widget):
        if widget is not None:
            if self.notes.isAncestorOf(widget):
                return self.notes
            if self.files.isAncestorOf(widget):
                return self.files
        return None

    def _focus_changed(self, _old, new):
        pane = self._pane_of(new)
        if pane is not None:
            self._last_pane = pane

    def _active_pane(self):
        return self._pane_of(QApplication.focusWidget()) or self._last_pane

    def _focus_pane(self, pane):
        self._last_pane = pane
        w = pane.current()
        if w is not None:
            w.setFocus()

    def pane_for(self, path):
        if path.lower().endswith(NOTER_EXT) or self.notes.is_daily(path):
            return self.notes
        return self.files

    def open_path(self, path, side=False):
        """Notes (.noter, daily) open on the left; everything else on the right."""
        path = os.path.abspath(path)
        target = self.files if side else self.pane_for(path)
        other = self.files if target is self.notes else self.notes
        if other.has(path) and not other.close_path(path):  # move between panes
            return
        target.open_file(path)
        self._last_pane = target

    def reveal_path(self, path, line, query):
        pane = self.pane_for(os.path.abspath(path))
        pane.reveal(path, line, query)
        self._last_pane = pane

    def close_current_tab(self):
        pane = self._active_pane()
        if pane.tabs.count():
            pane.close_tab(pane.tabs.currentIndex())

    # ---- find / search
    def cycle_html_mode(self):
        w = self._active_pane().current()
        if isinstance(w, HtmlTab):
            w.cycle_mode()
        else:
            self.statusBar().showMessage("Current tab is not an HTML file", 3000)

    def _selected_text(self):
        fw = QApplication.focusWidget()
        if isinstance(fw, (QTextEdit, QPlainTextEdit)):
            sel = fw.textCursor().selectedText()
            if sel and "\u2029" not in sel and len(sel) <= 100:
                return sel
        return None

    def find_here(self):
        pane = self._active_pane()
        if not pane.show_find():
            self.statusBar().showMessage("Nothing to search in this tab", 3000)

    def _step_find(self, forward):
        pane = self._active_pane()
        bar = pane.active_findbar()
        if bar.input.text() and bar.edit is not None:
            bar.step(forward)
        else:
            pane.show_find()

    def focus_search(self, scope):
        text = self._selected_text()
        self.left.show()
        self.left_tabs.setCurrentWidget(self.search)
        self.search.focus(scope, text)

    def goto_note(self, iso_date, query):
        d = QDate.fromString(iso_date, Qt.ISODate)
        if not d.isValid():
            return
        self.calendar.setSelectedDate(d)
        self.open_daily(d)
        w = self.notes.current()
        if isinstance(w, RichNoteTab):
            w.panel.findbar.open(query, from_start=True)
            w.panel.editor.setFocus()

    def _open_dialog(self):
        from PyQt5.QtWidgets import QFileDialog
        paths, _ = QFileDialog.getOpenFileNames(self, "Open file", self.explorer.root)
        for p in paths:
            self.open_path(p)

    # ---- daily notes (optional)
    def open_daily(self, qdate=None):
        if not isinstance(qdate, QDate) or not qdate.isValid():
            qdate = self.calendar.selectedDate()
        self.open_path(str(self.store.note_path(qdate)))
        self._focus_pane(self.notes)

    def go_today(self):
        today = QDate.currentDate()
        self.calendar.setSelectedDate(today)
        self.calendar.showSelectedDate()
        self.open_daily(today)

    def step_daily(self, n):
        d = self.calendar.selectedDate().addDays(n)
        self.calendar.setSelectedDate(d)
        self.open_daily(d)

    def _refresh_note_marks(self):
        self.calendar.note_dates = self.store.note_dates()
        self.calendar.updateCells()

    def save_all(self):
        self.notes.flush()
        self.files.flush()
        self._active_pane().save_current()

    # ---- session: reopen the notes that were open last time
    def _restore_session(self):
        paths = self.settings.value("notes_open", [])
        if isinstance(paths, str):
            paths = [paths]
        for path in paths or []:
            if os.path.isfile(path):
                self.notes.open_file(path)
        cur = self.settings.value("notes_current", "")
        if cur:
            self.notes.select(cur)

    def _save_session(self):
        cur = self.notes.current()
        self.settings.setValue("notes_open", self.notes.open_paths())
        self.settings.setValue("notes_current", cur.path if cur is not None else "")

    # ---- reminders
    def refresh_reminders(self):
        self.reminders.sort(key=lambda r: r["when"])
        self.reminder_list.clear()
        dates = set()
        for r in self.reminders:
            when = datetime.fromisoformat(r["when"])
            dates.add(when.date().isoformat())
            rep = " \u21BB" if r.get("repeat", "none") != "none" else ""
            it = QListWidgetItem(f"{when:%a %d %b %H:%M}{rep}  {r['text']}")
            it.setData(Qt.UserRole, r["id"])
            self.reminder_list.addItem(it)
        self.calendar.reminder_dates = dates
        self.calendar.updateCells()

    def _default_when(self, d=None):
        d = d if isinstance(d, QDate) and d.isValid() else self.calendar.selectedDate()
        now = QDateTime.currentDateTime()
        if d == QDate.currentDate():
            t = now.addSecs(3600)
            t.setTime(t.time().addSecs(-(t.time().minute() * 60 + t.time().second())))
            return t
        return QDateTime(d, now.time().addSecs(-(now.time().minute() * 60 + now.time().second())))

    def _reload_reminders(self, refresh=True):
        self.reminders = self.store.load_reminders()
        self._rem_mtime = self.store.rem_mtime()
        if refresh:
            self.refresh_reminders()

    def _commit_reminders(self):
        self.store.save_reminders(self.reminders)
        self._rem_mtime = self.store.rem_mtime()
        self.refresh_reminders()

    def add_reminder(self, text="", date=None):
        # also connected to clicked/triggered signals, which pass a bool
        dlg = ReminderDialog(self, self._default_when(date), text if isinstance(text, str) else "")
        if dlg.exec_() and dlg.text.text().strip():
            self._reload_reminders(refresh=False)
            self.reminders.append({
                "id": uuid.uuid4().hex,
                "text": dlg.text.text().strip(),
                "when": dlg.when.dateTime().toString("yyyy-MM-ddTHH:mm:00"),
                "repeat": dlg.repeat.currentText(),
            })
            self._commit_reminders()

    def _find(self, item):
        rid = item.data(Qt.UserRole)
        return next((r for r in self.reminders if r["id"] == rid), None)

    def edit_reminder(self, item):
        r = self._find(item)
        if not r:
            return
        when = QDateTime.fromString(r["when"], "yyyy-MM-ddTHH:mm:00")
        dlg = ReminderDialog(self, when, r["text"], r.get("repeat", "none"))
        if dlg.exec_() and dlg.text.text().strip():
            self._reload_reminders(refresh=False)
            r = next((x for x in self.reminders if x["id"] == r["id"]), None)
            if r is None:  # fired or removed in the meantime
                self.refresh_reminders()
                return
            r["text"] = dlg.text.text().strip()
            r["when"] = dlg.when.dateTime().toString("yyyy-MM-ddTHH:mm:00")
            r["repeat"] = dlg.repeat.currentText()
            self._commit_reminders()
            self.calendar.setSelectedDate(dlg.when.date())

    def _reminder_menu(self, pos):
        item = self.reminder_list.itemAt(pos)
        menu = QMenu(self)
        menu.addAction("New reminder...", self.add_reminder)
        if item:
            menu.addAction("Edit...", lambda: self.edit_reminder(item))
            menu.addAction("Delete", lambda: self.delete_reminder(item))
        menu.exec_(self.reminder_list.viewport().mapToGlobal(pos))

    def delete_reminder(self, item):
        rid = item.data(Qt.UserRole)
        self._reload_reminders(refresh=False)
        self.reminders = [x for x in self.reminders if x["id"] != rid]
        self._commit_reminders()

    def keyPressEvent(self, e):
        if e.key() == Qt.Key_Delete and self.reminder_list.hasFocus() \
                and self.reminder_list.currentItem():
            self.delete_reminder(self.reminder_list.currentItem())
            return
        super().keyPressEvent(e)

    def check_reminders(self):
        # when the background service runs it fires reminders; we only mirror the file
        if not daemon_running(self.store):
            self.store.fire_due(self.notify)
        if self.store.rem_mtime() != self._rem_mtime:
            self._reload_reminders()

    def agent_settings_dialog(self):
        dlg = AgentSettingsDialog(self)
        if dlg.exec_() == QDialog.Accepted:
            dlg.save()

    def install_launcher(self):
        try:
            path = install_launcher()
        except OSError as e:
            QMessageBox.warning(self, APP_NAME, f"Could not create the launcher: {e}")
            return
        QMessageBox.information(
            self, APP_NAME,
            f"Launcher created:\n{path}\n\nFind 'aNoter' in your application menu "
            "(Activities > type aNoter); pin it to the dock to keep the icon.\n"
            "Restart aNoter once so the window picks up the icon.")

    def set_background(self, on):
        if on:
            enable_background(self.store)
            self.statusBar().showMessage(
                "Background reminders enabled - they work even when aNoter is closed.", 8000)
        else:
            disable_background(self.store)
            self.statusBar().showMessage(
                "Background reminders disabled - reminders only fire while aNoter is open.", 8000)

    def _offer_background(self):
        if self.settings.value("asked_background", False, type=bool):
            return
        self.settings.setValue("asked_background", True)
        if autostart_enabled():
            return
        r = QMessageBox.question(
            self, "Background reminders",
            "Reminders only fire while aNoter is open.\n\n"
            "Run a small background service at login so reminders\n"
            "also work when aNoter is closed?")
        if r == QMessageBox.Yes:
            self.act_background.setChecked(True)

    def notify(self, title, body):
        self.statusBar().showMessage(f"{title}: {body}", 15000)
        shown = alert(self.store, title, body)
        if not shown and QSystemTrayIcon.isSystemTrayAvailable():
            self.tray.show()
            self.tray.showMessage(title, body, QSystemTrayIcon.Information, 10000)
        QApplication.alert(self, 0)

    def set_sound(self, on):
        self.store.set_config(sound=on)
        if on:
            play_sound(self.store)

    def choose_sound(self):
        from PyQt5.QtWidgets import QFileDialog
        start = self.store.config().get("sound_file") or "/usr/share/sounds"
        path, _ = QFileDialog.getOpenFileName(
            self, "Choose reminder sound", start,
            "Audio (*.wav *.oga *.ogg *.mp3 *.flac);;All files (*)")
        if path:
            self.store.set_config(sound_file=path, sound=True)
            self.act_sound.blockSignals(True)  # avoid playing the sound twice
            self.act_sound.setChecked(True)
            self.act_sound.blockSignals(False)
            play_sound(self.store)

    def reset_sound(self):
        self.store.set_config(sound_file="")
        play_sound(self.store)

    # ---- shutdown
    def closeEvent(self, e):
        self.notes.flush()
        self._save_session()
        self.search.shutdown()
        if not (self.notes.close_all() and self.files.close_all()):
            e.ignore()
            return
        self.settings.setValue("geometry", self.saveGeometry())
        self.settings.setValue("split", self.main_split.saveState())
        self.settings.setValue("left_split", self.left.saveState())
        self.settings.setValue("root", self.explorer.root)
        e.accept()


def main():
    sys.excepthook = lambda *a: traceback.print_exception(*a)
    if "--daemon" in sys.argv:
        sys.exit(run_daemon())
    app = QApplication(sys.argv)
    app.setApplicationName(APP_NAME)
    app.setDesktopFileName(APP_NAME)   # app id "aNoter" (not "Noter.py") -> matches aNoter.desktop
    app.setWindowIcon(make_app_icon())
    win = MainWindow([a for a in sys.argv[1:] if not a.startswith('--') and os.path.isfile(a)])
    win.show()
    sys.exit(app.exec_())


if __name__ == "__main__":
    main()
