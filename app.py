"""
Text Typing Video Generator

Scans a folder for text, CSV, and Markdown files, lets you pick them with checkboxes,
then renders typing-animation MP4 videos (with procedural audio) via FFmpeg.

Requirements:  Python 3.9+, PySide6, numpy, FFmpeg (on PATH).
Usage:         python text_typing.py
"""

from __future__ import annotations

import bisect
import io
import json
import logging
import math
import os
import platform
import random
import re
import string
import subprocess
import sys
import shutil
import tempfile
import threading
import time as _time
import wave
from collections import OrderedDict, deque
from contextlib import contextmanager
from dataclasses import dataclass
from datetime import datetime
from enum import Enum
from typing import Dict, List, Optional, Tuple, Callable

import numpy as np
from PySide6.QtCore import (
    QEvent, QPointF, QPoint, QRect, Qt, QThread, Signal, QTimer, QUrl, 
    QBuffer, QIODevice, QObject, Slot,
)
from PySide6.QtGui import (
    QColor, QFont, QFontDatabase, QFontMetrics, QImage, QLinearGradient, QPainter, QPalette, QPen, QBrush, QPainterPath, QPixmap, QPolygonF,
)
from PySide6.QtMultimedia import QAudioOutput, QMediaPlayer
from PySide6.QtWidgets import (
    QApplication, QCheckBox, QComboBox, QDialog, QDoubleSpinBox,
    QFileDialog, QGridLayout, QGroupBox, QHBoxLayout, QHeaderView,
    QLabel, QMainWindow, QMessageBox, QProgressBar, QPushButton,
    QSizePolicy, QStatusBar, QStyleFactory, QTabWidget,
    QTableWidget, QTableWidgetItem, QVBoxLayout, QWidget, QScrollArea,
    QFormLayout, QFrame, QDialogButtonBox, QSlider, QGraphicsDropShadowEffect,
    QLineEdit, QSpinBox, QMenu, QSplitter,
)

# Numba JIT compilation for audio mixing performance
try:
    import numba
    _HAS_NUMBA = True
except ImportError:
    _HAS_NUMBA = False

if _HAS_NUMBA:
    @numba.njit(cache=True)
    def _nb_mix_sounds(mix, sounds_flat, offsets, lengths, starts):
        for i in range(len(starts)):
            s = starts[i]; ln = lengths[i]; o = offsets[i]
            for j in range(ln):
                mix[s + j] += sounds_flat[o + j]

    @numba.njit(cache=True, parallel=True)
    def _nb_chunked_peak(mix, chunk_size):
        n = len(mix)
        n_chunks = (n + chunk_size - 1) // chunk_size
        peaks = np.empty(n_chunks, dtype=np.float32)
        for c in numba.prange(n_chunks):
            cs = c * chunk_size; ce = cs + chunk_size
            if ce > n: ce = n
            p = np.float32(0.0)
            for i in range(cs, ce):
                v = mix[i]
                if v < 0.0: v = -v
                if v > p: p = v
            peaks[c] = p
        return peaks

# =====================================================================
# 1. CONFIGURATION & CONSTANTS
# =====================================================================

log = logging.getLogger("SimpleTTVG")
log.setLevel(logging.INFO)

_formatter = logging.Formatter(
    "%(asctime)s | %(levelname)-7s | %(message)s",
    datefmt="%H:%M:%S",
)

_file_handler = logging.FileHandler("text_typing.log", mode='w', encoding='utf-8')
_file_handler.setFormatter(_formatter)
log.addHandler(_file_handler)

_console_handler = logging.StreamHandler()
_console_handler.setFormatter(_formatter)
log.addHandler(_console_handler)

CWD = os.getcwd()
INPUT_DIR  = os.path.join(CWD, "input")
OUTPUT_DIR = os.path.join(CWD, "output")
TEMP_DIR   = os.path.join(CWD, "temp")
SETTINGS_FILE = os.path.join(CWD, "settings.json")

for _d in (INPUT_DIR, OUTPUT_DIR, TEMP_DIR):
    os.makedirs(_d, exist_ok=True)

SUPPORTED_EXTENSIONS = frozenset({".txt", ".csv", ".md"})

_SKIP_DIRS = frozenset({
    ".git", ".hg", ".svn", "__pycache__", "node_modules",
    ".venv", "venv", ".env", ".idea", ".vscode", "dist",
    "build", ".tox", ".mypy_cache", ".pytest_cache", ".next",
    ".nuxt", "target", "vendor", ".bundle",
})

EXT_TO_LANGUAGE: dict[str, str] = {
    ".txt": "Text",
    ".csv": "Text",
    ".md": "Markdown",
}

RESOLUTIONS: Dict[str, Tuple[int, int]] = {
    "1920x1080": (1920, 1080),
    "1280x720":  (1280, 720),
    "1080x1920 (9:16)": (1080, 1920),
    "1080x1080 (1:1)": (1080, 1080),
}

ENCODERS = {
    "YouTube Optimized (H.264/AAC)": ["-c:v", "libx264", "-preset", "medium", "-crf", "18", "-maxrate", "8M", "-bufsize", "16M", "-pix_fmt", "yuv420p", "-g", "60", "-keyint_min", "60", "-sc_threshold", "0"],
    "x264 (CPU, Best Quality)": ["-c:v", "libx264", "-preset", "slow", "-crf", "18"],
    "x264 (CPU, Fast)": ["-c:v", "libx264", "-preset", "medium", "-crf", "20"],
    "NVENC (NVIDIA)": ["-c:v", "h264_nvenc", "-preset", "p5", "-rc", "vbr", "-cq", "20", "-b:v", "0"],
    "QSV (Intel)": ["-c:v", "h264_qsv", "-preset", "medium", "-global_quality", "20"],
    "AMF (AMD)": ["-c:v", "h264_amf", "-preset", "speed", "-rc", "cqp", "-qp_i", "20", "-qp_p", "20"],
}

THEMES: Dict[str, Dict[str, str]] = {
    "Dracula": {
        "background": "#282a36", "foreground": "#f8f8f2",
        "comment": "#6272a4", "keyword": "#ff79c6", "string": "#f1fa8c",
        "number": "#bd93f9", "function": "#50fa7b", "builtin": "#8be9fd",
        "decorator": "#50fa7b", "operator": "#ff79c6", "class_name": "#8be9fd",
        "line_number": "#6272a4", "current_line": "#44475a", "cursor": "#f8f8f2",
        "title_bar": "#21222c", "title_text": "#8be9fd",
        "window_border": "#191a21",
    },
    "One Dark": {
        "background": "#282c34", "foreground": "#abb2bf",
        "comment": "#5c6370", "keyword": "#c678dd", "string": "#98c379",
        "number": "#d19a66", "function": "#61afef", "builtin": "#e5c07b",
        "decorator": "#56b6c2", "operator": "#c678dd", "class_name": "#e5c07b",
        "line_number": "#4b5263", "current_line": "#2c313c", "cursor": "#528bff",
        "title_bar": "#21252b", "title_text": "#61afef",
        "window_border": "#181a1f",
    },
    "GitHub Dark": {
        "background": "#0d1117", "foreground": "#c9d1d9",
        "comment": "#8b949e", "keyword": "#ff7b72", "string": "#a5d6ff",
        "number": "#79c0ff", "function": "#d2a8ff", "builtin": "#ffa657",
        "decorator": "#ffa657", "operator": "#ff7b72", "class_name": "#ffa657",
        "line_number": "#484f58", "current_line": "#161b22", "cursor": "#58a6ff",
        "title_bar": "#010409", "title_text": "#58a6ff",
        "window_border": "#010409",
    },
    "Monokai": {
        "background": "#272822", "foreground": "#f8f8f2",
        "comment": "#75715e", "keyword": "#f92672", "string": "#e6db74",
        "number": "#ae81ff", "function": "#a6e22e", "builtin": "#66d9ef",
        "decorator": "#a6e22e", "operator": "#f92672", "class_name": "#66d9ef",
        "line_number": "#75715e", "current_line": "#3e3d32", "cursor": "#f8f8f2",
        "title_bar": "#1e1f1c", "title_text": "#a6e22e",
        "window_border": "#1e1f1c",
    },
    "Solarized Dark": {
        "background": "#002b36", "foreground": "#839496",
        "comment": "#586e75", "keyword": "#859900", "string": "#2aa198",
        "number": "#d33682", "function": "#268bd2", "builtin": "#b58900",
        "decorator": "#b58900", "operator": "#859900", "class_name": "#b58900",
        "line_number": "#586e75", "current_line": "#073642", "cursor": "#93a1a1",
        "title_bar": "#073642", "title_text": "#268bd2",
        "window_border": "#001e26",
    },
    "VS Code Dark+": {
        "background": "#1e1e1e", "foreground": "#d4d4d4",
        "comment": "#6a9955", "keyword": "#569cd6", "string": "#ce9178",
        "number": "#b5cea8", "function": "#dcdcaa", "builtin": "#4ec9b0",
        "decorator": "#4ec9b0", "operator": "#d4d4d4", "class_name": "#4ec9b0",
        "line_number": "#858585", "current_line": "#2a2d2e", "cursor": "#aeafad",
        "title_bar": "#323233", "title_text": "#007acc",
        "window_border": "#323233",
    },
    "Light (Paper)": {
        "background": "#fafafa", "foreground": "#383a42",
        "comment": "#a0a1a7", "keyword": "#a626a4", "string": "#50a14f",
        "number": "#986801", "function": "#4078f2", "builtin": "#c18401",
        "decorator": "#4078f2", "operator": "#a626a4", "class_name": "#c18401",
        "line_number": "#d0d0d0", "current_line": "#f0f0f0", "cursor": "#383a42",
        "title_bar": "#e8e8e8", "title_text": "#4078f2",
        "window_border": "#d0d0d0",
    },
}

# =====================================================================
# 2. EXPERT PATTERNS & UTILITIES
# =====================================================================

class ExportStatus(Enum):
    PENDING = "Pending"
    RENDERING = "Rendering"
    DONE = "Done"
    FAILED = "Failed"

@contextmanager
def painter_context(target):
    """Context manager for QPainter to ensure proper begin/end lifecycle."""
    p = QPainter(target)
    try:
        yield p
    finally:
        p.end()

@contextmanager
def signals_blocked(qt_obj):
    """Context manager to temporarily block Qt signals."""
    blocked = qt_obj.blockSignals(True)
    try:
        yield
    finally:
        qt_obj.blockSignals(blocked)


# =====================================================================
# 3. LANGUAGE DEFINITIONS & TOKENIZER
# =====================================================================

_LANG_DATA: Dict[str, dict] = {
    "Markdown": {
        "keywords": set(),
        "builtins": set(),
        "extra_patterns": [
            ("keyword", r"^\s*#{1,6}\s.*$|^\s*[-*+]\s|^\s*\d+\.\s|^\s*>"),
            ("decorator", r"\*\*[^*]*\*\*|__[^_]*__|`[^`]*`|\*[^*]*\*|_[^_]*_"),
        ],
        "comment": r"<!--[\s\S]*?-->",
        "string":  r"\[.*?\]\(.*?\)|!\[.*?\]\(.*?\)",
        "number":  r"(?!x)x",
    },
    "Text": {
        "keywords": set(),
        "builtins": set(),
        "extra_patterns": [],
        "comment": r"(?!x)x",
        "string":  r"(?!x)x",
        "number":  r"(?!x)x",
        "plain": True,
    },
}


class Tokenizer:
    _COMPILED: Dict[str, re.Pattern] = {}
    _LOCK = threading.Lock()

    @classmethod
    def _compile(cls, lang: str) -> re.Pattern:
        if lang not in cls._COMPILED:
            with cls._LOCK:
                if lang not in cls._COMPILED:
                    data = _LANG_DATA.get(lang, _LANG_DATA["Text"])
                    patterns = list(data.get("extra_patterns", []))
                    if data.get("plain"):
                        patterns.extend([
                            ("whitespace", r"\s+"),
                            ("other", r"."),
                        ])
                    else:
                        patterns.extend([
                            ("comment",    data["comment"]),
                            ("string",     data["string"]),
                            ("number",     data["number"]),
                        ])
                        if data.get("keywords"):
                            patterns.append(("keyword", r"\b(?:" + "|".join(data["keywords"]) + r")\b"))
                        if data.get("builtins"):
                            patterns.append(("builtin", r"\b(?:" + "|".join(data["builtins"]) + r")\b"))
                        patterns.extend([
                            ("function",   r"\b([a-zA-Z_]\w*)\s*(?=\()"),
                            ("identifier", r"\b[a-zA-Z_]\w*\b"),
                            ("operator",   r"[+\-*/%=<>!&|^~]+"),
                            ("bracket",    r"[(){}[\]]"),
                            ("punctuation",r"[;:,.]"),
                            ("whitespace", r"\s+"),
                            ("other",      r"."),
                        ])
                    pat_str = "|".join(f"(?P<{n}>{p})" for n, p in patterns)
                    cls._COMPILED[lang] = re.compile(pat_str, re.MULTILINE | re.DOTALL)
        return cls._COMPILED[lang]

    @classmethod
    def tokenize(cls, text: str, lang: str) -> List[Tuple[str, str]]:
        compiled = cls._COMPILED.get(lang) or cls._compile(lang)
        return [(m.lastgroup, m.group()) for m in compiled.finditer(text)]


# =====================================================================
# 4. FILE READING HELPERS
# =====================================================================

def _read_text_file(path: str, clean: bool = True) -> str:
    with open(path, "r", encoding="utf-8", errors="replace") as f:
        text = f.read()
    
    if clean:
        text = text.replace("\xa0", " ").replace("\xad", "")
        text = re.sub(r'[ \t]+\n', '\n', text)
        text = re.sub(r'\n{3,}', '\n\n', text)
        text = "\n".join(line.rstrip() for line in text.splitlines())
    return text


# =====================================================================
# 5. AUDIO GENERATION & DSP ENGINE
# =====================================================================

SOUND_PRESETS = {
    "Mechanical": {"description": "Cherry MX Blue: click jacket transient, FM tactile bump, housing resonance, sub-bass body, and housing rattle"},
    "Cherry MX Red": {"description": "Linear thock: deep sub-bass, keycap housing resonance, minimal high-frequency transient"},
    "Cherry Brown": {"description": "Tactile bump: dual-filtered mid-range FM with smooth exponential decay envelope"},
    "IBM Model M": {"description": "Buckling spring: metallic FM ping with long decay, membrane snap, and housing resonance"},
    "Logitech MX": {"description": "Scissor switch: shallow, crisp, highly dampened with quick transient response"},
    "Typewriter": {"description": "Type bar strike with platen resonance and carriage bell on Enter (modal synthesis)"},
    "Cash Register": {"description": "Mechanical key with drawer mechanism and ka-ching bell on Enter (modal synthesis)"},
    "Bubble Pop": {"description": "Cavity resonance with pitch sweep and membrane rupture broadband burst"},
    "Rain Drops": {"description": "Water droplet modal synthesis with surface tension resonance and splash tail"},
    "Membrane": {"description": "Rubber dome collapse with muffled low-frequency resonance and slow attack"},
    "Crystal": {"description": "Inharmonic modal bell with stretched partials and long exponential decay"},
    "Wooden": {"description": "Marimba bar with odd-harmonic modes and resonator tube coupling"},
    "Soft Foam": {"description": "Compressed foam thud with damped low-frequency resonance and no high-frequency content"},
    "Cat Paws": {"description": "Soft pad impact with fur-damped transients and gentle low-frequency body"},
}

CLICK_DURATIONS: Dict[str, float] = {
    "Mechanical": 0.12, "Cherry MX Red": 0.10, "Cherry Brown": 0.09,
    "IBM Model M": 0.25, "Logitech MX": 0.06, "Typewriter": 0.15,
    "Cash Register": 0.12, "Bubble Pop": 0.12, "Rain Drops": 0.10,
    "Membrane": 0.10, "Crystal": 0.40, "Wooden": 0.18, "Soft Foam": 0.18, "Cat Paws": 0.10,
}

_QWERTY_KEY_ROWS_SOUND = (
    "`1234567890-=",
    "qwertyuiop[]\\",
    "asdfghjkl;'",
    "zxcvbnm,./",
)
_SOUND_KEY_POS: Dict[str, Tuple[int, int]] = {}
for _r, _row in enumerate(_QWERTY_KEY_ROWS_SOUND):
    for _c, _ch in enumerate(_row):
        _SOUND_KEY_POS[_ch] = (_r, _c)

_US_SHIFT_MAP_SOUND: Dict[str, str] = {
    "~": "`", "!": "1", "@": "2", "#": "3", "$": "4", "%": "5",
    "^": "6", "&": "7", "*": "8", "(": "9", ")": "0",
    "_": "-", "+": "=", "{": "[", "}": "]", "|": "\\",
    ":": ";", '"': "'", "<": ",", ">": ".", "?": "/",
}

def _get_char_rc(ch: str) -> Tuple[int, int]:
    c = ch.lower()
    if c in _US_SHIFT_MAP_SOUND:
        c = _US_SHIFT_MAP_SOUND[c].lower()
    return _SOUND_KEY_POS.get(c, (2, 5))


class DSP:
    @staticmethod
    def env_exp(n: int, sr: int, attack: float = 0.001,
                decay_rate: float = 30.0, attack_curve: float = 2.0) -> np.ndarray:
        t = np.arange(n, dtype=np.float64) / sr
        env = np.exp(-t * decay_rate)
        a_samp = max(1, int(attack * sr))
        if a_samp < n:
            a_env = np.linspace(0, 1, a_samp) ** attack_curve
            env[:a_samp] = a_env * np.exp(
                -np.arange(a_samp, dtype=np.float64) / sr * decay_rate
            )
        return env

    @staticmethod
    def env_adsr(n: int, sr: int, attack: float = 0.0005,
                 decay: float = 0.005, sustain: float = 0.0,
                 release: float = 0.05, attack_curve: float = 2.0,
                 decay_rate: float = 100.0, release_rate: float = 30.0) -> np.ndarray:
        """Full ADSR envelope with vectorized computation.
        For percussive sounds (key clicks), set sustain=0.0.
        The release phase starts at max(sustain_end, n - release_samples)."""
        env = np.zeros(n, dtype=np.float64)
        if n <= 0:
            return env

        a_n = max(1, int(attack * sr))
        d_n = max(1, int(decay * sr))
        r_n = max(1, int(release * sr))

        a_n = min(a_n, n)
        d_n = min(d_n, max(0, n - a_n))
        sus_start = a_n + d_n
        rel_start = max(sus_start, n - r_n)
        if rel_start < 0:
            rel_start = 0

        # Attack phase: curved rise from 0 to 1
        if a_n > 0:
            env[:a_n] = np.linspace(0, 1, a_n, dtype=np.float64) ** attack_curve

        # Decay phase: exponential fall from 1.0 to sustain level
        if d_n > 0 and sus_start <= n:
            t_d = np.arange(min(d_n, n - a_n), dtype=np.float64) / sr
            d_len = len(t_d)
            env[a_n:a_n + d_len] = sustain + (1.0 - sustain) * np.exp(-t_d * decay_rate)

        # Sustain phase: constant level
        if rel_start > sus_start:
            env[sus_start:rel_start] = sustain

        # Release phase: exponential fall from current level to 0
        if n > rel_start:
            t_r = np.arange(n - rel_start, dtype=np.float64) / sr
            rel_level = env[rel_start] if rel_start > 0 and rel_start < n else sustain
            env[rel_start:] = rel_level * np.exp(-t_r * release_rate)

        return env

    @staticmethod
    def fir_lowpass(cutoff: float, sr: int = 44100, n_taps: int = 127,
                    window: str = "blackman") -> np.ndarray:
        if n_taps % 2 == 0: n_taps += 1
        fc = cutoff / sr
        n = np.arange(n_taps, dtype=np.float64)
        center = (n_taps - 1) / 2.0
        h = np.sinc(2 * fc * (n - center))
        if window == "blackman":
            w = (0.42 - 0.5*np.cos(2*np.pi*n/(n_taps-1))
                 + 0.08*np.cos(4*np.pi*n/(n_taps-1)))
        elif window == "hamming":
            w = 0.54 - 0.46*np.cos(2*np.pi*n/(n_taps-1))
        elif window == "hann":
            w = 0.5 - 0.5*np.cos(2*np.pi*n/(n_taps-1))
        else:
            w = np.ones(n_taps)
        h *= w
        s = np.sum(h)
        if s > 0: h /= s
        return h

    @staticmethod
    def fir_highpass(cutoff: float, sr: int = 44100, n_taps: int = 127,
                     window: str = "blackman") -> np.ndarray:
        hlp = DSP.fir_lowpass(cutoff, sr, n_taps, window)
        h = -hlp; h[len(h)//2] += 1.0
        return h

    @staticmethod
    def fir_bandpass(low: float, high: float, sr: int = 44100,
                     n_taps: int = 255, window: str = "blackman") -> np.ndarray:
        h_hi = DSP.fir_lowpass(high, sr, n_taps, window)
        h_lo = DSP.fir_lowpass(low, sr, n_taps, window)
        return h_hi - h_lo

    @staticmethod
    def convolve(x: np.ndarray, h: np.ndarray) -> np.ndarray:
        n = len(x); nh = len(h)
        if nh <= 1:
            return x * h[0] if nh == 1 else x
        if nh < 64 and n < 2048:
            return np.convolve(x, h, mode='full')[:n]
        n_fft = 1 << ((n + nh - 1).bit_length())
        X = np.fft.rfft(x, n_fft)
        H = np.fft.rfft(h, n_fft)
        return np.fft.irfft(X * H, n_fft)[:n]

    @staticmethod
    def filt_lp(x, cutoff, sr=44100, n_taps=127):
        return DSP.convolve(x, DSP.fir_lowpass(cutoff, sr, n_taps))

    @staticmethod
    def filt_hp(x, cutoff, sr=44100, n_taps=127):
        return DSP.convolve(x, DSP.fir_highpass(cutoff, sr, n_taps))

    @staticmethod
    def filt_bp(x, low, high, sr=44100, n_taps=255):
        return DSP.convolve(x, DSP.fir_bandpass(low, high, sr, n_taps))

    @staticmethod
    def filt_resonator(x, freq, q, sr=44100, gain=1.0):
        w0 = 2 * np.pi * freq / sr
        r = np.exp(-w0 / (2 * max(0.5, q)))
        wd = w0 * np.sqrt(max(0.0, 1.0 - 1.0/(4*q*q))) if q > 0.5 else w0
        decay_time = max(0.005, 6.0 * q / max(1.0, freq))
        n_ir = min(len(x), max(16, int(sr * decay_time)))
        t = np.arange(n_ir, dtype=np.float64)
        ir = (r ** t) * np.sin(wd * t)
        peak = np.max(np.abs(ir))
        if peak > 1e-10: ir = ir / peak * gain
        return DSP.convolve(x, ir)

    @staticmethod
    def dc_block(x, sr=44100):
        return DSP.filt_hp(x, 20.0, sr, n_taps=63)

    @staticmethod
    def osc_sine(freq, n, sr, phase=0.0):
        t = np.arange(n, dtype=np.float64) / sr
        return np.sin(2*np.pi*freq*t + phase)

    @staticmethod
    def osc_fm(carrier, mod_ratio, mod_index, n, sr, phase=0.0):
        t = np.arange(n, dtype=np.float64) / sr
        mod_f = carrier * mod_ratio
        return np.sin(2*np.pi*carrier*t + mod_index*np.sin(2*np.pi*mod_f*t) + phase)

    @staticmethod
    def osc_fm_multi(carrier, mod_ratios, mod_indices, n, sr):
        t = np.arange(n, dtype=np.float64) / sr
        ph = 2*np.pi*carrier*t
        for mr, mi in zip(mod_ratios, mod_indices):
            ph += mi * np.sin(2*np.pi*carrier*mr*t)
        return np.sin(ph)

    @staticmethod
    def osc_saw(freq, n, sr):
        t = np.arange(n, dtype=np.float64) / sr
        sig = np.zeros(n)
        for h in range(1, 17):
            fh = freq * h
            if fh >= sr * 0.45: break
            sig += np.sin(2*np.pi*fh*t) / h
        return sig * 0.5

    @staticmethod
    def noise_white(n, rng):
        return rng.randn(n).astype(np.float64)

    @staticmethod
    def noise_pink(n, rng):
        white = rng.randn(n).astype(np.float64)
        fft = np.fft.rfft(white)
        freqs = np.fft.rfftfreq(n, 1.0/44100)
        freqs[0] = max(freqs[1] if len(freqs) > 1 else 1.0, 1.0)
        fft[1:] /= np.sqrt(np.abs(freqs[1:]))
        fft[0] = 0
        return np.fft.irfft(fft, n=n)

    @staticmethod
    def noise_brown(n, rng):
        white = rng.randn(n).astype(np.float64)
        brown = np.cumsum(white)
        brown -= np.mean(brown)
        peak = np.max(np.abs(brown))
        if peak > 0: brown = brown / peak
        return brown * 0.5

    @staticmethod
    def modal(modes, n, sr, inharmonicity=0.0):
        t = np.arange(n, dtype=np.float64) / sr
        out = np.zeros(n, dtype=np.float64)
        f0 = modes[0][0] if modes else 440.0
        for freq, decay, amp in modes:
            af = freq
            if inharmonicity > 0:
                nh = freq / f0
                af = freq * np.sqrt(1 + inharmonicity * nh * nh)
            out += np.sin(2*np.pi*af*t) * np.exp(-decay*t) * amp
        return out

    @staticmethod
    def sat_tanh(x, drive=1.0):
        if drive <= 0: return x
        return np.tanh(x * drive) / max(0.001, np.tanh(drive))

    @staticmethod
    def sat_hard(x, threshold=1.0):
        return np.clip(x, -threshold, threshold)

    @staticmethod
    def normalize(x, target_db=-1.0):
        peak = np.max(np.abs(x))
        if peak < 1e-10: return x
        return x * (10**(target_db/20) / peak)

    @staticmethod
    def to_int16(x, target_db=-1.0):
        x = DSP.normalize(x, target_db)
        x = DSP.sat_hard(x, 1.0)
        return (x * 32767).astype(np.int16)


@dataclass(slots=True)
class Voice:
    osc: str = "sine"
    freq: float = 440.0
    fm_ratio: float = 1.0
    fm_index: float = 0.0
    fm_ratios: Optional[List[float]] = None
    fm_indices: Optional[List[float]] = None
    # ADSR envelope parameters
    attack: float = 0.001
    decay: float = 0.005
    sustain: float = 0.0
    release: float = 0.05
    attack_curve: float = 2.0
    decay_rate: float = 100.0
    release_rate: float = 30.0
    env_type: str = "adsr"  # "adsr" or "exp"
    # Legacy exponential envelope params (used when env_type == "exp")
    decay_rate_exp: float = 30.0
    # Filter
    filt: str = "none"
    f_cutoff: float = 8000.0
    f_high: float = 12000.0
    f_q: float = 1.0
    # Saturation / gain
    drive: float = 0.0
    gain: float = 0.5
    delay: float = 0.0
    # Modal synthesis
    modes: Optional[List[Tuple[float, float, float]]] = None
    inharmonicity: float = 0.0


def _apply_asmr_tail(snd: np.ndarray, sr: int, seed: int,
                     decay: float = 0.2, vol: float = 0.05) -> np.ndarray:
    n_tail = int(sr * decay)
    if n_tail < 10 or vol <= 0:
        return snd
    rng = np.random.RandomState(seed + 9999)
    t = np.linspace(0, decay, n_tail, False)
    ir = rng.randn(n_tail) * np.exp(-t * 8.0)
    for delay_t, gain in [(0.003, 0.4), (0.007, 0.3), (0.011, 0.2), (0.015, 0.15)]:
        ds = int(delay_t * sr)
        if ds < n_tail:
            ir[ds] += gain
    ir = DSP.filt_lp(ir, 4000.0, sr, n_taps=63)
    peak = np.max(np.abs(ir))
    if peak > 0:
        ir = ir / peak * vol
    snd_f = snd.astype(np.float64) / 32767.0
    tail_start = max(0, len(snd_f) - int(sr * 0.05))
    tail = snd_f[tail_start:]
    reverb = DSP.convolve(tail, ir)
    out = np.concatenate([
        snd_f[:tail_start],
        snd_f[tail_start:] + reverb[:len(tail)]
    ])
    if len(reverb) > len(tail):
        out = np.concatenate([out, reverb[len(tail):]])
    return DSP.to_int16(DSP.normalize(out, -1.0))


class SoundRenderer:
    def __init__(self, sr: int = 44100):
        self.sr = sr

    def render(self, voices: List[Voice], duration: float,
               rng: np.random.RandomState) -> np.ndarray:
        n = int(self.sr * duration)
        if n <= 0:
            return np.zeros(0, dtype=np.float64)
        mix = np.zeros(n, dtype=np.float64)
        for v in voices:
            sig = self._render_voice(v, n, rng)
            d_samp = int(v.delay * self.sr)
            if d_samp > 0:
                if d_samp >= n: continue
                sig = np.concatenate([np.zeros(d_samp, dtype=np.float64),
                                      sig[:n-d_samp]])
            if len(sig) < n:
                sig = np.concatenate([sig, np.zeros(n - len(sig))])
            else:
                sig = sig[:n]
            mix += sig
        mix = DSP.dc_block(mix, self.sr)
        return mix

    def _render_voice(self, v: Voice, n: int,
                      rng: np.random.RandomState) -> np.ndarray:
        if v.osc == "sine":
            sig = DSP.osc_sine(v.freq, n, self.sr)
        elif v.osc == "fm":
            if v.fm_ratios:
                sig = DSP.osc_fm_multi(v.freq, v.fm_ratios, v.fm_indices, n, self.sr)
            else:
                sig = DSP.osc_fm(v.freq, v.fm_ratio, v.fm_index, n, self.sr)
        elif v.osc == "noise_white":
            sig = DSP.noise_white(n, rng)
        elif v.osc == "noise_pink":
            sig = DSP.noise_pink(n, rng)
        elif v.osc == "noise_brown":
            sig = DSP.noise_brown(n, rng)
        elif v.osc == "modal":
            if v.modes:
                sig = DSP.modal(v.modes, n, self.sr, v.inharmonicity)
            else:
                sig = DSP.noise_white(n, rng)
        elif v.osc == "saw":
            sig = DSP.osc_saw(v.freq, n, self.sr)
        else:
            sig = np.zeros(n, dtype=np.float64)

        # Apply ADSR or legacy exponential envelope
        if v.env_type == "adsr":
            env = DSP.env_adsr(
                n, self.sr,
                attack=v.attack, decay=v.decay, sustain=v.sustain,
                release=v.release, attack_curve=v.attack_curve,
                decay_rate=v.decay_rate, release_rate=v.release_rate,
            )
        else:
            env = DSP.env_exp(n, self.sr, attack=v.attack,
                              decay_rate=v.decay_rate_exp,
                              attack_curve=v.attack_curve)
        sig *= env

        # Apply filter
        if v.filt == "lp":
            sig = DSP.filt_lp(sig, v.f_cutoff, self.sr)
        elif v.filt == "hp":
            sig = DSP.filt_hp(sig, v.f_cutoff, self.sr)
        elif v.filt == "bp":
            sig = DSP.filt_bp(sig, v.f_cutoff, v.f_high, self.sr)
        elif v.filt == "resonator":
            sig = DSP.filt_resonator(sig, v.f_cutoff, v.f_q, self.sr)

        # Apply saturation
        if v.drive > 0:
            sig = DSP.sat_tanh(sig, v.drive)
        sig *= v.gain
        return sig


# =====================================================================
# VOICE HELPERS & SOUND GENERATORS
# Each models a full keypress with multiple acoustic components using
# proper ADSR envelopes.
# =====================================================================

def _v_click_transient(freq, gain=0.5, delay=0.0, rng=None):
    """Sharp broadband click transient — the 'click leaf' of a mechanical switch."""
    if rng: freq = freq * (2 ** rng.uniform(-0.12, 0.12))
    return Voice(
        osc="noise_white", env_type="adsr",
        attack=0.0001, decay=0.003, sustain=0.0, release=0.004,
        attack_curve=3.0, decay_rate=500.0, release_rate=400.0,
        filt="bp", f_cutoff=freq * 0.6, f_high=freq * 1.5,
        drive=2.0, gain=gain, delay=delay,
    )

def _v_fm_tactile(freq, fm_idx=0.4, gain=0.35, cutoff=3500, delay=0.0, rng=None):
    """Tactile bump — FM-synthesized mid-range tone felt during key travel."""
    if rng: freq = freq * (2 ** rng.uniform(-0.08, 0.08))
    return Voice(
        osc="fm", freq=freq, fm_ratio=2.0, fm_index=fm_idx,
        env_type="adsr",
        attack=0.0003, decay=0.005, sustain=0.0, release=0.01,
        attack_curve=2.0, decay_rate=200.0, release_rate=100.0,
        filt="lp", f_cutoff=cutoff, drive=1.2, gain=gain, delay=delay,
    )

def _v_housing(freq, gain=0.25, delay=0.0, rng=None):
    """Housing resonance — sustained sine ring from the switch enclosure."""
    if rng: freq = freq * (2 ** rng.uniform(-0.06, 0.06))
    return Voice(
        osc="sine", freq=freq, env_type="adsr",
        attack=0.0008, decay=0.015, sustain=0.15, release=0.03,
        attack_curve=1.5, decay_rate=80.0, release_rate=60.0,
        filt="lp", f_cutoff=2000, gain=gain, delay=delay,
    )

def _v_thock(freq, gain=0.40, delay=0.002, rng=None):
    """Bottom-out thock — low-frequency impact when key hits bottom."""
    if rng: freq = freq * (2 ** rng.uniform(-0.10, 0.10))
    return Voice(
        osc="sine", freq=freq, env_type="adsr",
        attack=0.0015, decay=0.008, sustain=0.0, release=0.04,
        attack_curve=2.5, decay_rate=150.0, release_rate=50.0,
        filt="lp", f_cutoff=600, gain=gain, delay=delay,
    )

def _v_sub(freq, gain=0.25, delay=0.003, rng=None):
    """Sub-bass body — very low frequency resonance from the keyboard chassis."""
    if rng: freq = freq * (2 ** rng.uniform(-0.05, 0.05))
    return Voice(
        osc="sine", freq=freq, env_type="adsr",
        attack=0.0025, decay=0.02, sustain=0.0, release=0.06,
        attack_curve=2.0, decay_rate=60.0, release_rate=30.0,
        filt="lp", f_cutoff=300, gain=gain, delay=delay,
    )

def _v_rattle(lo, hi, gain=0.06, delay=0.002):
    """Housing rattle — high-frequency noise from key wobble."""
    return Voice(
        osc="noise_white", env_type="adsr",
        attack=0.0005, decay=0.003, sustain=0.0, release=0.015,
        attack_curve=1.0, decay_rate=200.0, release_rate=100.0,
        filt="bp", f_cutoff=lo, f_high=hi,
        gain=gain, delay=delay,
    )

def _v_spring_ping(freq, gain=0.15, delay=0.005, rng=None):
    """Spring return ping — FM tone from the key spring on release."""
    if rng: freq = freq * (2 ** rng.uniform(-0.08, 0.08))
    mi = rng.uniform(0.6, 1.0) if rng else 0.8
    return Voice(
        osc="fm", freq=freq, fm_ratio=3.5, fm_index=mi,
        env_type="adsr",
        attack=0.0002, decay=0.005, sustain=0.0, release=0.08,
        attack_curve=1.5, decay_rate=80.0, release_rate=15.0,
        filt="lp", f_cutoff=12000, drive=0.8, gain=gain, delay=delay,
    )

def _v_modal_bell(freq, modes_ratios, gain=0.50, decay=4.0, inharmonicity=0.0,
                  rng=None):
    """Inharmonic modal bell for crystalline / typewriter bell sounds."""
    if rng: freq = freq * (2 ** rng.uniform(-0.03, 0.03))
    modes = [(freq * r, decay * (1 + i * 0.2), a)
             for i, (r, a) in enumerate(modes_ratios)]
    return Voice(
        osc="modal", modes=modes, inharmonicity=inharmonicity,
        env_type="adsr",
        attack=0.0001, decay=0.01, sustain=0.3, release=decay * 0.5,
        attack_curve=1.0, decay_rate=decay, release_rate=decay * 0.3,
        filt="lp", f_cutoff=16000, gain=gain,
    )

_BASE_FREQS = {0: 1100, 1: 850, 2: 600, 3: 400, -1: 120}

def _get_char_freq(char: str, row: int, col: int) -> float:
    base_f = _BASE_FREQS.get(row, 600)
    base_f *= (1.0 + (col - 5) * 0.015)
    if char.isupper() or char in _US_SHIFT_MAP_SOUND:
        base_f *= 1.2
    return base_f


def _make_mechanical_click(sr=44100, duration=0.15, seed=0, row=2, col=5, char='a'):
    """Cherry MX Blue: click leaf + tactile bump + housing + thock + sub + rattle + spring."""
    rng = np.random.RandomState(seed)
    R = SoundRenderer(sr)
    base_f = _get_char_freq(char, row, col) * (2 ** rng.uniform(-0.02, 0.02))
    click_f = base_f * 4.0 * (2 ** rng.uniform(-0.1, 0.1))
    tactile_f = base_f * (2 ** rng.uniform(-0.08, 0.08))
    housing_f = base_f * 0.5 * (2 ** rng.uniform(-0.06, 0.06))
    thock_f = base_f * 0.25 * (2 ** rng.uniform(-0.10, 0.10))
    sub_f = base_f * 0.12 * (2 ** rng.uniform(-0.05, 0.05))
    spring_f = base_f * 3.5 * (2 ** rng.uniform(-0.08, 0.08))

    voices = [
        _v_click_transient(click_f, 0.50, delay=0.0, rng=rng),
        _v_fm_tactile(tactile_f, rng.uniform(0.3, 0.5), 0.30, int(tactile_f * 4), delay=0.0002, rng=rng),
        _v_housing(housing_f, 0.25, delay=0.0005, rng=rng),
        _v_thock(thock_f, 0.40, delay=0.002, rng=rng),
        _v_sub(sub_f, 0.25, delay=0.003, rng=rng),
        _v_rattle(int(base_f * 2.5), int(base_f * 5), 0.06, delay=0.002),
        _v_spring_ping(spring_f, 0.15, delay=0.005, rng=rng),
    ]
    return DSP.to_int16(R.render(voices, duration, rng))


def _make_mechanical_space(sr=44100, seed=100, row=-1, col=5, char=' '):
    """Spacebar: deeper, wider thock with more sub-bass and rattle."""
    rng = np.random.RandomState(seed)
    R = SoundRenderer(sr)
    base_f = _get_char_freq(char, row, col) * (2 ** rng.uniform(-0.10, 0.10))
    voices = [
        _v_click_transient(base_f * 3.0, 0.35, delay=0.0, rng=rng),
        _v_fm_tactile(base_f, rng.uniform(0.2, 0.4), 0.25, int(base_f * 4), delay=0.0003, rng=rng),
        _v_housing(base_f * 0.5, 0.30, delay=0.0005, rng=rng),
        _v_thock(base_f * 0.22, 0.50, delay=0.002, rng=rng),
        _v_sub(base_f * 0.10, 0.35, delay=0.003, rng=rng),
        _v_rattle(int(base_f * 1.5), int(base_f * 3), 0.05, delay=0.002),
        _v_spring_ping(base_f * 3.0, 0.10, delay=0.006, rng=rng),
    ]
    return DSP.to_int16(R.render(voices, 0.12, rng))


def _make_mechanical_enter(sr=44100, seed=200):
    """Enter key: solid mechanical return with extra weight."""
    rng = np.random.RandomState(seed)
    R = SoundRenderer(sr)
    base_f = 250.0 * (2 ** rng.uniform(-0.10, 0.10))
    voices = [
        _v_click_transient(base_f * 3.0, 0.40, delay=0.0, rng=rng),
        _v_fm_tactile(base_f, rng.uniform(0.2, 0.4), 0.30, int(base_f * 4), delay=0.0003, rng=rng),
        _v_housing(base_f * 0.5, 0.35, delay=0.0005, rng=rng),
        _v_thock(base_f * 0.22, 0.55, delay=0.002, rng=rng),
        _v_sub(base_f * 0.10, 0.40, delay=0.003, rng=rng),
        _v_rattle(int(base_f * 1.2), int(base_f * 2.5), 0.06, delay=0.002),
        _v_spring_ping(base_f * 3.5, 0.12, delay=0.005, rng=rng),
    ]
    return DSP.to_int16(R.render(voices, 0.12, rng))


def _make_red_click(sr=44100, duration=0.10, seed=0, row=2, col=5, char='a'):
    """Cherry MX Red: linear switch — deep thock, no click leaf, smooth travel."""
    rng = np.random.RandomState(seed)
    R = SoundRenderer(sr)
    base_f = _get_char_freq(char, row, col) * (2 ** rng.uniform(-0.05, 0.05))
    thock_f = base_f * 0.35 * (2 ** rng.uniform(-0.08, 0.08))
    housing_f = base_f * 0.55 * (2 ** rng.uniform(-0.06, 0.06))
    sub_f = base_f * 0.15 * (2 ** rng.uniform(-0.05, 0.05))
    voices = [
        # No click leaf — linear switch
        Voice(osc="noise_white", env_type="adsr",
              attack=0.0008, decay=0.003, sustain=0.0, release=0.01,
              attack_curve=2.0, decay_rate=250.0, release_rate=120.0,
              filt="lp", f_cutoff=2500, gain=0.08, delay=0.0),
        _v_thock(thock_f, 0.55, delay=0.001, rng=rng),
        _v_housing(housing_f, 0.35, delay=0.0008, rng=rng),
        _v_sub(sub_f, 0.35, delay=0.002, rng=rng),
        # Very subtle spring sound
        _v_spring_ping(base_f * 3.0, 0.06, delay=0.006, rng=rng),
    ]
    return DSP.to_int16(R.render(voices, duration, rng))


def _make_brown_click(sr=44100, duration=0.10, seed=0, row=2, col=5, char='a'):
    """Cherry MX Brown: tactile bump without the audible click — muted mid-range."""
    rng = np.random.RandomState(seed)
    R = SoundRenderer(sr)
    base_f = _get_char_freq(char, row, col) * (2 ** rng.uniform(-0.05, 0.05))
    tactile_f = base_f * (2 ** rng.uniform(-0.06, 0.06))
    housing_f = base_f * 0.5 * (2 ** rng.uniform(-0.06, 0.06))
    thock_f = base_f * 0.28 * (2 ** rng.uniform(-0.08, 0.08))
    sub_f = base_f * 0.14 * (2 ** rng.uniform(-0.05, 0.05))
    voices = [
        # Muted tactile bump (lower FM index, lower cutoff)
        _v_fm_tactile(tactile_f, rng.uniform(0.2, 0.35), 0.30, int(tactile_f * 3), delay=0.0003, rng=rng),
        _v_housing(housing_f, 0.25, delay=0.0008, rng=rng),
        _v_thock(thock_f, 0.40, delay=0.002, rng=rng),
        _v_sub(sub_f, 0.25, delay=0.003, rng=rng),
        _v_rattle(int(base_f * 2), int(base_f * 4), 0.04, delay=0.002),
    ]
    return DSP.to_int16(R.render(voices, duration, rng))


def _make_ibm_click(sr=44100, duration=0.25, seed=0, row=2, col=5, char='a'):
    """IBM Model M: buckling spring with long metallic ping and membrane snap."""
    rng = np.random.RandomState(seed)
    R = SoundRenderer(sr)
    base_f = _get_char_freq(char, row, col) * (2 ** rng.uniform(-0.05, 0.05))
    spring_f = base_f * 3.5 * (2 ** rng.uniform(-0.08, 0.08))
    membrane_f = base_f * 2.0 * (2 ** rng.uniform(-0.06, 0.06))
    housing_f = base_f * 0.6 * (2 ** rng.uniform(-0.06, 0.06))
    thock_f = base_f * 0.20 * (2 ** rng.uniform(-0.10, 0.10))
    sub_f = base_f * 0.10 * (2 ** rng.uniform(-0.05, 0.05))
    voices = [
        # Buckling spring ping — long FM decay
        Voice(osc="fm", freq=spring_f, fm_ratio=3.5, fm_index=rng.uniform(1.0, 1.5),
              env_type="adsr",
              attack=0.0002, decay=0.01, sustain=0.2, release=0.20,
              attack_curve=1.5, decay_rate=40.0, release_rate=8.0,
              filt="lp", f_cutoff=12000, drive=1.0, gain=0.50, delay=0.0),
        # Membrane snap
        Voice(osc="noise_white", env_type="adsr",
              attack=0.0003, decay=0.005, sustain=0.0, release=0.01,
              attack_curve=2.0, decay_rate=200.0, release_rate=100.0,
              filt="bp", f_cutoff=membrane_f * 0.5, f_high=membrane_f * 1.5,
              drive=1.5, gain=0.30, delay=0.0005),
        _v_housing(housing_f, 0.30, delay=0.001, rng=rng),
        _v_thock(thock_f, 0.45, delay=0.003, rng=rng),
        _v_sub(sub_f, 0.30, delay=0.004, rng=rng),
    ]
    return DSP.to_int16(R.render(voices, duration, rng))


def _make_mx_click(sr=44100, duration=0.06, seed=0, row=2, col=5, char='a'):
    """Logitech MX: scissor switch — shallow, crisp, highly dampened, quick decay."""
    rng = np.random.RandomState(seed)
    R = SoundRenderer(sr)
    base_f = _get_char_freq(char, row, col) * (2 ** rng.uniform(-0.03, 0.03))
    click_f = base_f * 5.0 * (2 ** rng.uniform(-0.05, 0.05))
    thock_f = base_f * 0.4 * (2 ** rng.uniform(-0.05, 0.05))
    housing_f = base_f * 0.7 * (2 ** rng.uniform(-0.04, 0.04))
    voices = [
        # Crisp, short click
        Voice(osc="noise_white", env_type="adsr",
              attack=0.0001, decay=0.001, sustain=0.0, release=0.002,
              attack_curve=3.0, decay_rate=800.0, release_rate=600.0,
              filt="bp", f_cutoff=click_f * 0.7, f_high=click_f * 1.5,
              drive=2.0, gain=0.35, delay=0.0),
        # Shallow thock
        Voice(osc="sine", freq=thock_f, env_type="adsr",
              attack=0.0005, decay=0.003, sustain=0.0, release=0.015,
              attack_curve=2.0, decay_rate=250.0, release_rate=100.0,
              filt="lp", f_cutoff=800, gain=0.40, delay=0.0005),
        # Housing — very short
        Voice(osc="sine", freq=housing_f, env_type="adsr",
              attack=0.0003, decay=0.003, sustain=0.0, release=0.01,
              attack_curve=1.5, decay_rate=200.0, release_rate=100.0,
              filt="lp", f_cutoff=3000, gain=0.20, delay=0.0003),
    ]
    return DSP.to_int16(R.render(voices, duration, rng))


def _make_typewriter_click(sr=44100, duration=0.18, seed=0, row=2, col=5, char='a'):
    """Typewriter: type bar strike with metallic resonance and platen impact."""
    rng = np.random.RandomState(seed)
    R = SoundRenderer(sr)
    base_f = _get_char_freq(char, row, col) * (2 ** rng.uniform(-0.05, 0.05))
    bar_f = base_f * 4.0 * (2 ** rng.uniform(-0.1, 0.1))
    platen_f = base_f * 0.3 * (2 ** rng.uniform(-0.08, 0.08))
    housing_f = base_f * 0.7 * (2 ** rng.uniform(-0.06, 0.06))
    sub_f = base_f * 0.12 * (2 ** rng.uniform(-0.05, 0.05))
    voices = [
        # Type bar metallic strike — FM with long decay
        Voice(osc="fm", freq=bar_f, fm_ratio=3.5, fm_index=rng.uniform(0.8, 1.2),
              env_type="adsr",
              attack=0.0002, decay=0.005, sustain=0.1, release=0.12,
              attack_curve=1.5, decay_rate=60.0, release_rate=12.0,
              filt="lp", f_cutoff=12000, drive=1.0, gain=0.50, delay=0.0),
        # Platen impact (rubber roller)
        Voice(osc="sine", freq=platen_f, env_type="adsr",
              attack=0.001, decay=0.008, sustain=0.0, release=0.04,
              attack_curve=2.5, decay_rate=120.0, release_rate=50.0,
              filt="lp", f_cutoff=500, gain=0.45, delay=0.003),
        _v_housing(housing_f, 0.35, delay=0.001, rng=rng),
        _v_sub(sub_f, 0.25, delay=0.004, rng=rng),
    ]
    return DSP.to_int16(R.render(voices, duration, rng))


def _make_cash_register_click(sr=44100, duration=0.15, seed=0, row=2, col=5, char='a'):
    """Cash Register: mechanical key with drawer mechanism sounds."""
    rng = np.random.RandomState(seed)
    R = SoundRenderer(sr)
    base_f = _get_char_freq(char, row, col) * (2 ** rng.uniform(-0.05, 0.05))
    voices = [
        _v_click_transient(base_f * 3.5, 0.40, delay=0.0, rng=rng),
        _v_thock(base_f * 0.3, 0.35, delay=0.002, rng=rng),
        _v_housing(base_f * 0.6, 0.25, delay=0.001, rng=rng),
        # Drawer mechanism rattle
        Voice(osc="noise_white", env_type="adsr",
              attack=0.001, decay=0.01, sustain=0.0, release=0.03,
              attack_curve=1.5, decay_rate=80.0, release_rate=40.0,
              filt="bp", f_cutoff=800, f_high=2500,
              gain=0.15, delay=0.005),
    ]
    return DSP.to_int16(R.render(voices, duration, rng))


def _make_bubble_pop_click(sr=44100, duration=0.12, seed=0, row=2, col=5, char='a'):
    """Bubble Pop: cavity resonance with pitch sweep and membrane burst."""
    rng = np.random.RandomState(seed)
    R = SoundRenderer(sr)
    base_f = _get_char_freq(char, row, col) * (2 ** rng.uniform(-0.1, 0.1))
    voices = [
        # Membrane rupture — broadband burst
        Voice(osc="noise_white", env_type="adsr",
              attack=0.0001, decay=0.002, sustain=0.0, release=0.008,
              attack_curve=2.0, decay_rate=300.0, release_rate=150.0,
              filt="bp", f_cutoff=base_f * 0.8, f_high=base_f * 2.5,
              gain=0.35, delay=0.0),
        # Cavity resonance — pitch-swept sine
        Voice(osc="sine", freq=base_f * 1.5, env_type="adsr",
              attack=0.0005, decay=0.005, sustain=0.0, release=0.03,
              attack_curve=1.5, decay_rate=100.0, release_rate=60.0,
              filt="lp", f_cutoff=3000, gain=0.35, delay=0.0003),
    ]
    return DSP.to_int16(R.render(voices, duration, rng))


def _make_rain_drop_click(sr=44100, duration=0.10, seed=0, row=2, col=5, char='a'):
    """Rain Drops: water droplet modal synthesis with surface tension resonance."""
    rng = np.random.RandomState(seed)
    R = SoundRenderer(sr)
    base_f = _get_char_freq(char, row, col) * (2 ** rng.uniform(-0.15, 0.15))
    # Droplet modes — inharmonic for water-like character
    modes = [
        (base_f * 1.0, 8.0, 1.0),
        (base_f * 1.8, 12.0, 0.5),
        (base_f * 2.6, 18.0, 0.3),
        (base_f * 3.5, 25.0, 0.15),
    ]
    voices = [
        Voice(osc="modal", modes=modes, inharmonicity=0.4,
              env_type="adsr",
              attack=0.0001, decay=0.005, sustain=0.0, release=0.06,
              attack_curve=1.0, decay_rate=80.0, release_rate=15.0,
              filt="lp", f_cutoff=8000, gain=0.50, delay=0.0),
        # Splash tail
        Voice(osc="noise_white", env_type="adsr",
              attack=0.0003, decay=0.002, sustain=0.0, release=0.02,
              attack_curve=2.0, decay_rate=200.0, release_rate=80.0,
              filt="hp", f_cutoff=2000, gain=0.10, delay=0.001),
    ]
    return DSP.to_int16(R.render(voices, duration, rng))


def _make_membrane_click(sr=44100, duration=0.10, seed=0, row=2, col=5, char='a'):
    """Membrane: rubber dome collapse — muffled, slow attack, low resonance."""
    rng = np.random.RandomState(seed)
    R = SoundRenderer(sr)
    base_f = _get_char_freq(char, row, col) * (2 ** rng.uniform(-0.05, 0.05))
    voices = [
        # Dome collapse — muffled low-frequency tone with slow attack
        Voice(osc="sine", freq=base_f * 0.3, env_type="adsr",
              attack=0.003, decay=0.015, sustain=0.0, release=0.05,
              attack_curve=1.5, decay_rate=60.0, release_rate=25.0,
              filt="lp", f_cutoff=400, gain=0.45, delay=0.0),
        # Muffled body
        Voice(osc="noise_white", env_type="adsr",
              attack=0.002, decay=0.008, sustain=0.0, release=0.03,
              attack_curve=1.5, decay_rate=100.0, release_rate=50.0,
              filt="lp", f_cutoff=1200, gain=0.15, delay=0.001),
        _v_sub(base_f * 0.1, 0.20, delay=0.003, rng=rng),
    ]
    return DSP.to_int16(R.render(voices, duration, rng))


def _make_crystal_click(sr=44100, duration=0.40, seed=0, row=2, col=5, char='a'):
    """Crystal: inharmonic modal bell with stretched partials and long decay."""
    rng = np.random.RandomState(seed)
    R = SoundRenderer(sr)
    base_f = _get_char_freq(char, row, col) * (2 ** rng.uniform(-0.03, 0.03))
    modes = [
        (base_f * 1.0, 2.0, 1.0),
        (base_f * 2.1, 3.0, 0.6),
        (base_f * 3.4, 4.0, 0.4),
        (base_f * 5.2, 5.0, 0.25),
        (base_f * 7.1, 6.0, 0.15),
    ]
    voices = [
        Voice(osc="modal", modes=modes, inharmonicity=0.5,
              env_type="adsr",
              attack=0.0001, decay=0.01, sustain=0.4, release=0.30,
              attack_curve=1.0, decay_rate=20.0, release_rate=4.0,
              filt="lp", f_cutoff=16000, gain=0.50, delay=0.0),
        # Strike transient
        Voice(osc="noise_white", env_type="adsr",
              attack=0.0001, decay=0.001, sustain=0.0, release=0.005,
              attack_curve=3.0, decay_rate=600.0, release_rate=300.0,
              filt="bp", f_cutoff=base_f * 3, f_high=base_f * 8,
              gain=0.15, delay=0.0),
    ]
    return DSP.to_int16(R.render(voices, duration, rng))


def _make_wooden_click(sr=44100, duration=0.18, seed=0, row=2, col=5, char='a'):
    """Wooden: marimba bar with odd-harmonic modes and resonator coupling."""
    rng = np.random.RandomState(seed)
    R = SoundRenderer(sr)
    base_f = _get_char_freq(char, row, col) * (2 ** rng.uniform(-0.05, 0.05))
    # Marimba modes — odd harmonics dominate
    modes = [
        (base_f * 1.0, 6.0, 1.0),
        (base_f * 3.0, 10.0, 0.4),
        (base_f * 5.0, 15.0, 0.2),
        (base_f * 7.0, 20.0, 0.1),
    ]
    voices = [
        Voice(osc="modal", modes=modes, inharmonicity=0.1,
              env_type="adsr",
              attack=0.0005, decay=0.01, sustain=0.2, release=0.12,
              attack_curve=1.5, decay_rate=30.0, release_rate=8.0,
              filt="lp", f_cutoff=6000, gain=0.50, delay=0.0),
        # Wood impact noise
        Voice(osc="noise_white", env_type="adsr",
              attack=0.0002, decay=0.003, sustain=0.0, release=0.01,
              attack_curve=2.0, decay_rate=250.0, release_rate=120.0,
              filt="bp", f_cutoff=base_f * 0.5, f_high=base_f * 2,
              gain=0.15, delay=0.0),
    ]
    return DSP.to_int16(R.render(voices, duration, rng))


def _make_foam_click(sr=44100, duration=0.12, seed=0, row=2, col=5, char='a'):
    """Soft Foam: compressed foam thud — damped, no high frequencies."""
    rng = np.random.RandomState(seed)
    R = SoundRenderer(sr)
    base_f = _get_char_freq(char, row, col) * (2 ** rng.uniform(-0.05, 0.05))
    voices = [
        Voice(osc="sine", freq=base_f * 0.2, env_type="adsr",
              attack=0.004, decay=0.02, sustain=0.0, release=0.06,
              attack_curve=1.5, decay_rate=40.0, release_rate=20.0,
              filt="lp", f_cutoff=250, gain=0.50, delay=0.0),
        Voice(osc="noise_white", env_type="adsr",
              attack=0.003, decay=0.01, sustain=0.0, release=0.03,
              attack_curve=1.5, decay_rate=80.0, release_rate=40.0,
              filt="lp", f_cutoff=500, gain=0.15, delay=0.001),
    ]
    return DSP.to_int16(R.render(voices, duration, rng))


def _make_cat_click(sr=44100, duration=0.10, seed=0, row=2, col=5, char='a'):
    """Cat Paws: soft pad impact — fur-damped transients, gentle low body."""
    rng = np.random.RandomState(seed)
    R = SoundRenderer(sr)
    base_f = _get_char_freq(char, row, col) * (2 ** rng.uniform(-0.05, 0.05))
    voices = [
        Voice(osc="sine", freq=base_f * 0.25, env_type="adsr",
              attack=0.002, decay=0.012, sustain=0.0, release=0.04,
              attack_curve=2.0, decay_rate=70.0, release_rate=30.0,
              filt="lp", f_cutoff=400, gain=0.45, delay=0.0),
        Voice(osc="noise_white", env_type="adsr",
              attack=0.001, decay=0.005, sustain=0.0, release=0.02,
              attack_curve=2.0, decay_rate=150.0, release_rate=70.0,
              filt="lp", f_cutoff=800, gain=0.12, delay=0.0005),
    ]
    return DSP.to_int16(R.render(voices, duration, rng))


def _make_backspace_click(sr=44100, duration=0.08, seed=0,
                          row=2, col=5, char='\b'):
    """Backspace: short, muted click — distinct from character keys."""
    rng = np.random.RandomState(seed)
    R = SoundRenderer(sr)
    voices = [
        # Quick muted broadband click
        Voice(osc="noise_white", env_type="adsr",
              attack=0.0002, decay=0.002, sustain=0.0, release=0.006,
              attack_curve=2.0, decay_rate=400.0, release_rate=200.0,
              filt="bp", f_cutoff=2500, f_high=7000,
              drive=1.5, gain=0.35, delay=0.0),
        # Low-frequency body
        Voice(osc="sine", freq=350, env_type="adsr",
              attack=0.0005, decay=0.003, sustain=0.0, release=0.012,
              attack_curve=2.0, decay_rate=200.0, release_rate=80.0,
              filt="lp", f_cutoff=1800, gain=0.25, delay=0.0),
    ]
    return DSP.to_int16(R.render(voices, duration, rng))


_PRESET_FACTORIES: Dict[str, Dict[str, Callable]] = {
    "Mechanical":     {"click": _make_mechanical_click,  "space": _make_mechanical_space,  "enter": _make_mechanical_enter},
    "Cherry MX Red":  {"click": _make_red_click,         "space": _make_mechanical_space,  "enter": _make_mechanical_enter},
    "Cherry Brown":   {"click": _make_brown_click,       "space": _make_mechanical_space,  "enter": _make_mechanical_enter},
    "IBM Model M":    {"click": _make_ibm_click,         "space": _make_mechanical_space,  "enter": _make_mechanical_enter},
    "Logitech MX":    {"click": _make_mx_click,          "space": _make_mechanical_space,  "enter": _make_mechanical_enter},
    "Typewriter":     {"click": _make_typewriter_click,  "space": _make_mechanical_space,  "enter": _make_mechanical_enter},
    "Cash Register":  {"click": _make_cash_register_click, "space": _make_mechanical_space, "enter": _make_mechanical_enter},
    "Bubble Pop":     {"click": _make_bubble_pop_click,  "space": _make_mechanical_space,  "enter": _make_mechanical_enter},
    "Rain Drops":     {"click": _make_rain_drop_click,   "space": _make_mechanical_space,  "enter": _make_mechanical_enter},
    "Membrane":       {"click": _make_membrane_click,    "space": _make_mechanical_space,  "enter": _make_mechanical_enter},
    "Crystal":        {"click": _make_crystal_click,     "space": _make_mechanical_space,  "enter": _make_mechanical_enter},
    "Wooden":         {"click": _make_wooden_click,      "space": _make_mechanical_space,  "enter": _make_mechanical_enter},
    "Soft Foam":      {"click": _make_foam_click,        "space": _make_mechanical_space,  "enter": _make_mechanical_enter},
    "Cat Paws":       {"click": _make_cat_click,         "space": _make_mechanical_space,  "enter": _make_mechanical_enter},
}


class SimpleSoundGen:
    _THUMB_CHARS = frozenset(" \t")

    def __init__(self, sr: int = 44100, preset: str = "Mechanical",
                 stereo: bool = False, reverb_amt: float = 0.1):
        self.sr = sr
        self.preset = preset
        self.stereo = stereo
        self.reverb_amt = reverb_amt
        self._rng = random.Random(98765)
        factories = _PRESET_FACTORIES.get(preset, _PRESET_FACTORIES["Mechanical"])
        click_dur = CLICK_DURATIONS.get(preset, 0.06)

        self.char_sounds = {}
        for i, char in enumerate(string.printable):
            if char in string.whitespace and char not in ' \t':
                continue
            if char == ' ':
                # --- FIXED: use the preset's click factory so space matches the preset ---
                self.spaces = []
                for j in range(16):
                    snd = factories["click"](
                        sr, duration=click_dur * 1.3,
                        seed=100 + j, row=-1, col=5, char=' ',
                    )
                    if self.reverb_amt > 0:
                        snd = _apply_asmr_tail(snd, sr, 100 + j, vol=self.reverb_amt)
                    self.spaces.append(snd)
                continue
            if char == '\t':
                row, col = 1, 5
            else:
                row, col = _get_char_rc(char)
            seed_val = ord(char) * 13 + i
            snd = factories["click"](
                sr, duration=click_dur, seed=seed_val,
                row=row, col=col, char=char,
            )
            if self.reverb_amt > 0:
                snd = _apply_asmr_tail(snd, sr, seed_val, vol=self.reverb_amt)
            self.char_sounds[char] = snd

        # --- FIXED: use the preset's click factory so enter matches the preset ---
        self.enters = []
        for j in range(16):
            snd = factories["click"](
                sr, duration=click_dur * 1.5,
                seed=200 + j, row=3, col=5, char='\n',
            )
            if self.reverb_amt > 0:
                snd = _apply_asmr_tail(snd, sr, 200 + j, vol=self.reverb_amt)
            self.enters.append(snd)

        # --- NEW: dedicated backspace sounds ---
        self.backspaces = []
        for j in range(16):
            snd = _make_backspace_click(sr, seed=300 + j)
            if self.reverb_amt > 0:
                snd = _apply_asmr_tail(snd, sr, 300 + j, vol=self.reverb_amt)
            self.backspaces.append(snd)

    def _pick(self, char: str, rng: random.Random) -> Tuple[np.ndarray, float, float]:
        if char == "\n":
            snd = rng.choice(self.enters)
            vol_mod = rng.uniform(1.05, 1.20)
            pan = 0.2
        elif char == "\b":
            # --- FIXED: use dedicated backspace sound instead of random char ---
            snd = rng.choice(self.backspaces)
            vol_mod = rng.uniform(0.85, 1.00)
            pan = 0.0
        elif char == " ":
            snd = rng.choice(self.spaces)
            vol_mod = rng.uniform(1.00, 1.15)
            pan = 0.0
        elif char in self.char_sounds:
            snd = self.char_sounds[char]
            row, col = _get_char_rc(char)
            if col == 0 or col >= 9:
                vol_mod = rng.uniform(0.85, 1.05)
            else:
                vol_mod = rng.uniform(0.95, 1.10)
            pan = max(-0.5, min(0.5, (col - 6) * 0.08))
        else:
            # --- FIXED: unknown chars produce silence instead of random sound ---
            snd = np.zeros(100, dtype=np.int16)
            vol_mod = 0.0
            pan = 0.0

        # --- FIXED: increased pitch variation from ±0.02 to ±0.15 semitones ---
        shift = rng.gauss(0, 0.15)
        if abs(shift) > 0.04:
            snd = self._pitch_shift(snd, shift)
        return snd, vol_mod, pan

    def generate_track(self, timestamps: List[Tuple[float, str]], filepath: str,
                       volume: float = 0.5) -> None:
        if not timestamps: return
        pcm = self.generate_pcm(timestamps, volume)
        if len(pcm) == 0: return
        channels = 2 if self.stereo else 1
        with wave.open(filepath, "w") as wf:
            wf.setnchannels(channels)
            wf.setsampwidth(2)
            wf.setframerate(self.sr)
            wf.writeframes(pcm.tobytes())

    def generate_pcm(self, timestamps: List[Tuple[float, str]],
                     volume: float = 0.5) -> np.ndarray:
        if not timestamps:
            return np.zeros(0, dtype=np.int16)
        sr = self.sr
        total = max(ts for ts, _ in timestamps) + 0.3
        n = int(sr * total)
        rng = self._rng
        raw_sounds: List[np.ndarray] = []
        starts_i: List[int] = []
        pans: List[float] = []
        for ts, ch in timestamps:
            snd, vol_mod, pan = self._pick(ch, rng)
            s = int(ts * sr)
            e = min(s + len(snd), n)
            if s < n:
                vol_var = rng.gauss(1.0, 0.05) * vol_mod
                raw_sounds.append(snd[:e - s].astype(np.float32) * volume * vol_var)
                starts_i.append(s)
                if self.stereo:
                    pans.append(pan)
        if not raw_sounds:
            return np.zeros(n, dtype=np.int16)
        if self.stereo:
            return self._mix_stereo(n, raw_sounds, starts_i, pans)
        starts      = np.array(starts_i, dtype=np.int64)
        lengths     = np.array([len(s) for s in raw_sounds], dtype=np.int64)
        sounds_flat = np.concatenate(raw_sounds)
        offsets     = np.zeros(len(raw_sounds), dtype=np.int64)
        for i in range(1, len(raw_sounds)):
            offsets[i] = offsets[i - 1] + lengths[i - 1]
        del raw_sounds, starts_i
        mix = self._mix_sounds(n, starts, lengths, offsets, sounds_flat)

        # --- FIXED: peak detection (chunked if numba available) ---
        if _HAS_NUMBA:
            CHUNK = 10 * sr
            chunk_peaks = _nb_chunked_peak(mix, CHUNK)
            peak = float(np.max(chunk_peaks)) if len(chunk_peaks) > 0 else 0.0
        else:
            peak = float(np.max(np.abs(mix))) if len(mix) > 0 else 0.0

        # --- FIXED: only normalize DOWN when peak exceeds target;
        #     don't amplify quiet passages (preserves natural dynamics) ---
        target = 32767.0 * 10 ** (-1.5 / 20)  # ≈ -1.5 dB
        if peak > target:
            norm = np.float32(target / peak)
        else:
            norm = np.float32(1.0)

        # Apply gain
        mix = mix * norm

        # --- NEW: soft saturation (tanh) prevents harsh digital clipping ---
        # Linear for small values; gently compresses peaks above ~0.7 full-scale
        mix_f = mix / 32767.0
        mix_f = np.tanh(mix_f * 1.2) / np.tanh(1.2)
        return (mix_f * 32767.0).astype(np.int16)

    @staticmethod
    def _pitch_shift(sound: np.ndarray, semitones: float) -> np.ndarray:
        factor = 2 ** (semitones / 12)
        n_orig = len(sound)
        n_new = max(1, int(n_orig / factor))
        if n_new == n_orig or n_orig < 8:
            return sound
        if factor < 1.0:
            cutoff = min(20000, 44100 * factor * 0.45)
            sound_f = sound.astype(np.float64) / 32767.0
            sound_f = DSP.filt_lp(sound_f, cutoff, 44100, n_taps=63)
            sound = (sound_f * 32767).astype(np.int16)
        indices = np.linspace(0, n_orig - 1, n_new)
        i0 = indices.astype(np.int32)
        frac = indices - i0
        i1 = np.minimum(i0 + 1, n_orig - 1)
        i2 = np.minimum(i0 + 2, n_orig - 1)
        im1 = np.maximum(i0 - 1, 0)
        s = sound.astype(np.float64)
        shifted = 0.5 * (
            s[im1] * (-frac**3 + 2*frac**2 - frac) +
            s[i0]  * (3*frac**3 - 5*frac**2 + 2) +
            s[i1]  * (-3*frac**3 + 4*frac**2 + frac) +
            s[i2]  * (frac**3 - frac**2)
        )
        return shifted.astype(np.int16)

    def _mix_sounds(self, n: int, starts: np.ndarray, lengths: np.ndarray,
                    offsets: np.ndarray, sounds_flat: np.ndarray) -> np.ndarray:
        mix = np.zeros(n, dtype=np.float32)
        if _HAS_NUMBA:
            _nb_mix_sounds(mix, sounds_flat, offsets, lengths, starts)
        else:
            for i in range(len(starts)):
                s = int(starts[i]); ln = int(lengths[i]); o = int(offsets[i])
                mix[s:s + ln] += sounds_flat[o:o + ln]
        return mix

    def _mix_stereo(self, n: int, raw_sounds: List[np.ndarray],
                    starts_i: List[int], pans: List[float]) -> np.ndarray:
        mix_l = np.zeros(n, dtype=np.float32)
        mix_r = np.zeros(n, dtype=np.float32)
        for i, snd in enumerate(raw_sounds):
            s = starts_i[i]; ln = len(snd); pan = pans[i]
            lg = np.cos((pan + 1.0) * np.pi / 4.0)
            rg = np.sin((pan + 1.0) * np.pi / 4.0)
            e = min(s + ln, n)
            mix_l[s:e] += snd[:e - s] * lg
            mix_r[s:e] += snd[:e - s] * rg
        peak_l = float(np.max(np.abs(mix_l))) if len(mix_l) > 0 else 0.0
        peak_r = float(np.max(np.abs(mix_r))) if len(mix_r) > 0 else 0.0
        peak = max(peak_l, peak_r)

        # --- FIXED: only normalize down, don't amplify quiet passages ---
        target = 32767.0 * 10 ** (-1.5 / 20)
        if peak > target:
            norm = np.float32(target / peak)
        else:
            norm = np.float32(1.0)

        mix_l = mix_l * norm
        mix_r = mix_r * norm

        # --- NEW: soft saturation ---
        mix_lf = mix_l / 32767.0
        mix_rf = mix_r / 32767.0
        mix_lf = np.tanh(mix_lf * 1.2) / np.tanh(1.2)
        mix_rf = np.tanh(mix_rf * 1.2) / np.tanh(1.2)
        out_l = (mix_lf * 32767.0).astype(np.int16)
        out_r = (mix_rf * 32767.0).astype(np.int16)

        stereo_out = np.empty(n * 2, dtype=np.int16)
        stereo_out[0::2] = out_l
        stereo_out[1::2] = out_r
        return stereo_out


def _pcm_to_wav_bytes(pcm: np.ndarray, sr: int = 44100, channels: int = 1) -> bytes:
    buf = io.BytesIO()
    with wave.open(buf, "w") as wf:
        wf.setnchannels(channels)
        wf.setsampwidth(2)
        wf.setframerate(sr)
        wf.writeframes(pcm.tobytes())
    return buf.getvalue()


# =====================================================================
# 6. KEYBOARD OVERLAY & RENDERER
# =====================================================================

KEYBOARD_LAYOUTS: Dict[str, dict] = {
    "QWERTY": {
        "description": "Standard US QWERTY layout with full modifier row",
        "rows": [
            [("`",1),("1",1),("2",1),("3",1),("4",1),("5",1),("6",1),("7",1),
             ("8",1),("9",1),("0",1),("-",1),("=",1),("Bksp",2)],
            [("Tab",1.5),("Q",1),("W",1),("E",1),("R",1),("T",1),("Y",1),("U",1),
             ("I",1),("O",1),("P",1),("[",1),("]",1),("\\",1.5)],
            [("Caps",1.75),("A",1),("S",1),("D",1),("F",1),("G",1),("H",1),("J",1),
             ("K",1),("L",1),(";",1),("'",1),("Enter",2.25)],
            [("Shift",2.25),("Z",1),("X",1),("C",1),("V",1),("B",1),("N",1),("M",1),
             (",",1),(".",1),("/",1),("Shift",2.75)],
            [("Ctrl",1.25),("Win",1.25),("Alt",1.25),(" ",6.25),
             ("Alt",1.25),("Win",1.25),("Menu",1.25),("Ctrl",1.25)],
        ],
    },
    "AZERTY": {
        "description": "French AZERTY layout",
        "rows": [
            [("²",1),("&",1),("é",1),("\"",1),("'",1),("(",1),("-",1),("è",1),
             ("_",1),("ç",1),("à",1),(")",1),("=",1),("Bksp",2)],
            [("Tab",1.5),("A",1),("Z",1),("E",1),("R",1),("T",1),("Y",1),("U",1),
             ("I",1),("O",1),("P",1),("^",1),("$",1),("Enter",1.5)],
            [("Caps",1.75),("Q",1),("S",1),("D",1),("F",1),("G",1),("H",1),("J",1),
             ("K",1),("L",1),("M",1),("ù",1),("*",1),("Enter",2.25)],
            [("Shift",1.25),("<",1),("W",1),("X",1),("C",1),("V",1),("B",1),("N",1),
             (",",1),(";",1),(":",1),("!",1),("Shift",2.75)],
            [("Ctrl",1.25),("Win",1.25),("Alt",1.25),(" ",6.25),
             ("Alt",1.25),("Win",1.25),("Menu",1.25),("Ctrl",1.25)],
        ],
    },
    "QWERTZ": {
        "description": "German QWERTZ layout",
        "rows": [
            [("^",1),("1",1),("2",1),("3",1),("4",1),("5",1),("6",1),("7",1),
             ("8",1),("9",1),("0",1),("ß",1),("´",1),("Bksp",2)],
            [("Tab",1.5),("Q",1),("W",1),("E",1),("R",1),("T",1),("Z",1),("U",1),
             ("I",1),("O",1),("P",1),("Ü",1),("+",1),("Enter",1.5)],
            [("Caps",1.75),("A",1),("S",1),("D",1),("F",1),("G",1),("H",1),("J",1),
             ("K",1),("L",1),("Ö",1),("Ä",1),("#",1),("Enter",2.25)],
            [("Shift",1.25),("<",1),("Y",1),("X",1),("C",1),("V",1),("B",1),("N",1),
             (",",1),(".",1),("-",1),("Shift",2.75)],
            [("Ctrl",1.25),("Win",1.25),("Alt",1.25),(" ",6.25),
             ("Alt",1.25),("Win",1.25),("Menu",1.25),("Ctrl",1.25)],
        ],
    },
    "Dvorak": {
        "description": "Dvorak Simplified Keyboard (optimized for English)",
        "rows": [
            [("`",1),("1",1),("2",1),("3",1),("4",1),("5",1),("6",1),("7",1),
             ("8",1),("9",1),("0",1),("[",1),("]",1),("Bksp",2)],
            [("Tab",1.5),("'",1),(",",1),(".",1),("P",1),("Y",1),("F",1),("G",1),
             ("C",1),("R",1),("L",1),("/",1),("=",1),("\\",1.5)],
            [("Caps",1.75),("A",1),("O",1),("E",1),("U",1),("I",1),("D",1),("H",1),
             ("T",1),("N",1),("S",1),("-",1),("Enter",2.25)],
            [("Shift",2.25),(";",1),("Q",1),("J",1),("K",1),("X",1),("B",1),("M",1),
             ("W",1),("V",1),("Z",1),("Shift",2.75)],
            [("Ctrl",1.25),("Win",1.25),("Alt",1.25),(" ",6.25),
             ("Alt",1.25),("Win",1.25),("Menu",1.25),("Ctrl",1.25)],
        ],
    },
    "Compact (60%)": {
        "description": "60% mechanical keyboard without function/nav/numpad",
        "rows": [
            [("`",1),("1",1),("2",1),("3",1),("4",1),("5",1),("6",1),("7",1),
             ("8",1),("9",1),("0",1),("-",1),("=",1),("Bksp",2)],
            [("Tab",1.5),("Q",1),("W",1),("E",1),("R",1),("T",1),("Y",1),("U",1),
             ("I",1),("O",1),("P",1),("[",1),("]",1),("\\",1.5)],
            [("Caps",1.75),("A",1),("S",1),("D",1),("F",1),("G",1),("H",1),("J",1),
             ("K",1),("L",1),(";",1),("'",1),("Enter",2.25)],
            [("Shift",2.25),("Z",1),("X",1),("C",1),("V",1),("B",1),("N",1),("M",1),
             (",",1),(".",1),("/",1),("Shift",2.75)],
            [("Ctrl",1.25),("Win",1.25),("Alt",1.25),(" ",6.25),
             ("Alt",1.25),("Fn",1.25),("Menu",1.25),("Ctrl",1.25)],
        ],
    },
}

_US_SHIFT_PAIRS: Dict[str, str] = {
    "`": "~", "1": "!", "2": "@", "3": "#", "4": "$", "5": "%", "6": "^",
    "7": "&", "8": "*", "9": "(", "0": ")",
    "-": "_", "=": "+", "[": "{", "]": "}", "\\": "|",
    ";": ":", "'": "\"", ",": "<", ".": ">", "/": "?",
}

_MOD_LABEL_TO_CHAR: Dict[str, str] = {
    "Tab": "\t", "Enter": "\n", "Bksp": "\b", " ": " ",
}


def _build_char_map(layout_name: str) -> Dict[str, Tuple[int, int]]:
    """Build a {char: (row, col)} map for a given keyboard layout."""
    layout = KEYBOARD_LAYOUTS.get(layout_name, KEYBOARD_LAYOUTS["QWERTY"])
    char_map: Dict[str, Tuple[int, int]] = {}

    for ri, row in enumerate(layout["rows"]):
        for ci, (label, _w) in enumerate(row):
            if not label:
                continue

            if label in _MOD_LABEL_TO_CHAR:
                char_map[_MOD_LABEL_TO_CHAR[label]] = (ri, ci)
                continue

            if len(label) == 1:
                char_map[label] = (ri, ci)
                lower = label.lower()
                if lower != label:
                    char_map[lower] = (ri, ci)
                if lower in _US_SHIFT_PAIRS:
                    char_map[_US_SHIFT_PAIRS[lower]] = (ri, ci)

    return char_map


class TypingAnimator:
    def __init__(self, text: str, wpm: int = 100, start_pause: float = 0.5,
                 end_pause: float = 1.5, typo_rate: float = 0.0):
        self.text = text
        self.wpm = wpm
        self.start_pause = start_pause
        self.end_pause = end_pause
        self.typo_rate = typo_rate
        seed = sum(ord(c) for c in text)
        self._rng = random.Random(seed)
        
        self.display_chars: List[str] = []
        self._timestamps: List[float] = []
        self.timeline: List[Tuple[float, str]] = []
        
        self._build_timeline()

    def _build_timeline(self):
        t = self.start_pause
        base_interval = 60.0 / max(1, self.wpm) / 5.0
        
        for char in self.text:
            if char != '\n' and char != ' ' and self._rng.random() < self.typo_rate:
                typo_char = self._rng.choice(string.ascii_letters + string.digits)
                self.timeline.append((t, typo_char))
                self.display_chars.append(typo_char)
                self._timestamps.append(t)
                t += base_interval * self._rng.uniform(0.5, 1.0)
                
                self.timeline.append((t, '\b'))
                self.display_chars.append('\b')
                self._timestamps.append(t)
                t += base_interval * self._rng.uniform(0.5, 1.0)
            
            self.timeline.append((t, char))
            self.display_chars.append(char)
            self._timestamps.append(t)
            
            if char in ".!?":
                t += base_interval * self._rng.uniform(4.0, 6.0)
            elif char in ",;:":
                t += base_interval * self._rng.uniform(2.0, 3.5)
            elif char == '\n':
                t += base_interval * self._rng.uniform(3.0, 5.0)
            elif char == ' ':
                t += base_interval * self._rng.uniform(1.2, 1.8)
            else:
                t += base_interval * self._rng.uniform(0.7, 1.3)
                
        self._duration = t + self.end_pause

    def duration(self) -> float:
        return self._duration

    def visible_at(self, t: float) -> int:
        if t <= 0: return 0
        return bisect.bisect_right(self._timestamps, t)

    def active_key_at(self, t: float) -> Tuple[Optional[str], float]:
        if not self.timeline or t < self.timeline[0][0]:
            return None, 0.0
        
        idx = bisect.bisect_right(self._timestamps, t)
        if idx == 0:
            return None, 0.0
            
        last_ts, last_char = self.timeline[idx - 1]
        elapsed = t - last_ts
        
        # Flash duration based on the actual time until the next keystroke,
        # clamped to a visible range (≥2 frames at 30fps, ≤0.18s)
        if idx < len(self._timestamps):
            next_ts = self._timestamps[idx]
            interval = next_ts - last_ts
            flash_dur = max(0.06, min(0.18, interval * 0.65))
        else:
            flash_dur = 0.15
        
        if elapsed < flash_dur:
            # Smooth ease-out decay (starts fast, ends gentle)
            progress = elapsed / flash_dur
            flash = max(0.0, (1.0 - progress) ** 1.5)
            return last_char, flash
        return None, 0.0

    def char_timestamps(self) -> List[Tuple[float, str]]:
        return self.timeline

    @staticmethod
    def find_wpm_for_target_duration(text: str, target_dur: float, start_pause: float, 
                                     end_pause: float, typo_rate: float) -> int:
        available_time = target_dur - start_pause - end_pause
        if available_time <= 0 or not text:
            return 300
        
        base_interval = available_time / max(1, len(text) * 1.2)
        wpm = int(60.0 / max(0.01, base_interval) / 5.0)
        return max(30, min(300, wpm))


class KeyboardOverlay:
    def __init__(self, video_w: int, video_h: int, layout_name: str = "QWERTY",
                 theme: Optional[Dict[str, str]] = None, opacity: float = 0.82,
                 max_height: Optional[int] = None, position: str = "bottom_center"):
        self.video_w = video_w
        self.video_h = video_h
        self.layout_name = layout_name
        self.theme = theme
        self.opacity = opacity
        self.rows = KEYBOARD_LAYOUTS[layout_name]["rows"]
        self.char_map = _build_char_map(layout_name)
        self.num_rows = len(self.rows)
        self.position = position
        self.key_unit = max(20, int(video_w * 0.028))
        self.key_gap  = max(2, self.key_unit // 14)
        self.key_h    = int(self.key_unit * 0.82)
        if max_height is not None and max_height > 0:
            natural_h = self.num_rows * self.key_h + (self.num_rows - 1) * self.key_gap
            if natural_h > max_height:
                lo, hi = 10, self.key_unit
                for _ in range(30):
                    mid = (lo + hi) / 2
                    test_gap = max(2, int(mid) // 14)
                    test_h = self.num_rows * int(mid * 0.82) + (self.num_rows - 1) * test_gap
                    if test_h > max_height:
                        hi = mid
                    else:
                        lo = mid
                self.key_unit = max(10, int(lo))
                self.key_gap  = max(2, self.key_unit // 14)
                self.key_h    = int(self.key_unit * 0.82)
        
        # Accurately compute max width based on the widest row
        self._max_units = max(sum(w for _, w in row) for row in self.rows)
        self._kb_width = max(
            int(sum(w for _, w in row) * self.key_unit) + (len(row) - 1) * self.key_gap
            for row in self.rows
        )
        self._kb_height = int(len(self.rows) * self.key_h + (len(self.rows) - 1) * self.key_gap)
        self._kb_x = (video_w - self._kb_width) // 2
        self._kb_y = video_h - self._kb_height - max(8, video_h // 60)
        self._apply_position()
        self.key_rects: Dict[Tuple[int, int], QRect] = {}
        self._rebuild_key_rects()

    def height_needed(self) -> int:
        return self._kb_height + max(8, self.video_h // 60) + max(6, self.video_h // 90)

    def _apply_position(self):
        margin = max(8, self.video_h // 60)
        vw, vh, kw, kh = self.video_w, self.video_h, self._kb_width, self._kb_height
        if self.position == "bottom_center":
            self._kb_x = (vw - kw) // 2; self._kb_y = vh - kh - margin
        elif self.position == "bottom_right":
            self._kb_x = vw - kw - margin; self._kb_y = vh - kh - margin
        elif self.position == "bottom_left":
            self._kb_x = margin; self._kb_y = vh - kh - margin
        elif self.position == "top_center":
            self._kb_x = (vw - kw) // 2; self._kb_y = margin
        elif self.position == "top_right":
            self._kb_x = vw - kw - margin; self._kb_y = margin
        elif self.position == "top_left":
            self._kb_x = margin; self._kb_y = margin
        elif self.position == "center_left":
            self._kb_x = margin; self._kb_y = (vh - kh) // 2
        elif self.position == "center_right":
            self._kb_x = vw - kw - margin; self._kb_y = (vh - kh) // 2

    def _rebuild_key_rects(self):
        self.key_rects: Dict[Tuple[int, int], QRect] = {}
        for ri, row in enumerate(self.rows):
            x = self._kb_x
            for ci, (_label, w) in enumerate(row):
                kw = int(w * self.key_unit) - self.key_gap
                y = self._kb_y + ri * (self.key_h + self.key_gap)
                self.key_rects[(ri, ci)] = QRect(x, y, kw, self.key_h)
                x += int(w * self.key_unit)

    def set_position(self, position: str):
        self.position = position
        self._apply_position()
        self._rebuild_key_rects()

    def reposition(self, y_below: int):
        # Use standard positioning for top/center, 
        # but for bottom, pin it exactly below the text area to prevent overlap
        self._apply_position()
        if self.position.startswith("bottom"):
            self._kb_y = y_below
        self._rebuild_key_rects()

    def resolve_key(self, ch: str) -> Optional[Tuple[int, int]]:
        return self.char_map.get(ch)

    def draw(self, painter: QPainter, active_key: Optional[Tuple[int, int]] = None, flash: float = 0.0):
        painter.save()
        painter.setOpacity(self.opacity)
        painter.setRenderHint(QPainter.Antialiasing)
        th = self.theme or THEMES["Dracula"]
        radius = max(3, self.key_unit // 8)
        bg = QColor(th["background"])
        painter.setPen(QPen(QColor(th["window_border"]), max(1, self.key_unit // 20)))
        painter.setBrush(bg)
        pad = max(6, self.key_unit // 4)
        painter.drawRoundedRect(self._kb_x - pad, self._kb_y - pad,
                                self._kb_width + 2 * pad, self._kb_height + 2 * pad,
                                radius * 2, radius * 2)
        key_bg    = QColor(th["title_bar"])
        key_border = QColor(th["window_border"])
        label_color = QColor(th["foreground"])
        mod_color   = QColor(th["line_number"])
        try:
            hl_base = QColor(th["cursor"])
        except Exception:
            hl_base = QColor("#89b4fa")
        if flash > 0 and active_key is not None:
            hl_key_fill = QColor(
                int(key_bg.red()   + (hl_base.red()   - key_bg.red())   * flash),
                int(key_bg.green() + (hl_base.green() - key_bg.green()) * flash),
                int(key_bg.blue()  + (hl_base.blue()  - key_bg.blue())  * flash),
            )
            hl_glow = QColor(hl_base)
            hl_glow.setAlpha(int(60 * flash))
            hl_expand = max(3, int(self.key_unit * 0.12 * flash))
        else:
            hl_key_fill = None
        for (ri, ci), rect in self.key_rects.items():
            label = self.rows[ri][ci][0]
            is_active = (active_key is not None and active_key == (ri, ci))
            if is_active and hl_key_fill is not None:
                painter.setPen(Qt.PenStyle.NoPen)
                painter.setBrush(hl_glow)
                painter.drawRoundedRect(rect.adjusted(-hl_expand, -hl_expand, hl_expand, hl_expand), radius, radius)
                painter.setBrush(hl_key_fill)
            else:
                painter.setBrush(key_bg)
            painter.setPen(key_border)
            painter.drawRoundedRect(rect, radius, radius)
            if label:
                is_mod = len(label) > 1 or label in {
                    "²", "^", "¨", "´", "ß", "Ü", "Ö", "Ä", "€", "ù",
                    "é", "è", "ç", "à", "æ", "Ğ", "Ş", "İ", "Ö", "Ç",
                    "¥", "@", "_", ":", "*", ";", "<", ">",
                    "半", "無", "変", "中",
                }
                painter.setPen(mod_color if is_mod else label_color)
                fsize = max(7, int(self.key_unit * 0.30))
                painter.setFont(QFont("Segoe UI", fsize))
                if label == "":
                    pass
                else:
                    painter.drawText(rect, Qt.AlignCenter, label)
        painter.restore()


class TextRenderer:
    TOKEN_COLOR_MAP = {
        "keyword": "keyword", "builtin": "builtin", "string": "string",
        "number": "number", "comment": "comment", "decorator": "decorator",
        "function": "function", "class_name": "class_name",
        "operator": "operator", "bracket": "builtin",
    }
    CURSOR_BLINK = 0.53

    def __init__(self, width: int, height: int, theme_name: str = "Dracula",
                 font_family: str = "Consolas", font_size: int = 22,
                 show_line_numbers: bool = True, show_window_chrome: bool = True,
                 padding: int = 24, tab_size: int = 4, title_text: str = "document.txt",
                 language: str = "Text", keyboard_overlay: Optional["KeyboardOverlay"] = None,
                 bg_image_path: Optional[str] = None, total_lines: int = 0,
                 cursor_glow: bool = True, show_watermark: bool = False):
        self.width = width
        self.height = height
        self.theme = THEMES.get(theme_name, THEMES["Dracula"])
        self.font_family = font_family
        self.font_size = font_size
        self.show_line_numbers = show_line_numbers
        self.show_window_chrome = show_window_chrome
        self.padding = padding
        self.tab_size = tab_size
        self.title_text = title_text
        self.language = language
        self.keyboard_overlay = keyboard_overlay
        self.total_lines = total_lines
        self.cursor_glow = cursor_glow
        self.show_watermark = show_watermark

        _MONO_FALLBACKS = ["Consolas", "JetBrains Mono", "DejaVu Sans Mono",
                           "Liberation Mono", "Courier New", "monospace"]
        _families_to_try = [font_family] + [f for f in _MONO_FALLBACKS if f != font_family]
        _available = QFontDatabase.families()
        chosen = "monospace"
        for family in _families_to_try:
            if family in _available:
                chosen = family
                break

        _emoji_fallbacks = [
            "Noto Color Emoji", "Apple Color Emoji", "Segoe UI Emoji",
            "Twemoji Mozilla", "Android Emoji",
        ]
        _font_families = [chosen]
        for ef in _emoji_fallbacks:
            if ef in _available and ef != chosen:
                _font_families.append(ef)
        if "sans-serif" not in _font_families:
            _font_families.append("sans-serif")

        self.font = QFont(chosen, font_size)
        self.font.setFamilies(_font_families)
        self.font.setFixedPitch(True)
        self.fm = QFontMetrics(self.font)
        self.char_w = self.fm.horizontalAdvance("M")
        self.line_h = self.fm.height()

        self._qcolors: Dict[str, QColor] = {}
        for key, val in self.theme.items():
            if isinstance(val, str) and val.startswith("#"):
                self._qcolors[key] = QColor(val)
        self._qc_fg = self._qcolors.get("foreground", QColor("#f8f8f2"))
        self._qc_ln = self._qcolors.get("line_number", QColor("#6272a4"))
        self._qc_ln_active = QColor(self._qc_fg).darker(120)
        self._qc_cursor = self._qcolors.get("cursor", QColor("#f8f8f2"))
        self._qc_current_line = self._qcolors.get("current_line", QColor("#44475a"))

        self.bg_image: Optional[QPixmap] = None
        if bg_image_path and os.path.exists(bg_image_path):
            self.bg_image = QPixmap(bg_image_path)

        self._build_bg_cache()
        self._cached_display_chars_id: int = 0
        self._cached_display_chars_len: int = 0
        self._cached_resolved: str = ""
        self._cached_resolved_colors: List[str] = []
        self._cached_is_clean: List[bool] = []
        self._cached_stack_len: List[int] = []
        self._cached_resolved_color_qc: List[QColor] = []

        self._dirty_num_visible: int = -1
        self._dirty_vis_color_qc: List[QColor] = []
        self._dirty_visible_text: str = ""

        self._layout_nv: int = -1
        self._layout_lines: List[str] = []
        self._layout_offsets: List[int] = []
        self._layout_cursor_line: int = 0

        self._LINE_CACHE_MAX = 512
        self._line_layout_cache: "OrderedDict[str, List[int]]" = OrderedDict()
        self._tab_advance = self.char_w * self.tab_size

    def _build_bg_cache(self):
        self._bg = QImage(self.width, self.height, QImage.Format_RGB32)
        self._bg.fill(QColor(self.theme["background"]))
        
        with painter_context(self._bg) as p:
            p.setRenderHint(QPainter.Antialiasing)
            p.save()
            self._draw_bg(p)
            p.restore()

            w, h = self.width, self.height
            pad = self.padding
            chrome_h = 42 if self.show_window_chrome else 0

            # Properly reserve space for keyboard based on position
            kb_reserve_top = 0
            kb_reserve_bottom = 0
            if self.keyboard_overlay:
                self.keyboard_overlay._apply_position()
                kb_h_needed = self.keyboard_overlay.height_needed()
                available_v = h - 2 * pad
                kb_budget = available_v // 3
                kb_h_needed = min(kb_h_needed, kb_budget)
                
                pos = self.keyboard_overlay.position
                if pos.startswith("top"):
                    kb_reserve_top = kb_h_needed
                elif pos.startswith("bottom"):
                    kb_reserve_bottom = kb_h_needed

            wx = pad
            wy = pad + kb_reserve_top
            ww = w - 2 * pad
            wh = h - 2 * pad - kb_reserve_top - kb_reserve_bottom

            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(QColor(0, 0, 0, 60))
            p.drawRoundedRect(wx + 4, wy + 4, ww, wh, 12, 12)
            p.setPen(QColor(self.theme["window_border"]))
            p.setBrush(QColor(self.theme["background"]))
            r = 12
            p.drawRoundedRect(wx, wy, ww, wh, r, r)

            if self.show_window_chrome:
                p.setPen(Qt.PenStyle.NoPen)
                p.setBrush(QColor(self.theme["title_bar"]))
                p.drawRoundedRect(wx, wy, ww, chrome_h, r, r)
                p.drawRect(wx, wy + chrome_h - r, ww, r)

                btn_r = 7
                btn_y = wy + 19
                glyphs = {"button_close": "×", "button_min": "−", "button_max": "+"}
                glyph_colors = ["#ff5f56", "#ffbd2e", "#27c93f"]
                glyph_shadow = QColor(0, 0, 0, 100)
                glyph_font = QFont("Arial", 7, QFont.Weight.Bold)
                for i, color in enumerate(glyph_colors):
                    cx = wx + 20 + i * 24
                    p.setBrush(QColor(color))
                    p.setPen(Qt.PenStyle.NoPen)
                    p.drawEllipse(QPoint(cx, btn_y), btn_r, btn_r)
                    p.setPen(glyph_shadow)
                    p.setFont(glyph_font)
                    p.drawText(
                        QRect(cx - btn_r, btn_y - btn_r, btn_r * 2, btn_r * 2),
                        Qt.AlignmentFlag.AlignCenter,
                        glyphs[["button_close", "button_min", "button_max"][i]],
                    )

                p.setPen(QColor(self.theme["title_text"]))
                p.setFont(QFont(self.font_family, 12))
                p.drawText(QRect(wx, wy, ww, chrome_h), Qt.AlignCenter, self.title_text)
                text_top = wy + chrome_h
            else:
                text_top = wy

            self._text_rect = QRect(wx + 4, text_top, ww - 8, wh - (text_top - wy))

            if self.keyboard_overlay:
                self.keyboard_overlay.reposition(wy + wh)

    def _draw_bg(self, p: QPainter):
        if self.bg_image:
            scaled = self.bg_image.scaled(
                self.width, self.height,
                Qt.AspectRatioMode.KeepAspectRatioByExpanding,
                Qt.TransformationMode.SmoothTransformation,
            )
            x = (self.width - scaled.width()) // 2
            y = (self.height - scaled.height()) // 2
            p.drawPixmap(x, y, scaled)
            p.fillRect(0, 0, self.width, self.height, QColor(0, 0, 0, 130))
        else:
            bg = self._qcolors.get("background", QColor("#282a36"))
            g = QLinearGradient(0, 0, 0, self.height)
            g.setColorAt(0, bg.lighter(105))
            g.setColorAt(1, bg)
            p.fillRect(0, 0, self.width, self.height, g)

    @staticmethod
    def auto_font_size(lines_count: int, width: int, height: int,
                      padding: int = 24, show_window_chrome: bool = True,
                      show_line_numbers: bool = True, tab_size: int = 4,
                      text: Optional[str] = None, font_family: str = "Consolas",
                      keyboard_h: int = 0) -> int:
        chrome_h = 42 if show_window_chrome else 0
        kb_used = min(keyboard_h, (height - 2 * padding) // 3) if keyboard_h > 0 else 0
        rect_h = height - 2 * padding - kb_used - chrome_h
        rect_w = width  - 2 * padding - 8

        if rect_h < 20 or rect_w < 40 or lines_count < 1:
            return 14

        max_chars = 80
        if text:
            longest = max((len(line.replace("\t", " " * tab_size)) for line in text.split("\n")), default=1)
            max_chars = max(longest, 1)

        def _ln_width(cw: int) -> int:
            return (len(str(lines_count)) * cw + 16) if show_line_numbers else 0

        max_font_w = int((rect_w - _ln_width(10)) / max(max_chars, 1) * 1.8)
        max_font = max(8, min(48, max_font_w))
        
        target_vis = min(lines_count, 35)
        max_chars_check = min(max_chars, 120)

        v_lo, v_hi, v_best = 8, max_font, 14
        while v_lo <= v_hi:
            mid = (v_lo + v_hi) // 2
            fm = QFontMetrics(QFont(font_family, mid))
            line_h = fm.height()
            if target_vis * line_h <= rect_h:
                char_w = fm.horizontalAdvance("M")
                line_w = max_chars_check * char_w + _ln_width(char_w)
                if line_w <= rect_w:
                    v_best = mid
                    v_lo = mid + 1
                else:
                    v_hi = mid - 1
            else:
                v_hi = mid - 1

        return max(8, v_best)

    @staticmethod
    def _resolve_backspaces(chars: List[str]) -> str:
        out: List[str] = []
        for ch in chars:
            if ch == "\b":
                if out: out.pop()
            else:
                out.append(ch)
        return "".join(out)

    @staticmethod
    def _precompute_clean(display_chars: List[str], resolved: str) -> Tuple[List[bool], List[int]]:
        n = len(display_chars)
        is_clean: List[bool] = [True] * (n + 1)
        stack_len: List[int] = [0] * (n + 1)
        stack: List[Tuple[str, bool]] = []
        incorrect = 0
        rlen = len(resolved)

        for i in range(n):
            ch = display_chars[i]
            if ch == "\b":
                if stack:
                    _, was_correct = stack.pop()
                    if not was_correct:
                        incorrect -= 1
            else:
                pos = len(stack)
                was_correct = pos < rlen and ch == resolved[pos]
                stack.append((ch, was_correct))
                if not was_correct:
                    incorrect += 1
            is_clean[i + 1] = (incorrect == 0)
            stack_len[i + 1] = len(stack)

        return is_clean, stack_len

    def _get_cache(self, full_text: List[str]) -> Tuple[str, List[str], List[QColor], List[bool], List[int]]:
        cid = id(full_text)
        clen = len(full_text)
        if cid != self._cached_display_chars_id or clen != self._cached_display_chars_len:
            resolved = self._resolve_backspaces(full_text)
            self._cached_resolved = resolved
            self._cached_resolved_colors = self._tokenize_to_colors(resolved)
            fg = self._qc_fg
            qc = self._qcolors
            self._cached_resolved_color_qc = [qc.get(ck, fg) for ck in self._cached_resolved_colors]
            self._cached_is_clean, self._cached_stack_len = self._precompute_clean(full_text, resolved)
            self._cached_display_chars_id = cid
            self._cached_display_chars_len = clen
            self._dirty_num_visible = -1
            self._layout_nv = -1  # Invalidate layout cache on text change

        return (self._cached_resolved, self._cached_resolved_colors,
                self._cached_resolved_color_qc, self._cached_is_clean, self._cached_stack_len)

    def _get_line_layout(self, line: str) -> List[int]:
        cached = self._line_layout_cache.get(line)
        if cached is not None:
            return cached
        char_x: List[int] = []
        x = 0
        tab = self._tab_advance
        ham = self.fm.horizontalAdvance
        for ch in line:
            char_x.append(x)
            x += tab if ch == "\t" else ham(ch)
        if len(self._line_layout_cache) >= self._LINE_CACHE_MAX:
            self._line_layout_cache.popitem(last=False)
        self._line_layout_cache[line] = char_x
        return char_x

    def _tokenize_to_colors(self, text: str) -> List[str]:
        tokens = Tokenizer.tokenize(text, self.language)
        colors: List[str] = ["foreground"] * len(text)
        pos = 0
        get = self.TOKEN_COLOR_MAP.get
        n = len(colors)
        for ttype, ttxt in tokens:
            ckey = get(ttype, "foreground")
            end = min(pos + len(ttxt), n)
            colors[pos:end] = [ckey] * (end - pos)
            pos = end
        return colors

    def render_frame(self, display_chars: List[str], num_visible: int,
                     cursor_visible: bool = True, target: Optional[QImage] = None,
                     active_char: Optional[str] = None, key_flash: float = 0.0) -> QImage:
        img = target if target is not None else QImage(self.width, self.height, QImage.Format_RGB32)
        if target is None:
            img.fill(QColor(self.theme["background"]))

        with painter_context(img) as p:
            p.setRenderHint(QPainter.TextAntialiasing)
            p.drawImage(0, 0, self._bg)

            cr = self._text_rect
            resolved, resolved_colors, resolved_color_qc, is_clean, stack_len = self._get_cache(display_chars)

            if 0 <= num_visible < len(is_clean) and is_clean[num_visible]:
                vl = stack_len[num_visible]
                visible_text = resolved[:vl]
                vis_color_qc = resolved_color_qc[:vl]
            else:
                if num_visible != self._dirty_num_visible:
                    dirty_chars = display_chars[:num_visible]
                    self._dirty_visible_text = self._resolve_backspaces(dirty_chars)
                    dirty_colors = self._tokenize_to_colors(self._dirty_visible_text)
                    fg = self._qc_fg
                    qc = self._qcolors
                    self._dirty_vis_color_qc = [qc.get(ck, fg) for ck in dirty_colors]
                    self._dirty_num_visible = num_visible
                visible_text = self._dirty_visible_text
                vis_color_qc = self._dirty_vis_color_qc

            if num_visible != self._layout_nv:
                self._layout_lines = visible_text.split("\n")
                offsets: List[int] = []
                off = 0
                for ln in self._layout_lines:
                    offsets.append(off)
                    off += len(ln) + 1
                self._layout_offsets = offsets
                self._layout_cursor_line = visible_text.count("\n")
                self._layout_nv = num_visible

            lines = self._layout_lines
            line_offsets = self._layout_offsets
            cursor_line = self._layout_cursor_line

            total_lines = len(lines)
            cr_h = cr.height()
            cr_top = cr.top()

            max_vis = max(1, -(-cr_h // self.line_h))
            lh_base = self.line_h
            total_used = max_vis * lh_base
            remainder = cr_h - total_used
            lh_extra = 1 if (remainder > 0 and max_vis > 0) else 0

            scroll_margin_top = 3
            scroll_margin_bottom = min(5, max_vis - 1)
            scroll = 0
            if cursor_line >= scroll + max_vis - scroll_margin_bottom:
                scroll = max(0, cursor_line - max_vis + scroll_margin_bottom + 1)
            if cursor_line < scroll + scroll_margin_top:
                scroll = max(0, cursor_line - scroll_margin_top)

            max_scroll = max(0, total_lines - max_vis)
            if scroll > max_scroll:
                scroll = max_scroll

            ln_width = 0
            if self.show_line_numbers:
                ln_width = len(str(total_lines + scroll)) * self.char_w + 16

            current_scroll_line = cursor_line - scroll

            line_y_arr: List[int] = []
            line_h_arr: List[int] = []
            y_acc = cr_top
            for si in range(max_vis):
                li = scroll + si
                if li >= total_lines:
                    break
                lh = lh_base + (lh_extra if si < remainder else 0)
                line_y_arr.append(y_acc)
                line_h_arr.append(lh)
                y_acc += lh
            n_drawn = len(line_y_arr)

            if 0 <= current_scroll_line < n_drawn:
                idx = current_scroll_line
                p.fillRect(cr.left(), line_y_arr[idx], cr.width(), line_h_arr[idx], self._qc_current_line)

            if self.show_line_numbers and ln_width > 0:
                sep_x = cr.left() + ln_width
                sep_color = QColor(self._qc_ln)
                sep_color.setAlpha(60)
                p.setPen(QPen(sep_color, 1))
                p.drawLine(sep_x, cr.top(), sep_x, cr.top() + max_vis * lh_base)

            p.setClipRect(cr)
            p.setFont(self.font)
            x0 = cr.left() + ln_width
            n_vis_chars = len(visible_text)
            fg = self._qc_fg

            cr_w = cr.width() - ln_width
            h_scroll = 0
            if 0 <= current_scroll_line < n_drawn:
                li = scroll + current_scroll_line
                if li < len(lines):
                    line = lines[li]
                    char_x = self._get_line_layout(line)
                    n_ch = len(line)
                    if n_ch < len(char_x):
                        cursor_x_rel = char_x[n_ch]
                    else:
                        if line:
                            last_w = self._tab_advance if line[-1] == "\t" else self.fm.horizontalAdvance(line[-1])
                            cursor_x_rel = (char_x[-1] if char_x else 0) + last_w
                        else:
                            cursor_x_rel = 0
                    
                    if cursor_x_rel > h_scroll + cr_w - self.char_w * 4:
                        h_scroll = max(0, cursor_x_rel - (cr_w - self.char_w * 4))
                    elif cursor_x_rel < h_scroll:
                        h_scroll = max(0, cursor_x_rel - self.char_w)

            for si in range(n_drawn):
                li = scroll + si
                lh = line_h_arr[si]
                y = line_y_arr[si]
                global_off = line_offsets[li]

                if self.show_line_numbers:
                    p.setPen(self._qc_ln_active if li == cursor_line else self._qc_ln)
                    p.drawText(QRect(cr.left(), y, ln_width, lh),
                               Qt.AlignRight | Qt.AlignVCenter, str(li + 1))

                line = lines[li]

                if not line:
                    if cursor_visible and li == cursor_line:
                        caret_h = max(4, lh - 10)
                        self._draw_caret(p, int(x0 - h_scroll), int(y + lh * 0.18), caret_h)
                    continue

                char_x = self._get_line_layout(line)
                line_start_x = x0 - h_scroll

                cur_qc = vis_color_qc[global_off] if global_off < n_vis_chars else fg
                run_start = 0
                for j in range(1, len(line) + 1):
                    next_qc = fg
                    if j < len(line):
                        gp = global_off + j
                        next_qc = vis_color_qc[gp] if gp < n_vis_chars else fg
                    if j == len(line) or next_qc is not cur_qc:
                        run_text = line[run_start:j].replace("\t", " " * self.tab_size)
                        p.setPen(cur_qc)
                        p.drawText(QPoint(int(line_start_x + char_x[run_start]),
                                         int(y + lh * 0.78)), run_text)
                        cur_qc = next_qc
                        run_start = j

                if cursor_visible and li == cursor_line:
                    n_ch = len(line)
                    if n_ch < len(char_x):
                        cx = char_x[n_ch]
                    else:
                        last_x = char_x[-1] if char_x else 0
                        if line and line[-1] == "\t":
                            cx = last_x + self._tab_advance
                        elif line:
                            cx = last_x + self.fm.horizontalAdvance(line[-1])
                        else:
                            cx = last_x
                    caret_h = max(4, lh - 10)
                    self._draw_caret(p, int(line_start_x + cx), int(y + lh * 0.18), caret_h)

            p.setClipping(False)
            
            if self.keyboard_overlay:
                ak = None
                kf = 0.0
                if active_char is not None and key_flash > 0:
                    ak = self.keyboard_overlay.resolve_key(active_char)
                    kf = key_flash
                self.keyboard_overlay.draw(p, active_key=ak, flash=kf)

            if self.show_watermark:
                wm_font = QFont(self.font_family, max(8, self.font_size // 3))
                p.setFont(wm_font)
                p.setPen(QColor(self._qc_ln))
                wm_text = f"{datetime.now().strftime('%Y-%m-%d %H:%M')}  |  {self.title_text}"
                fm = QFontMetrics(wm_font)
                wm_w = fm.horizontalAdvance(wm_text)
                p.drawText(self.width - wm_w - 20, self.height - 10, wm_text)

        return img

    def _draw_caret(self, p: QPainter, x: int, y: int, h: Optional[int] = None):
        w = max(2, self.font_size // 10)
        caret_h = h if h is not None else self.line_h - 10
        
        if self.cursor_glow:
            glow_color = QColor(self._qc_cursor)
            glow_color.setAlpha(60)
            p.fillRect(x - w, y - 2, w * 3, caret_h + 4, glow_color)
            glow_color.setAlpha(100)
            p.fillRect(x - 1, y - 1, w * 2, caret_h + 2, glow_color)
            
        p.fillRect(x, y, w, caret_h, self._qc_cursor)


# =====================================================================
# 7. FFMPEG FACADE & WORKER PATTERN
# =====================================================================

class FFmpegFacade:
    """Encapsulates FFmpeg subprocess interactions."""
    
    @staticmethod
    def _get_startupinfo():
        if platform.system() == "Windows":
            si = subprocess.STARTUPINFO()
            si.dwFlags |= subprocess.STARTF_USESHOWWINDOW
            si.wShowWindow = subprocess.SW_HIDE
            return si
        return None

    @staticmethod
    def render_chunk(renderer: TextRenderer, animator: TypingAnimator, start_frame: int, n_frames: int, 
                     aud_path: str, has_audio: bool, out_path: str, fps: int, 
                     encoder_name: str, fade_in: float, fade_out: float, 
                     cancel_event: threading.Event, status_callback: Callable[[str], None]) -> bool:
        w, h = renderer.width, renderer.height
        
        cmd = [
            "ffmpeg", "-nostdin", "-loglevel", "warning", "-y",
            "-f", "rawvideo", "-pix_fmt", "rgb24",
            "-s", f"{w}x{h}", "-r", str(fps),
            "-i", "pipe:0",
        ]
        if has_audio:
            cmd += ["-i", aud_path]

        enc_args = ENCODERS.get(encoder_name, ENCODERS["YouTube Optimized (H.264/AAC)"])
        cmd += enc_args
        cmd += ["-pix_fmt", "yuv420p", "-movflags", "+faststart"]

        if has_audio:
            cmd += ["-c:a", "aac", "-b:a", "192k"]
        cmd.append(out_path)

        try:
            proc = subprocess.Popen(cmd, stdin=subprocess.PIPE,
                                    stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                                    startupinfo=FFmpegFacade._get_startupinfo())
        except FileNotFoundError:
            status_callback("FFmpeg not found.")
            return False

        stderr_chunks: list[bytes] = []
        def _drain():
            while True:
                chunk = proc.stderr.read(8192)
                if not chunk: break
                stderr_chunks.append(chunk)

        drain_t = threading.Thread(target=_drain, daemon=True)
        drain_t.start()

        scratch = QImage(w, h, QImage.Format_RGB32)
        write_queue: deque = deque()
        write_lock = threading.Lock()
        write_cv = threading.Condition(write_lock)
        write_error: list = []
        writer_done = False

        def _writer_thread():
            nonlocal writer_done
            try:
                while True:
                    with write_lock:
                        while not write_queue and not writer_done:
                            write_cv.wait(timeout=0.5)
                            if cancel_event.is_set():
                                break
                        if cancel_event.is_set() or (not write_queue and writer_done):
                            break
                        frame_data = write_queue.popleft()
                    if frame_data is None:
                        break
                    proc.stdin.write(frame_data)
            except Exception as exc:
                write_error.append(str(exc))
            finally:
                try:
                    proc.stdin.close()
                except (BrokenPipeError, OSError):
                    pass
                writer_done = True
                with write_lock:
                    write_cv.notify_all()

        writer_t = threading.Thread(target=_writer_thread, daemon=True)
        writer_t.start()

        prev_state = None
        prev_frame_bytes = None
        total_dur = animator.duration()

        for fi in range(n_frames):
            if cancel_event.is_set() or write_error:
                break

            t = (start_frame + fi) / fps
            nv = animator.visible_at(t)

            cur_vis = True
            if nv > 0:
                idx = bisect.bisect_right(animator._timestamps, t)
                if idx > 0:
                    last_ts = animator.timeline[idx - 1][0]
                    if t - last_ts > 0.25:
                        cur_vis = (int((t - last_ts) / renderer.CURSOR_BLINK) % 2) == 0

            active_char, key_flash = animator.active_key_at(t)
            kf_rounded = round(key_flash, 2)
            frame_state = (nv, cur_vis, active_char, kf_rounded)

            if frame_state == prev_state and prev_frame_bytes is not None:
                pass
            else:
                qimg = renderer.render_frame(
                    animator.display_chars, nv, cur_vis, target=scratch,
                    active_char=active_char, key_flash=key_flash,
                )
                
                alpha = 1.0
                if fade_in > 0 and t < fade_in:
                    alpha = max(0.0, t / fade_in)
                elif fade_out > 0 and t > total_dur - fade_out:
                    alpha = max(0.0, (total_dur - t) / fade_out)
                
                if alpha < 1.0:
                    with painter_context(qimg) as p:
                        p.setOpacity(1.0 - alpha)
                        p.fillRect(qimg.rect(), QColor(0, 0, 0))

                # Returns immutable bytes. Safe to queue and prevents race conditions.
                prev_frame_bytes = FFmpegFacade._qimg_to_rgb(qimg)
                prev_state = frame_state

            with write_lock:
                while len(write_queue) >= 24:  # Limit queue to prevent OOM
                    write_cv.wait(timeout=0.1)
                    if cancel_event.is_set() or write_error:
                        break
                if cancel_event.is_set() or write_error:
                    break
                write_queue.append(prev_frame_bytes)
                write_cv.notify_all()

        with write_lock:
            writer_done = True
            if not cancel_event.is_set() and not write_error:
                write_queue.append(None)
            write_cv.notify_all()
        
        writer_t.join(timeout=60)

        if cancel_event.is_set():
            try:
                proc.terminate()
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait()
            return False

        if write_error:
            status_callback(f"FFmpeg write failed: {write_error[0]}")
            return False

        try:
            proc.wait(timeout=600)
        except subprocess.TimeoutExpired:
            proc.kill()
            status_callback("FFmpeg timed out during rendering.")
            return False

        drain_t.join(timeout=5)

        if proc.returncode != 0:
            err = b"".join(stderr_chunks).decode(errors="ignore")[-800:]
            status_callback(f"FFmpeg failed (code {proc.returncode}): {err}")
            return False

        return True

    @staticmethod
    def stitch_chunks(chunk_paths: List[str], tmp_dir: str, output: str) -> None:
        concat_path = os.path.join(tmp_dir, "concat_list.txt")
        with open(concat_path, "w", encoding="utf-8") as f:
            for p in chunk_paths:
                safe_p = p.replace("\\", "/").replace("'", r"\'")
                f.write(f"file '{safe_p}'\n")

        cmd = [
            "ffmpeg", "-nostdin", "-loglevel", "warning", "-y",
            "-f", "concat", "-safe", "0",
            "-i", concat_path,
            "-c", "copy",
            "-movflags", "+faststart",
            output
        ]

        try:
            proc = subprocess.Popen(cmd, stdin=subprocess.DEVNULL,
                                    stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                                    startupinfo=FFmpegFacade._get_startupinfo())
            try:
                proc.wait(timeout=120)
            except subprocess.TimeoutExpired:
                proc.kill()
                raise RuntimeError("Stitching timed out after 120 seconds.")
            
            if proc.returncode != 0:
                err = proc.stderr.read(8192).decode(errors="ignore")
                raise RuntimeError(f"Stitching failed: {err}")
        except Exception as e:
            raise RuntimeError(f"Failed to stitch chunks: {e}")

    @staticmethod
    def _qimg_to_rgb(qimg: QImage) -> bytes:
        """Converts a QImage to raw RGB24 bytes for FFmpeg pipe."""
        w, h = qimg.width(), qimg.height()
        bpl = qimg.bytesPerLine()

        if qimg.format() in (QImage.Format_RGB32, QImage.Format_ARGB32) and bpl >= w * 4:
            ptr = qimg.constBits()
            if hasattr(ptr, 'setsize'):
                ptr.setsize(h * bpl)
            # RGB32 is 0xffRRGGBB, stored as B, G, R, 255 in memory (little-endian)
            arr = np.frombuffer(ptr, dtype=np.uint8).reshape((h, bpl // 4, 4))[:, :w, :]
            # Select R, G, B (indices 2, 1, 0) and make contiguous
            rgb_arr = np.ascontiguousarray(arr[:, :, 2::-1])
            return rgb_arr.tobytes()

        # Fallback for other formats
        qimg = qimg.convertToFormat(QImage.Format_RGB888)
        bpl = qimg.bytesPerLine()
        ptr = qimg.constBits()
        if hasattr(ptr, 'setsize'):
            ptr.setsize(h * bpl)
        arr = np.frombuffer(ptr, dtype=np.uint8).reshape((h, bpl))
        return np.ascontiguousarray(arr[:, :w * 3]).tobytes()


class VideoExportWorker(QObject):
    """Worker object that runs on a background QThread."""
    progress = Signal(int)
    status = Signal(str)
    finished_ok = Signal(str)
    error = Signal(str)
    finished = Signal()

    CHUNK_DURATION = 600.0

    def __init__(self, text: str, output: str, renderer: TextRenderer,
                 animator: TypingAnimator, fps: int = 30,
                 sound_gen: Optional[SimpleSoundGen] = None,
                 volume: float = 0.5,
                 encoder_name: str = "YouTube Optimized (H.264/AAC)",
                 fade_in: float = 0.5, fade_out: float = 0.5):
        super().__init__()
        self.text = text
        self.output = output
        self.renderer = renderer
        self.animator = animator
        self.fps = fps
        self.sound_gen = sound_gen
        self.volume = volume
        self.encoder_name = encoder_name
        self.fade_in = fade_in
        self.fade_out = fade_out
        self._cancel = threading.Event()

    def cancel(self):
        self._cancel.set()

    @Slot()
    def run(self):
        tmp = ""
        try:
            os.makedirs(TEMP_DIR, exist_ok=True)
            tmp = tempfile.mkdtemp(dir=TEMP_DIR, prefix="export_")
            
            total_dur = self.animator.duration()
            num_chunks = max(1, math.ceil(total_dur / self.CHUNK_DURATION))
            chunk_paths = []

            self.status.emit(f"Preparing {num_chunks} chunks for rendering...")

            for c_idx in range(num_chunks):
                if self._cancel.is_set():
                    break

                start_t = c_idx * self.CHUNK_DURATION
                end_t = min(total_dur, start_t + self.CHUNK_DURATION)
                start_frame = int(start_t * self.fps)
                end_frame = int(end_t * self.fps)
                n_chunk_frames = end_frame - start_frame

                self.status.emit(f"Rendering Chunk {c_idx+1}/{num_chunks} (Frames {start_frame} to {end_frame})...")

                chunk_aud = os.path.join(tmp, f"aud_{c_idx}.wav")
                chunk_vid = os.path.join(tmp, f"chunk_{c_idx}.mp4")

                has_audio = False
                if self.sound_gen:
                    chunk_ts = [(ts - start_t, ch) for ts, ch in self.animator.char_timestamps() if start_t <= ts < end_t]
                    if chunk_ts:
                        self.sound_gen.generate_track(chunk_ts, chunk_aud, self.volume)
                        has_audio = os.path.getsize(chunk_aud) > 44

                if not FFmpegFacade.render_chunk(self.renderer, self.animator, start_frame, n_chunk_frames, 
                                                 chunk_aud, has_audio, chunk_vid, self.fps, self.encoder_name, 
                                                 self.fade_in, self.fade_out, self._cancel, self.status.emit):
                    if self._cancel.is_set():
                        break
                    raise RuntimeError(f"Failed to render chunk {c_idx+1}. See status log for FFmpeg details.")

                chunk_paths.append(chunk_vid)
                overall_pct = int(((c_idx + 1) / num_chunks) * 100)
                self.progress.emit(overall_pct)

            if self._cancel.is_set():
                self.error.emit("Cancelled")
                return

            self.status.emit("Stitching chunks together for final export...")
            FFmpegFacade.stitch_chunks(chunk_paths, tmp, self.output)

            self.progress.emit(100)
            self.status.emit(f"Done -> {self.output}")
            self.finished_ok.emit(self.output)

        except Exception as e:
            log.error("Export failed: %s", e, exc_info=True)
            self.error.emit(str(e))
        finally:
            try:
                if tmp: shutil.rmtree(tmp, ignore_errors=True)
            except (OSError, NameError):
                pass
            self.finished.emit()


# =====================================================================
# 8. GUI DIALOGS & MAIN WINDOW
# =====================================================================

_SAMPLE_TEXT = """The Art of Writing

Writing is a medium of human communication that represents
language through the inscription or recording of signs and
symbols.

The key elements of effective writing include:

1. Clarity - Using precise, unambiguous language
2. Conciseness - Expressing ideas with minimal words
3. Coherence - Maintaining logical flow between ideas
4. Correctness - Following grammatical and spelling rules
5. Engagement - Captivating the reader's interest

"Good writing is clear thinking made visible."
                                    — Bill Wheeler
"""

class _PreviewImageLabel(QLabel):
    def __init__(self, parent=None):
        super().__init__(parent)
        self._pixmap = None
        self.setAlignment(Qt.AlignCenter)
        self.setMinimumSize(480, 270)
        self.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)
        self.setStyleSheet("background: #11111b; border-radius: 8px;")

    def set_preview_image(self, qimg: QImage):
        self._pixmap = QPixmap.fromImage(qimg)
        self._update_painted()

    def resizeEvent(self, event):
        super().resizeEvent(event)
        self._update_painted()

    def _update_painted(self):
        if self._pixmap is None:
            return
        scaled = self._pixmap.scaled(
            self.size(), Qt.AspectRatioMode.KeepAspectRatio,
            Qt.TransformationMode.SmoothTransformation,
        )
        self.setPixmap(scaled)


class _ExportTableWidget(QTableWidget):
    def mousePressEvent(self, event: QEvent) -> None:
        super().mousePressEvent(event)
        if event.button() != Qt.MouseButton.LeftButton:
            return
        
        pos = event.position().toPoint() if hasattr(event, 'position') else event.pos()
        item = self.itemAt(pos)
        if not item:
            return
        
        if item.column() != 0:
            chk_item = self.item(item.row(), 0)
            if chk_item is not None:
                new_state = Qt.CheckState.Checked if chk_item.checkState() == Qt.CheckState.Unchecked else Qt.CheckState.Unchecked
                chk_item.setCheckState(new_state)


@dataclass(slots=True)
class FileItem:
    path: str
    checked: bool = False
    status: ExportStatus = ExportStatus.PENDING
    output_path: Optional[str] = None
    error: Optional[str] = None


class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Simple Text Typing Video Generator")
        self.setAcceptDrops(True)

        self._items: List[FileItem] = []
        self._item_paths: set[str] = set()
        
        self._export_thread: Optional[QThread] = None
        self._export_worker: Optional[VideoExportWorker] = None
        self._export_queue: List[FileItem] = []
        self._loading_settings = False
        self._bg_image_path = ""

        self._checkbox_anchor: Optional[int] = None

        self._preview_progress = 0.30
        self._preview_animating = False
        self._preview_anim_t = 0.0
        self._preview_timer = QTimer(self)
        self._preview_timer.setInterval(33)
        self._preview_timer.timeout.connect(self._advance_preview_animation)

        self._cached_preview_key: Optional[tuple] = None
        self._cached_preview_code: Optional[str] = None
        self._cached_preview_renderer: Optional["TextRenderer"] = None
        self._cached_preview_animator: Optional["TypingAnimator"] = None
        self._preview_scratch: Optional[QImage] = None
        self._cached_preview_pcm: Optional[np.ndarray] = None
        self._cached_preview_pcm_sr: int = 44100
        self._cached_preview_pcm_channels: int = 1
        
        self._cached_text_key: Optional[tuple] = None
        self._cached_text: str = ""

        self._build_ui()
        self._connect_settings_signals()
        self._load_settings()
        self._scan_input_dir()
        QTimer.singleShot(500, self._update_preview)

    def dragEnterEvent(self, event):
        if event.mimeData().hasUrls():
            event.acceptProposedAction()

    def dropEvent(self, event):
        for url in event.mimeData().urls():
            path = url.toLocalFile()
            if os.path.isfile(path) and os.path.splitext(path)[1].lower() in SUPPORTED_EXTENSIONS:
                if path not in self._item_paths:
                    item = FileItem(path=path, checked=True)
                    self._items.append(item)
                    self._item_paths.add(path)
            elif os.path.isdir(path):
                self._scan_directory(path)
        self._refresh_table()
        self._invalidate_preview_cache()
        self._schedule_preview_update()

    def _build_ui(self):
        central = QWidget()
        self.setCentralWidget(central)
        root = QVBoxLayout(central)
        root.setContentsMargins(16, 16, 16, 16)
        root.setSpacing(12)

        hsplit = QSplitter(Qt.Horizontal)
        hsplit.setHandleWidth(8)

        left_panel = QVBoxLayout()
        left_panel.setContentsMargins(0, 0, 0, 0)

        file_group = QGroupBox("Documents")
        fg_lay = QVBoxLayout(file_group)

        btn_row = QHBoxLayout()
        self.scan_btn = QPushButton("Scan input/")
        self.scan_btn.setToolTip("Scan the default 'input' folder for supported files.")
        self.scan_btn.clicked.connect(self._scan_input_dir)
        btn_row.addWidget(self.scan_btn)

        self.scan_folder_btn = QPushButton("Choose Folder...")
        self.scan_folder_btn.setToolTip("Open a specific folder to scan for files.")
        self.scan_folder_btn.clicked.connect(self._scan_folder)
        btn_row.addWidget(self.scan_folder_btn)

        self.add_btn = QPushButton("Add files...")
        self.add_btn.setToolTip("Manually add individual files to the list.")
        self.add_btn.clicked.connect(self._add_files)
        btn_row.addWidget(self.add_btn)
        
        self.clear_btn = QPushButton("Clear List")
        self.clear_btn.setToolTip("Remove all files from the list.")
        self.clear_btn.clicked.connect(self._clear_list)
        btn_row.addWidget(self.clear_btn)

        btn_row.addStretch()

        self.recurse_chk = QCheckBox("Recursive")
        self.recurse_chk.setChecked(True)
        self.recurse_chk.setToolTip("Scan subfolders recursively.")
        btn_row.addWidget(self.recurse_chk)

        btn_row.addWidget(QLabel("Depth:"))
        self.depth_sp = QSpinBox()
        self.depth_sp.setRange(1, 99)
        self.depth_sp.setValue(10)
        self.depth_sp.setToolTip("Max recursion depth (1 = only root folder).")
        self.depth_sp.setFixedWidth(60)
        btn_row.addWidget(self.depth_sp)
        fg_lay.addLayout(btn_row)

        btn_row2 = QHBoxLayout()
        self.select_all_btn = QPushButton("Select All")
        self.select_all_btn.clicked.connect(self._select_all)
        btn_row2.addWidget(self.select_all_btn)

        self.deselect_all_btn = QPushButton("Deselect All")
        self.deselect_all_btn.clicked.connect(self._deselect_all)
        btn_row2.addWidget(self.deselect_all_btn)

        self.file_count_lbl = QLabel("")
        self.file_count_lbl.setStyleSheet("color: #a6adc8; font-size: 11px;")
        btn_row2.addWidget(self.file_count_lbl)

        btn_row2.addStretch()
        fg_lay.addLayout(btn_row2)

        self.table = _ExportTableWidget(0, 4)
        self.table.setHorizontalHeaderLabels(["Export", "Path", "Language", "Status"])
        self.table.setSelectionBehavior(QTableWidget.SelectRows)
        self.table.setEditTriggers(QTableWidget.NoEditTriggers)
        self.table.verticalHeader().setVisible(False)
        self.table.setContextMenuPolicy(Qt.CustomContextMenu)
        self.table.customContextMenuRequested.connect(self._on_table_context_menu)
        hdr = self.table.horizontalHeader()
        hdr.setSectionResizeMode(0, QHeaderView.Fixed)
        hdr.resizeSection(0, 60)
        hdr.setSectionResizeMode(1, QHeaderView.Stretch)
        hdr.setSectionResizeMode(2, QHeaderView.Fixed)
        hdr.resizeSection(2, 90)
        hdr.setSectionResizeMode(3, QHeaderView.Stretch)
        self.table.itemChanged.connect(self._on_item_changed)
        fg_lay.addWidget(self.table)
        left_panel.addWidget(file_group, stretch=1)

        self.progress_bar = QProgressBar()
        self.progress_bar.setValue(0)
        left_panel.addWidget(self.progress_bar)

        btn_row3 = QHBoxLayout()
        btn_row3.addStretch()
        self.export_btn = QPushButton("Export Checked")
        self.export_btn.setObjectName("primaryBtn")
        self.export_btn.setMinimumHeight(36)
        self.export_btn.setToolTip("Begin exporting all checked files to MP4 format.")
        self.export_btn.clicked.connect(self._start_export)
        btn_row3.addWidget(self.export_btn)
        self.cancel_btn = QPushButton("Cancel")
        self.cancel_btn.setToolTip("Cancel the current ongoing export process.")
        self.cancel_btn.setEnabled(False)
        self.cancel_btn.clicked.connect(self._cancel_export)
        btn_row3.addWidget(self.cancel_btn)
        left_panel.addLayout(btn_row3)

        left_widget = QWidget()
        left_widget.setLayout(left_panel)
        hsplit.addWidget(left_widget)

        right_panel = QVBoxLayout()
        right_panel.setContentsMargins(0, 0, 0, 0)

        settings_tabs = QTabWidget()
        settings_tabs.setObjectName("settingsTabs")

        preview_tab = QWidget()
        pl = QVBoxLayout(preview_tab)
        pl.setContentsMargins(8, 8, 8, 8)
        pl.setSpacing(6)

        self._preview_label = _PreviewImageLabel()
        shadow = QGraphicsDropShadowEffect()
        shadow.setBlurRadius(20)
        shadow.setOffset(0, 4)
        shadow.setColor(QColor(0, 0, 0, 120))
        self._preview_label.setGraphicsEffect(shadow)
        pl.addWidget(self._preview_label, stretch=1)

        info_row1 = QHBoxLayout()
        self._preview_render_time_lbl = QLabel()
        self._preview_render_time_lbl.setStyleSheet("color: #a6adc8; font-size: 11px;")
        info_row1.addWidget(self._preview_render_time_lbl)
        info_row1.addStretch()

        self._preview_duration_lbl = QLabel("Duration: 00:00")
        self._preview_duration_lbl.setStyleSheet("color: #a6e3a1; font-size: 11px; font-weight: bold;")
        info_row1.addWidget(self._preview_duration_lbl)
        pl.addLayout(info_row1)
        
        self._stats_lbl = QLabel("")
        self._stats_lbl.setStyleSheet("color: #a6adc8; font-size: 11px;")
        pl.addWidget(self._stats_lbl)

        info_row2 = QHBoxLayout()
        self._prev_btn = QPushButton("◀ Prev")
        self._prev_btn.setToolTip("Jump backwards in the preview timeline.")
        self._prev_btn.setFixedWidth(70)
        self._prev_btn.clicked.connect(self._preview_prev)
        info_row2.addWidget(self._prev_btn)

        self._frame_slider = QSlider(Qt.Orientation.Horizontal)
        self._frame_slider.setRange(0, 100)
        self._frame_slider.setValue(30)
        self._frame_slider.setToolTip("Scrub through the typing animation timeline.")
        self._frame_slider.valueChanged.connect(self._on_preview_slider)
        info_row2.addWidget(self._frame_slider, stretch=1)

        self._next_btn = QPushButton("Next ▶")
        self._next_btn.setToolTip("Jump forwards in the preview timeline.")
        self._next_btn.setFixedWidth(70)
        self._next_btn.clicked.connect(self._preview_next)
        info_row2.addWidget(self._next_btn)

        self._frame_lbl = QLabel("30%")
        self._frame_lbl.setStyleSheet("color: #cdd6f4; font-size: 11px; min-width: 100px;")
        self._frame_lbl.setAlignment(Qt.AlignCenter)
        info_row2.addWidget(self._frame_lbl)

        self._play_btn = QPushButton("▶ Animate")
        self._play_btn.setObjectName("previewBtn")
        self._play_btn.setToolTip("Play the typing animation in real-time with audio.")
        self._play_btn.setFixedWidth(90)
        self._play_btn.clicked.connect(self._toggle_preview_animation)
        info_row2.addWidget(self._play_btn)
        pl.addLayout(info_row2)

        settings_tabs.addTab(preview_tab, "Preview")

        settings_container = QWidget()
        settings_scroll = QScrollArea()
        settings_scroll.setWidget(settings_container)
        settings_scroll.setWidgetResizable(True)
        settings_scroll.setFrameShape(QFrame.NoFrame)
        sl = QVBoxLayout(settings_container)
        sl.setSpacing(16)
        sl.setContentsMargins(12, 12, 12, 12)

        visual_grp = QGroupBox("Visual")
        vl = QFormLayout(visual_grp)
        vl.setSpacing(10)
        vl.setContentsMargins(12, 16, 12, 12)

        self.theme_cb = QComboBox()
        self.theme_cb.addItems(list(THEMES.keys()))
        self.theme_cb.setCurrentText("Dracula")
        self.theme_cb.setToolTip("Select the color theme for the code editor.")
        vl.addRow("Theme:", self.theme_cb)

        self.res_cb = QComboBox()
        self.res_cb.addItems(list(RESOLUTIONS.keys()))
        self.res_cb.setCurrentText("1920x1080")
        self.res_cb.setToolTip("Set the output video resolution.")
        vl.addRow("Resolution:", self.res_cb)

        self.font_family_cb = QComboBox()
        _known_mono = [
            "Consolas", "JetBrains Mono", "Fira Code", "Cascadia Code",
            "Source Code Pro", "Inconsolata", "Ubuntu Mono", "DejaVu Sans Mono",
            "Liberation Mono", "Courier New", "Courier 10 Pitch", "FreeMono",
            "Nimbus Mono PS", "monospace",
        ]
        _available_families = QFontDatabase.families()
        _mono_choices = [f for f in _known_mono if f in _available_families]
        for fam in sorted(_available_families):
            if fam not in _mono_choices:
                test_font = QFont(fam)
                test_font.setFixedPitch(True)
                if test_font.fixedPitch():
                    _mono_choices.append(fam)
        self.font_family_cb.addItems(_mono_choices)
        self.font_family_cb.setCurrentText("Consolas" if "Consolas" in _mono_choices else (_mono_choices[0] if _mono_choices else "monospace"))
        self.font_family_cb.setToolTip("Select the monospace font for the text.")
        vl.addRow("Text Font:", self.font_family_cb)

        font_size_row = QHBoxLayout()
        self.font_size_auto_chk = QCheckBox("Auto")
        self.font_size_auto_chk.setChecked(True)
        self.font_size_auto_chk.setToolTip("Automatically calculate font size based on resolution and text length.")
        font_size_row.addWidget(self.font_size_auto_chk)
        self.font_size_sp = QSpinBox()
        self.font_size_sp.setRange(8, 72)
        self.font_size_sp.setValue(22)
        self.font_size_sp.setSuffix(" px")
        self.font_size_sp.setEnabled(False)
        self.font_size_sp.setToolTip("Manually set the font size in pixels.")
        font_size_row.addWidget(self.font_size_sp)
        self.font_size_auto_chk.toggled.connect(self._on_font_size_auto_toggled)
        vl.addRow("Font Size:", font_size_row)

        title_row = QHBoxLayout()
        self.title_auto_chk = QCheckBox("Auto")
        self.title_auto_chk.setChecked(True)
        self.title_auto_chk.setToolTip("Use the filename as the window title automatically.")
        title_row.addWidget(self.title_auto_chk)
        self.title_edit = QLineEdit()
        self.title_edit.setPlaceholderText("filename - Text Editor")
        self.title_edit.setEnabled(False)
        self.title_edit.setToolTip("Custom text to display in the fake window title bar.")
        title_row.addWidget(self.title_edit)
        self.title_auto_chk.toggled.connect(self._on_title_auto_toggled)
        vl.addRow("Window Title:", title_row)
        
        bg_row = QHBoxLayout()
        self.bg_edit = QLineEdit()
        self.bg_edit.setPlaceholderText("Background image path (optional)")
        self.bg_edit.setToolTip("Path to a background image to use instead of a solid color.")
        bg_row.addWidget(self.bg_edit)
        bg_btn = QPushButton("Browse...")
        bg_btn.clicked.connect(self._browse_bg_image)
        bg_row.addWidget(bg_btn)
        self.bg_clear_btn = QPushButton("Clear")
        self.bg_clear_btn.clicked.connect(self._clear_bg_image)
        bg_row.addWidget(self.bg_clear_btn)
        vl.addRow("BG Image:", bg_row)
        
        self.fade_in_sp = QDoubleSpinBox()
        self.fade_in_sp.setRange(0, 5)
        self.fade_in_sp.setSingleStep(0.1)
        self.fade_in_sp.setValue(0.5)
        self.fade_in_sp.setToolTip("Duration of the fade-in effect at the start of the video (seconds).")
        vl.addRow("Fade In (s):", self.fade_in_sp)

        self.fade_out_sp = QDoubleSpinBox()
        self.fade_out_sp.setRange(0, 5)
        self.fade_out_sp.setSingleStep(0.1)
        self.fade_out_sp.setValue(0.5)
        self.fade_out_sp.setToolTip("Duration of the fade-out effect at the end of the video (seconds).")
        vl.addRow("Fade Out (s):", self.fade_out_sp)

        self.clean_text_chk = QCheckBox("Auto-Clean Text Spacing")
        self.clean_text_chk.setChecked(True)
        self.clean_text_chk.setToolTip("Remove trailing whitespace and condense multiple blank lines.")
        vl.addRow(self.clean_text_chk)

        self.cursor_glow_chk = QCheckBox("Cursor Glow Effect")
        self.cursor_glow_chk.setChecked(True)
        self.cursor_glow_chk.setToolTip("Add a subtle glow around the blinking cursor.")
        vl.addRow(self.cursor_glow_chk)
        
        self.watermark_chk = QCheckBox("Show Watermark (Date/Time + Filename)")
        self.watermark_chk.setChecked(False)
        self.watermark_chk.setToolTip("Overlay a small watermark with the current date and filename in the bottom right.")
        vl.addRow(self.watermark_chk)

        sl.addWidget(visual_grp)

        layout_grp = QGroupBox("Layout")
        ll = QFormLayout(layout_grp)
        ll.setSpacing(10)
        ll.setContentsMargins(12, 16, 12, 12)

        self.padding_sp = QSpinBox()
        self.padding_sp.setRange(0, 120)
        self.padding_sp.setValue(24)
        self.padding_sp.setSuffix(" px")
        self.padding_sp.setToolTip("Padding around the window editor in pixels.")
        ll.addRow("Padding:", self.padding_sp)

        self.chrome_chk = QCheckBox("Show Window Chrome")
        self.chrome_chk.setChecked(True)
        self.chrome_chk.setToolTip("Display the fake title bar with window controls.")
        ll.addRow(self.chrome_chk)

        self.line_numbers_chk = QCheckBox("Show Line Numbers")
        self.line_numbers_chk.setChecked(True)
        self.line_numbers_chk.setToolTip("Display line numbers on the left side of the text.")
        ll.addRow(self.line_numbers_chk)

        sl.addWidget(layout_grp)

        typing_grp = QGroupBox("Typing")
        tl = QFormLayout(typing_grp)
        tl.setSpacing(10)
        tl.setContentsMargins(12, 16, 12, 12)

        self.wpm_sp = QSpinBox()
        self.wpm_sp.setRange(30, 300)
        self.wpm_sp.setValue(100)
        self.wpm_sp.setToolTip("Typing speed in Words Per Minute.")
        tl.addRow("WPM:", self.wpm_sp)

        self.auto_speed_shorts_chk = QCheckBox("Auto-Adjust Speed (< 3 min Shorts)")
        self.auto_speed_shorts_chk.setChecked(False)
        self.auto_speed_shorts_chk.setToolTip("Automatically adjust WPM so the video fits within 3 minutes.")
        tl.addRow(self.auto_speed_shorts_chk)

        self.fps_sp = QSpinBox()
        self.fps_sp.setRange(10, 60)
        self.fps_sp.setValue(30)
        self.fps_sp.setToolTip("Frames Per Second for the output video.")
        tl.addRow("FPS:", self.fps_sp)

        self.start_pause_sp = QDoubleSpinBox()
        self.start_pause_sp.setRange(0, 10)
        self.start_pause_sp.setSingleStep(0.5)
        self.start_pause_sp.setValue(0.5)
        self.start_pause_sp.setToolTip("Pause before typing begins (seconds).")
        tl.addRow("Start Pause (s):", self.start_pause_sp)

        self.end_pause_sp = QDoubleSpinBox()
        self.end_pause_sp.setRange(0, 10)
        self.end_pause_sp.setSingleStep(0.5)
        self.end_pause_sp.setValue(1.5)
        self.end_pause_sp.setToolTip("Pause after typing finishes (seconds).")
        tl.addRow("End Pause (s):", self.end_pause_sp)
        
        self.typo_rate_sp = QDoubleSpinBox()
        self.typo_rate_sp.setRange(0.0, 0.2)
        self.typo_rate_sp.setSingleStep(0.01)
        self.typo_rate_sp.setValue(0.0)
        self.typo_rate_sp.setToolTip("Probability of making a typo and correcting it (0.0 to 0.2).")
        tl.addRow("Typo Rate:", self.typo_rate_sp)
        
        self.encoder_cb = QComboBox()
        self.encoder_cb.addItems(list(ENCODERS.keys()))
        self.encoder_cb.setCurrentText("YouTube Optimized (H.264/AAC)")
        self.encoder_cb.setToolTip("Select the FFmpeg video encoder. Hardware encoders (NVENC, QSV, AMF) are much faster if available.")
        tl.addRow("Encoder:", self.encoder_cb)

        sl.addWidget(typing_grp)

        audio_grp = QGroupBox("Audio")
        al = QFormLayout(audio_grp)
        al.setSpacing(10)
        al.setContentsMargins(12, 16, 12, 12)

        self.sound_chk = QCheckBox("Typing Sounds")
        self.sound_chk.setChecked(True)
        self.sound_chk.setToolTip("Generate procedural typing audio.")
        self.sound_chk.toggled.connect(self._on_sound_toggled)
        al.addRow(self.sound_chk)

        self.vol_sl = QSpinBox()
        self.vol_sl.setRange(0, 100)
        self.vol_sl.setValue(50)
        self.vol_sl.setSuffix("%")
        self.vol_sl.setToolTip("Audio volume percentage.")
        al.addRow("Volume:", self.vol_sl)

        self.sound_preset_cb = QComboBox()
        self.sound_preset_cb.addItems(list(SOUND_PRESETS.keys()))
        self.sound_preset_cb.setCurrentText("Mechanical")
        self.sound_preset_cb.setToolTip("Select the mechanical profile for the typing sounds.")
        self.sound_preset_cb.currentTextChanged.connect(self._on_preset_changed)
        al.addRow("Sound Preset:", self.sound_preset_cb)

        self.preset_desc_lbl = QLabel(SOUND_PRESETS["Mechanical"]["description"])
        self.preset_desc_lbl.setStyleSheet("color: #a6adc8; font-size: 11px; font-style: italic;")
        al.addRow(self.preset_desc_lbl)

        self.binaural_chk = QCheckBox("Binaural ASMR (Stereo Panning)")
        self.binaural_chk.setChecked(False)
        self.binaural_chk.setToolTip("Pan sounds left/right based on key location for ASMR effect.")
        al.addRow(self.binaural_chk)
        
        self.reverb_amt_sp = QDoubleSpinBox()
        self.reverb_amt_sp.setRange(0.0, 0.5)
        self.reverb_amt_sp.setSingleStep(0.05)
        self.reverb_amt_sp.setValue(0.10)
        self.reverb_amt_sp.setSuffix(" amt")
        self.reverb_amt_sp.setToolTip("Amount of reverb/echo applied to the sounds for a roomy feel.")
        al.addRow("ASMR Reverb:", self.reverb_amt_sp)

        test_row = QHBoxLayout()
        self.test_sound_btn = QPushButton("🔊  Test Sound Preset")
        self.test_sound_btn.setToolTip("Play a short sample of the selected sound preset.")
        self.test_sound_btn.clicked.connect(self._test_sound)
        test_row.addWidget(self.test_sound_btn)
        test_row.addStretch()
        al.addRow(test_row)

        sl.addWidget(audio_grp)

        kb_grp = QGroupBox("Keyboard")
        kl = QFormLayout(kb_grp)
        kl.setSpacing(10)
        kl.setContentsMargins(12, 16, 12, 12)

        self.kb_overlay_chk = QCheckBox("Show Keyboard Overlay")
        self.kb_overlay_chk.setChecked(False)
        self.kb_overlay_chk.setToolTip("Display a visual keyboard at the bottom that highlights keys as they are typed.")
        self.kb_overlay_chk.toggled.connect(self._on_kb_overlay_toggled)
        kl.addRow(self.kb_overlay_chk)

        self.kb_layout_cb = QComboBox()
        self.kb_layout_cb.addItems(list(KEYBOARD_LAYOUTS.keys()))
        self.kb_layout_cb.setCurrentText("QWERTY")
        self.kb_layout_cb.setEnabled(False)
        self.kb_layout_cb.setToolTip("Select the layout of the visual keyboard overlay.")
        self.kb_layout_cb.currentTextChanged.connect(self._on_kb_layout_changed)
        kl.addRow("Layout:", self.kb_layout_cb)

        self.kb_position_cb = QComboBox()
        self.kb_position_cb.addItems([
            "Bottom Center", "Bottom Right", "Bottom Left",
            "Center Left", "Center Right",
            "Top Center", "Top Right", "Top Left",
        ])
        self.kb_position_cb.setCurrentText("Bottom Center")
        self.kb_position_cb.setEnabled(False)
        self.kb_position_cb.setToolTip("Position of the keyboard overlay on the screen.")
        kl.addRow("Position:", self.kb_position_cb)
        
        self.kb_opacity_sp = QDoubleSpinBox()
        self.kb_opacity_sp.setRange(0.1, 1.0)
        self.kb_opacity_sp.setSingleStep(0.05)
        self.kb_opacity_sp.setValue(0.82)
        self.kb_opacity_sp.setToolTip("Transparency of the keyboard overlay (0.1 to 1.0).")
        kl.addRow("Overlay Opacity:", self.kb_opacity_sp)

        self.kb_desc_lbl = QLabel(KEYBOARD_LAYOUTS["QWERTY"]["description"])
        self.kb_desc_lbl.setStyleSheet("color: #a6adc8; font-size: 11px; font-style: italic;")
        self.kb_desc_lbl.setEnabled(False)
        kl.addRow(self.kb_desc_lbl)

        sl.addWidget(kb_grp)
        sl.addStretch()

        settings_tabs.addTab(settings_scroll, "Settings")

        right_panel.addWidget(settings_tabs)
        
        right_widget = QWidget()
        right_widget.setLayout(right_panel)
        hsplit.addWidget(right_widget)

        root.addWidget(hsplit, stretch=1)
        hsplit.setSizes([600, 400])

        self.statusBar().showMessage("Ready. Place text, CSV, or Markdown files in input/ folder and click Scan.")

        self._preview_audio_player = QMediaPlayer()
        self._preview_audio_out = QAudioOutput()
        self._preview_audio_player.setAudioOutput(self._preview_audio_out)
        self._preview_audio_buf = None

    def _browse_bg_image(self):
        path, _ = QFileDialog.getOpenFileName(self, "Select Background Image", "", "Images (*.png *.jpg *.jpeg *.bmp)")
        if path:
            self._bg_image_path = path
            self.bg_edit.setText(path)

    def _clear_bg_image(self):
        self._bg_image_path = ""
        self.bg_edit.setText("")

    def _on_bg_edit_changed(self, text):
        self._bg_image_path = text.strip()
        self._invalidate_preview_cache()
        self._schedule_preview_update()
        self._auto_save_settings()

    def _on_sound_toggled(self, checked: bool):
        self.sound_preset_cb.setEnabled(checked)
        self.preset_desc_lbl.setEnabled(checked)

    def _on_preset_changed(self, preset_name: str):
        desc = SOUND_PRESETS.get(preset_name, {}).get("description", "")
        self.preset_desc_lbl.setText(desc)

    def _test_sound(self):
        try:
            preset = self.sound_preset_cb.currentText()
            vol = self.vol_sl.value() / 100.0
            stereo = self.binaural_chk.isChecked()
            reverb_amt = self.reverb_amt_sp.value()
            sound_gen = SimpleSoundGen(preset=preset, stereo=stereo, reverb_amt=reverb_amt)
            test_chars = list("hello world\n")
            timestamps = []
            t = 0.0
            for ch in test_chars:
                timestamps.append((t, ch))
                if ch == "\n": t += 0.25
                elif ch == " ": t += 0.12
                else: t += 0.08
            pcm = sound_gen.generate_pcm(timestamps, vol)
            if len(pcm) > 0:
                channels = 2 if stereo else 1
                wav_bytes = _pcm_to_wav_bytes(pcm, sound_gen.sr, channels)
                if self._preview_audio_player is not None:
                    self._preview_audio_player.stop()
                if self._preview_audio_buf is not None:
                    self._preview_audio_buf.close()
                self._preview_audio_buf = QBuffer()
                self._preview_audio_buf.setData(wav_bytes)
                self._preview_audio_buf.open(QIODevice.ReadOnly)
                self._preview_audio_out.setVolume(vol)
                self._preview_audio_player.setSourceDevice(self._preview_audio_buf, QUrl())
                self._preview_audio_player.play()
                self.statusBar().showMessage(f"Testing '{preset}' preset...")
        except Exception as e:
            log.warning("Test sound failed: %s", e)
            QMessageBox.warning(self, "Test Sound Error", f"Failed to play test sound:\n{e}")

    def _on_kb_overlay_toggled(self, checked: bool):
        self.kb_layout_cb.setEnabled(checked)
        self.kb_position_cb.setEnabled(checked)
        self.kb_desc_lbl.setEnabled(checked)

    def _on_kb_layout_changed(self, layout_name: str):
        desc = KEYBOARD_LAYOUTS.get(layout_name, {}).get("description", "")
        self.kb_desc_lbl.setText(desc)

    def _on_font_size_auto_toggled(self, checked: bool):
        self.font_size_sp.setEnabled(not checked)

    def _on_title_auto_toggled(self, checked: bool):
        self.title_edit.setEnabled(not checked)
        self._invalidate_preview_cache()
        self._schedule_preview_update()

    def _scan_input_dir(self):
        self._scan_directory(INPUT_DIR)

    def _scan_folder(self):
        folder = QFileDialog.getExistingDirectory(self, "Select Root Folder to Scan", INPUT_DIR)
        if folder:
            self._scan_directory(folder)

    def _scan_directory(self, root_dir: str):
        self._items.clear()
        self._checkbox_anchor = None
        if not os.path.isdir(root_dir):
            self.statusBar().showMessage(f"Folder not found: {root_dir}")
            self._refresh_table()
            return

        max_depth = self.depth_sp.value() if self.recurse_chk.isChecked() else 1
        found: List[FileItem] = []

        for dirpath, dirnames, filenames in os.walk(root_dir):
            rel = os.path.relpath(dirpath, root_dir)
            if rel == ".":
                depth = 1
            else:
                depth = rel.count(os.sep) + 2

            if depth > max_depth:
                dirnames.clear()
                continue

            dirnames[:] = [d for d in dirnames if d not in _SKIP_DIRS and not d.startswith(".")]

            for fname in sorted(filenames):
                ext = os.path.splitext(fname)[1].lower()
                if ext in SUPPORTED_EXTENSIONS:
                    fpath = os.path.join(dirpath, fname)
                    found.append(FileItem(path=fpath))

        self._items = found
        self._item_paths = {it.path for it in found}
        self._refresh_table()

        recurse_note = f" (depth ≤ {max_depth})" if self.recurse_chk.isChecked() else " (top-level only)"
        self.file_count_lbl.setText(f"{len(self._items)} file(s) found{recurse_note}")
        self.statusBar().showMessage(f"Found {len(self._items)} document(s) in {root_dir}{recurse_note}")

    def _add_files(self):
        ext_str = " ".join(f"*{e}" for e in sorted(SUPPORTED_EXTENSIONS))
        paths, _ = QFileDialog.getOpenFileNames(self, "Select Documents", "", f"Documents ({ext_str});;All Files (*)")
        for p in paths:
            if p not in self._item_paths:
                item = FileItem(path=p)
                self._items.append(item)
                self._item_paths.add(p)
        self._refresh_table()
        
    def _clear_list(self):
        self._items.clear()
        self._item_paths.clear()
        self._checkbox_anchor = None
        self._refresh_table()
        self._invalidate_preview_cache()
        self._schedule_preview_update()

    def _select_all(self):
        for it in self._items:
            it.checked = True
        self._checkbox_anchor = None
        self._refresh_table()

    def _deselect_all(self):
        for it in self._items:
            it.checked = False
        self._checkbox_anchor = None
        self._refresh_table()

    def _on_item_changed(self, item):
        row = item.row()
        col = item.column()
        if col == 0 and 0 <= row < len(self._items):
            new_state = (item.checkState() == Qt.CheckState.Checked)

            modifiers = QApplication.keyboardModifiers()
            if (modifiers & Qt.ShiftModifier
                    and self._checkbox_anchor is not None
                    and self._checkbox_anchor != row
                    and 0 <= self._checkbox_anchor < len(self._items)):
                anchor = self._checkbox_anchor
                lo = min(anchor, row)
                hi = max(anchor, row)

                self.table.blockSignals(True)
                for i in range(lo, hi + 1):
                    self._items[i].checked = new_state
                    chk_item = self.table.item(i, 0)
                    if chk_item is not None:
                        chk_item.setCheckState(
                            Qt.CheckState.Checked if new_state else Qt.CheckState.Unchecked
                        )
                self.table.blockSignals(False)
            else:
                self._items[row].checked = new_state
                self._checkbox_anchor = row

            self._invalidate_preview_cache()
            self._schedule_preview_update()
            
    def _on_table_context_menu(self, pos):
        item = self.table.itemAt(pos)
        if not item: return
        row = item.row()
        if row >= len(self._items): return
        
        menu = QMenu(self)
        export_action = menu.addAction("Export This File Only")
        action = menu.exec_(self.table.viewport().mapToGlobal(pos))
        
        if action == export_action:
            for it in self._items:
                it.checked = False
            self._items[row].checked = True
            self._checkbox_anchor = None
            self._refresh_table()
            self._start_export()

    def _refresh_table(self):
        with signals_blocked(self.table):
            self.table.setRowCount(len(self._items))
            for i, item in enumerate(self._items):
                chk = QTableWidgetItem()
                chk.setFlags(Qt.ItemFlag.ItemIsUserCheckable | Qt.ItemFlag.ItemIsEnabled)
                chk.setCheckState(
                    Qt.CheckState.Checked if item.checked else Qt.CheckState.Unchecked
                )
                self.table.setItem(i, 0, chk)

                try:
                    rel = os.path.relpath(item.path, CWD)
                    display_path = rel if not rel.startswith("..") else item.path
                except ValueError:
                    display_path = item.path
                path_item = QTableWidgetItem(display_path)
                path_item.setToolTip(item.path)
                self.table.setItem(i, 1, path_item)

                ext = os.path.splitext(item.path)[1].lower()
                lang = EXT_TO_LANGUAGE.get(ext, "Text")
                self.table.setItem(i, 2, QTableWidgetItem(lang))

                status_item = QTableWidgetItem(item.status.value)
                if item.status == ExportStatus.DONE:
                    status_item.setForeground(QColor("#50fa7b"))
                elif item.status == ExportStatus.FAILED:
                    status_item.setForeground(QColor("#ff5555"))
                elif item.status == ExportStatus.RENDERING:
                    status_item.setForeground(QColor("#8be9fd"))
                self.table.setItem(i, 3, status_item)

    def _start_export(self):
        if shutil.which("ffmpeg") is None:
            QMessageBox.critical(self, "FFmpeg Not Found", 
                                 "FFmpeg is not installed or not in your system PATH.\n"
                                 "Please install FFmpeg to export videos.")
            return

        checked = [it for it in self._items if it.checked]
        if not checked:
            QMessageBox.information(self, "Nothing selected", "Check at least one document to export.")
            return

        for it in checked:
            it.status = ExportStatus.PENDING
            it.output_path = None
            it.error = None
        self._refresh_table()

        self._export_queue = list(checked)
        self.export_btn.setEnabled(False)
        self.cancel_btn.setEnabled(True)
        self._export_next()

    def _export_next(self):
        if not self._export_queue:
            self.export_btn.setEnabled(True)
            self.cancel_btn.setEnabled(False)
            done = sum(1 for it in self._items if it.status == ExportStatus.DONE)
            failed = sum(1 for it in self._items if it.status == ExportStatus.FAILED)
            msg = f"Batch complete: {done} done"
            if failed:
                msg += f", {failed} failed"
            self.statusBar().showMessage(msg)
            self.progress_bar.setValue(100)
            return

        item = self._export_queue.pop(0)
        item.status = ExportStatus.RENDERING
        self._refresh_table()

        try:
            text = _read_text_file(item.path, clean=self.clean_text_chk.isChecked())
        except Exception as e:
            item.status = ExportStatus.FAILED
            item.error = str(e)
            self._refresh_table()
            self._on_item_failed(item, str(e))
            return

        if not text.strip():
            item.status = ExportStatus.FAILED
            item.error = "Empty file"
            self._refresh_table()
            self._on_item_failed(item, "Empty file")
            return

        ext = os.path.splitext(item.path)[1].lower()
        language = EXT_TO_LANGUAGE.get(ext, "Text")
        res_name = self.res_cb.currentText()
        w, h = RESOLUTIONS.get(res_name, (1920, 1080))

        _pad = self.padding_sp.value()
        _chrome = self.chrome_chk.isChecked()
        _ln = self.line_numbers_chk.isChecked()
        _chosen_font = self.font_family_cb.currentText()

        kb_overlay = None
        kb_h = 0
        if self.kb_overlay_chk.isChecked():
            layout_name = self.kb_layout_cb.currentText()
            kb_overlay = KeyboardOverlay(
                video_w=w, video_h=h, layout_name=layout_name,
                theme=THEMES.get(self.theme_cb.currentText(), THEMES["Dracula"]),
                max_height=(h - 2 * _pad) // 3,
                position=self._kb_position_key(),
                opacity=self.kb_opacity_sp.value(),
            )
            kb_h = kb_overlay.height_needed()

        if self.font_size_auto_chk.isChecked():
            font_size = TextRenderer.auto_font_size(
                lines_count=text.count("\n") + 1, width=w, height=h,
                text=text, font_family=_chosen_font, keyboard_h=kb_h,
                padding=_pad, show_window_chrome=_chrome, show_line_numbers=_ln,
            )
        else:
            font_size = self.font_size_sp.value()

        if self.title_auto_chk.isChecked():
            title = f"{os.path.basename(item.path)} - Text Editor"
        else:
            custom = self.title_edit.text().strip()
            title = custom if custom else f"{os.path.basename(item.path)} - Text Editor"

        renderer = TextRenderer(
            width=w, height=h, theme_name=self.theme_cb.currentText(),
            font_family=_chosen_font, font_size=font_size, title_text=title,
            language=language, keyboard_overlay=kb_overlay, padding=_pad,
            show_window_chrome=_chrome, show_line_numbers=_ln,
            bg_image_path=self._bg_image_path, total_lines=text.count("\n") + 1,
            cursor_glow=self.cursor_glow_chk.isChecked(),
            show_watermark=self.watermark_chk.isChecked(),
        )

        export_wpm = self.wpm_sp.value()
        if self.auto_speed_shorts_chk.isChecked():
            export_wpm = TypingAnimator.find_wpm_for_target_duration(
                text, 179.0, self.start_pause_sp.value(), self.end_pause_sp.value(), self.typo_rate_sp.value()
            )

        animator = TypingAnimator(
            text, wpm=export_wpm, start_pause=self.start_pause_sp.value(),
            end_pause=self.end_pause_sp.value(), typo_rate=self.typo_rate_sp.value()
        )

        base = os.path.splitext(os.path.basename(item.path))[0]
        output = os.path.join(OUTPUT_DIR, f"{base}.mp4")

        sound_gen = SimpleSoundGen(
            preset=self.sound_preset_cb.currentText(),
            stereo=self.binaural_chk.isChecked(),
            reverb_amt=self.reverb_amt_sp.value(),
        ) if self.sound_chk.isChecked() else None

        self._export_thread = QThread()
        self._export_worker = VideoExportWorker(
            text=text, output=output, renderer=renderer, animator=animator,
            fps=self.fps_sp.value(), sound_gen=sound_gen,
            volume=self.vol_sl.value() / 100.0,
            encoder_name=self.encoder_cb.currentText(),
            fade_in=self.fade_in_sp.value(), fade_out=self.fade_out_sp.value(),
        )
        self._export_worker.moveToThread(self._export_thread)
        
        self._export_thread.started.connect(self._export_worker.run)
        self._export_worker.progress.connect(self.progress_bar.setValue)
        self._export_worker.status.connect(self.statusBar().showMessage)
        self._export_worker.finished_ok.connect(lambda p: self._on_item_done(item, p))
        self._export_worker.error.connect(lambda e: self._on_item_failed(item, e))
        
        self._export_worker.finished.connect(self._on_exporter_thread_done)
        self._export_worker.finished.connect(self._export_thread.quit)
        self._export_worker.finished.connect(self._export_worker.deleteLater)
        self._export_thread.finished.connect(self._export_thread.deleteLater)
        
        self._export_thread.start()

    def _on_item_done(self, item: FileItem, path: str):
        item.status = ExportStatus.DONE
        item.output_path = path
        self._refresh_table()
        self._export_next()

    def _on_item_failed(self, item: FileItem, err: str):
        item.status = ExportStatus.FAILED
        item.error = err
        self._refresh_table()
        QMessageBox.critical(self, "Export Failed", 
                             f"Failed to export {os.path.basename(item.path)}:\n\n{err}")
        self._export_next()

    def _on_exporter_thread_done(self):
        self._export_thread = None
        self._export_worker = None

    def _cancel_export(self):
        if self._export_worker:
            self._export_worker.cancel()
        self._export_queue.clear()

    def closeEvent(self, event):
        if self._export_thread and self._export_thread.isRunning():
            self._cancel_export()
            if not self._export_thread.wait(5000):
                log.warning("Export thread did not finish in time, terminating.")
                self._export_thread.terminate()
        self._save_settings()
        super().closeEvent(event)

    def _connect_settings_signals(self):
        self.theme_cb.currentTextChanged.connect(self._auto_save_settings)
        self.theme_cb.currentTextChanged.connect(self._invalidate_preview_cache)
        self.theme_cb.currentTextChanged.connect(self._schedule_preview_update)
        self.res_cb.currentTextChanged.connect(self._auto_save_settings)
        self.res_cb.currentTextChanged.connect(self._invalidate_preview_cache)
        self.res_cb.currentTextChanged.connect(self._schedule_preview_update)
        self.wpm_sp.valueChanged.connect(self._auto_save_settings)
        self.wpm_sp.valueChanged.connect(self._invalidate_preview_cache)
        self.wpm_sp.valueChanged.connect(self._schedule_preview_update)
        self.auto_speed_shorts_chk.toggled.connect(self._auto_save_settings)
        self.auto_speed_shorts_chk.toggled.connect(self._invalidate_preview_cache)
        self.auto_speed_shorts_chk.toggled.connect(self._schedule_preview_update)
        self.fps_sp.valueChanged.connect(self._auto_save_settings)
        self.fps_sp.valueChanged.connect(self._schedule_preview_update)
        self.start_pause_sp.valueChanged.connect(self._auto_save_settings)
        self.start_pause_sp.valueChanged.connect(self._invalidate_preview_cache)
        self.start_pause_sp.valueChanged.connect(self._schedule_preview_update)
        self.end_pause_sp.valueChanged.connect(self._auto_save_settings)
        self.end_pause_sp.valueChanged.connect(self._invalidate_preview_cache)
        self.end_pause_sp.valueChanged.connect(self._schedule_preview_update)
        self.font_family_cb.currentTextChanged.connect(self._auto_save_settings)
        self.font_family_cb.currentTextChanged.connect(self._invalidate_preview_cache)
        self.font_family_cb.currentTextChanged.connect(self._schedule_preview_update)
        self.font_size_auto_chk.toggled.connect(self._auto_save_settings)
        self.font_size_auto_chk.toggled.connect(self._invalidate_preview_cache)
        self.font_size_auto_chk.toggled.connect(self._schedule_preview_update)
        self.font_size_sp.valueChanged.connect(self._auto_save_settings)
        self.font_size_sp.valueChanged.connect(self._invalidate_preview_cache)
        self.font_size_sp.valueChanged.connect(self._schedule_preview_update)
        self.sound_chk.toggled.connect(self._auto_save_settings)
        self.vol_sl.valueChanged.connect(self._auto_save_settings)
        self.sound_preset_cb.currentTextChanged.connect(self._auto_save_settings)
        self.binaural_chk.toggled.connect(self._auto_save_settings)
        self.reverb_amt_sp.valueChanged.connect(self._auto_save_settings)
        self.kb_overlay_chk.toggled.connect(self._auto_save_settings)
        self.kb_overlay_chk.toggled.connect(self._invalidate_preview_cache)
        self.kb_overlay_chk.toggled.connect(self._schedule_preview_update)
        self.kb_layout_cb.currentTextChanged.connect(self._auto_save_settings)
        self.kb_layout_cb.currentTextChanged.connect(self._invalidate_preview_cache)
        self.kb_layout_cb.currentTextChanged.connect(self._schedule_preview_update)
        self.kb_position_cb.currentTextChanged.connect(self._auto_save_settings)
        self.kb_position_cb.currentTextChanged.connect(self._invalidate_preview_cache)
        self.kb_position_cb.currentTextChanged.connect(self._schedule_preview_update)
        self.kb_opacity_sp.valueChanged.connect(self._auto_save_settings)
        self.kb_opacity_sp.valueChanged.connect(self._invalidate_preview_cache)
        self.kb_opacity_sp.valueChanged.connect(self._schedule_preview_update)
        self.recurse_chk.toggled.connect(self._auto_save_settings)
        self.depth_sp.valueChanged.connect(self._auto_save_settings)
        self.title_auto_chk.toggled.connect(self._auto_save_settings)
        self.title_edit.textChanged.connect(self._auto_save_settings)
        self.title_edit.textChanged.connect(self._invalidate_preview_cache)
        self.title_edit.textChanged.connect(self._schedule_preview_update)
        self.padding_sp.valueChanged.connect(self._auto_save_settings)
        self.padding_sp.valueChanged.connect(self._invalidate_preview_cache)
        self.padding_sp.valueChanged.connect(self._schedule_preview_update)
        self.chrome_chk.toggled.connect(self._auto_save_settings)
        self.chrome_chk.toggled.connect(self._invalidate_preview_cache)
        self.chrome_chk.toggled.connect(self._schedule_preview_update)
        self.line_numbers_chk.toggled.connect(self._auto_save_settings)
        self.line_numbers_chk.toggled.connect(self._invalidate_preview_cache)
        self.line_numbers_chk.toggled.connect(self._schedule_preview_update)
        self.bg_edit.textChanged.connect(self._on_bg_edit_changed)
        self.typo_rate_sp.valueChanged.connect(self._auto_save_settings)
        self.typo_rate_sp.valueChanged.connect(self._invalidate_preview_cache)
        self.typo_rate_sp.valueChanged.connect(self._schedule_preview_update)
        self.encoder_cb.currentTextChanged.connect(self._auto_save_settings)
        self.cursor_glow_chk.toggled.connect(self._auto_save_settings)
        self.cursor_glow_chk.toggled.connect(self._invalidate_preview_cache)
        self.cursor_glow_chk.toggled.connect(self._schedule_preview_update)
        self.watermark_chk.toggled.connect(self._auto_save_settings)
        self.watermark_chk.toggled.connect(self._invalidate_preview_cache)
        self.watermark_chk.toggled.connect(self._schedule_preview_update)
        self.fade_in_sp.valueChanged.connect(self._auto_save_settings)
        self.fade_out_sp.valueChanged.connect(self._auto_save_settings)
        self.clean_text_chk.toggled.connect(self._auto_save_settings)
        self.clean_text_chk.toggled.connect(self._invalidate_preview_cache)
        self.clean_text_chk.toggled.connect(self._schedule_preview_update)

    def _auto_save_settings(self, *_args):
        if self._loading_settings: return
        if not hasattr(self, "_save_timer"):
            self._save_timer = QTimer(self)
            self._save_timer.setSingleShot(True)
            self._save_timer.setInterval(300)
            self._save_timer.timeout.connect(self._save_settings)
        self._save_timer.start()

    def _save_settings(self):
        try:
            data = {
                "theme": self.theme_cb.currentText(), "resolution": self.res_cb.currentText(),
                "wpm": self.wpm_sp.value(), "auto_speed_shorts": self.auto_speed_shorts_chk.isChecked(),
                "fps": self.fps_sp.value(), "start_pause": self.start_pause_sp.value(),
                "end_pause": self.end_pause_sp.value(), "font_family": self.font_family_cb.currentText(),
                "font_size_auto": self.font_size_auto_chk.isChecked(), "font_size": self.font_size_sp.value(),
                "sound_enabled": self.sound_chk.isChecked(), "volume": self.vol_sl.value(),
                "sound_preset": self.sound_preset_cb.currentText(), "binaural": self.binaural_chk.isChecked(),
                "reverb_amt": self.reverb_amt_sp.value(), "kb_overlay": self.kb_overlay_chk.isChecked(),
                "kb_layout": self.kb_layout_cb.currentText(), "kb_position": self.kb_position_cb.currentText(),
                "kb_opacity": self.kb_opacity_sp.value(), "recursive": self.recurse_chk.isChecked(),
                "depth": self.depth_sp.value(), "title_auto": self.title_auto_chk.isChecked(),
                "title_custom": self.title_edit.text(), "padding": self.padding_sp.value(),
                "show_chrome": self.chrome_chk.isChecked(), "show_line_numbers": self.line_numbers_chk.isChecked(),
                "bg_image_path": self._bg_image_path, "typo_rate": self.typo_rate_sp.value(),
                "encoder": self.encoder_cb.currentText(), "cursor_glow": self.cursor_glow_chk.isChecked(),
                "watermark": self.watermark_chk.isChecked(), "fade_in": self.fade_in_sp.value(),
                "fade_out": self.fade_out_sp.value(), "clean_text": self.clean_text_chk.isChecked(),
            }
            with open(SETTINGS_FILE, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2, ensure_ascii=False)
        except Exception as e:
            log.warning("Failed to save settings: %s", e)

    def _load_settings(self):
        if not os.path.isfile(SETTINGS_FILE): return
        try:
            with open(SETTINGS_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
        except (json.JSONDecodeError, OSError):
            return

        self._loading_settings = True
        try:
            if "theme" in data and data["theme"] in THEMES: self.theme_cb.setCurrentText(data["theme"])
            if "resolution" in data and data["resolution"] in RESOLUTIONS: self.res_cb.setCurrentText(data["resolution"])
            if "wpm" in data: self.wpm_sp.setValue(int(data["wpm"]))
            if "auto_speed_shorts" in data: self.auto_speed_shorts_chk.setChecked(bool(data["auto_speed_shorts"]))
            if "fps" in data: self.fps_sp.setValue(int(data["fps"]))
            if "start_pause" in data: self.start_pause_sp.setValue(float(data["start_pause"]))
            if "end_pause" in data: self.end_pause_sp.setValue(float(data["end_pause"]))
            if "sound_enabled" in data: self.sound_chk.setChecked(bool(data["sound_enabled"]))
            if "volume" in data: self.vol_sl.setValue(int(data["volume"]))
            if "sound_preset" in data and data["sound_preset"] in SOUND_PRESETS: self.sound_preset_cb.setCurrentText(data["sound_preset"])
            if "binaural" in data: self.binaural_chk.setChecked(bool(data["binaural"]))
            if "reverb_amt" in data: self.reverb_amt_sp.setValue(float(data["reverb_amt"]))
            if "kb_overlay" in data: self.kb_overlay_chk.setChecked(bool(data["kb_overlay"]))
            if "kb_layout" in data and data["kb_layout"] in KEYBOARD_LAYOUTS: self.kb_layout_cb.setCurrentText(data["kb_layout"])
            
            kb_pos = data.get("kb_position")
            if kb_pos:
                # Check if it's UI text or internal key
                idx = self.kb_position_cb.findText(kb_pos)
                if idx >= 0:
                    self.kb_position_cb.setCurrentIndex(idx)
                else:
                    # Try reverse lookup
                    for ui_text, key in self._KB_POS_MAP.items():
                        if key == kb_pos:
                            self.kb_position_cb.setCurrentText(ui_text)
                            break

            if "kb_opacity" in data: self.kb_opacity_sp.setValue(float(data["kb_opacity"]))
            if "font_family" in data:
                idx = self.font_family_cb.findText(data["font_family"])
                if idx >= 0: self.font_family_cb.setCurrentIndex(idx)
            if "font_size_auto" in data: self.font_size_auto_chk.setChecked(bool(data["font_size_auto"]))
            if "font_size" in data: self.font_size_sp.setValue(int(data["font_size"]))
            if "recursive" in data: self.recurse_chk.setChecked(bool(data["recursive"]))
            if "depth" in data: self.depth_sp.setValue(int(data["depth"]))
            if "title_auto" in data: self.title_auto_chk.setChecked(bool(data["title_auto"]))
            if "title_custom" in data: self.title_edit.setText(str(data["title_custom"]))
            if "padding" in data: self.padding_sp.setValue(int(data["padding"]))
            if "show_chrome" in data: self.chrome_chk.setChecked(bool(data["show_chrome"]))
            if "show_line_numbers" in data: self.line_numbers_chk.setChecked(bool(data["show_line_numbers"]))
            if "bg_image_path" in data:
                self._bg_image_path = str(data["bg_image_path"])
                self.bg_edit.setText(self._bg_image_path)
            if "typo_rate" in data: self.typo_rate_sp.setValue(float(data["typo_rate"]))
            if "encoder" in data and data["encoder"] in ENCODERS: self.encoder_cb.setCurrentText(data["encoder"])
            if "cursor_glow" in data: self.cursor_glow_chk.setChecked(bool(data["cursor_glow"]))
            if "watermark" in data: self.watermark_chk.setChecked(bool(data["watermark"]))
            if "fade_in" in data: self.fade_in_sp.setValue(float(data["fade_in"]))
            if "fade_out" in data: self.fade_out_sp.setValue(float(data["fade_out"]))
            if "clean_text" in data: self.clean_text_chk.setChecked(bool(data["clean_text"]))
        finally:
            self._loading_settings = False

    def _kb_position_key(self) -> str:
        return self._KB_POS_MAP.get(self.kb_position_cb.currentText(), "bottom_center")

    _KB_POS_MAP = {
        "Bottom Center": "bottom_center", "Bottom Right": "bottom_right",
        "Bottom Left": "bottom_left", "Center Left": "center_left",
        "Center Right": "center_right", "Top Center": "top_center",
        "Top Right": "top_right", "Top Left": "top_left",
    }

    def _invalidate_preview_cache(self, *_args):
        self._cached_preview_key = None
        self._cached_preview_code = None
        self._cached_preview_renderer = None
        self._cached_preview_animator = None
        self._preview_scratch = None
        self._cached_preview_pcm = None

    def _update_preview(self):
        if not hasattr(self, '_preview_label'): return
        
        checked_items = [it for it in self._items if it.checked]
        if checked_items:
            item = checked_items[0]
            text_key = (item.path, self.clean_text_chk.isChecked())
            if self._cached_text_key != text_key:
                try:
                    self._cached_text = _read_text_file(item.path, clean=self.clean_text_chk.isChecked())
                except Exception:
                    self._cached_text = _SAMPLE_TEXT
                self._cached_text_key = text_key
            text = self._cached_text
            title = os.path.basename(item.path)
        else:
            text_key = ("_SAMPLE", self.clean_text_chk.isChecked())
            if self._cached_text_key != text_key:
                self._cached_text = _SAMPLE_TEXT
                self._cached_text_key = text_key
            text = self._cached_text
            title = "preview.txt"

        res_name = self.res_cb.currentText()
        w, h = RESOLUTIONS.get(res_name, (1920, 1080))
        
        _pad = self.padding_sp.value()
        _chrome = self.chrome_chk.isChecked()
        _ln = self.line_numbers_chk.isChecked()
        _font = self.font_family_cb.currentText()
        
        kb_overlay = None
        kb_h = 0
        if self.kb_overlay_chk.isChecked():
            layout_name = self.kb_layout_cb.currentText()
            kb_overlay = KeyboardOverlay(
                video_w=w, video_h=h, layout_name=layout_name,
                theme=THEMES.get(self.theme_cb.currentText(), THEMES["Dracula"]),
                max_height=(h - 2 * _pad) // 3,
                position=self._kb_position_key(),
                opacity=self.kb_opacity_sp.value(),
            )
            kb_h = kb_overlay.height_needed()

        if self.font_size_auto_chk.isChecked():
            font_size = TextRenderer.auto_font_size(
                lines_count=text.count("\n") + 1, width=w, height=h,
                text=text, font_family=_font, keyboard_h=kb_h,
                padding=_pad, show_window_chrome=_chrome, show_line_numbers=_ln,
            )
        else:
            font_size = self.font_size_sp.value()

        if self.title_auto_chk.isChecked():
            title_str = f"{title} - Text Editor"
        else:
            custom = self.title_edit.text().strip()
            title_str = custom if custom else f"{title} - Text Editor"

        # Detect language from the selected file's extension
        if checked_items:
            ext = os.path.splitext(item.path)[1].lower()
            preview_language = EXT_TO_LANGUAGE.get(ext, "Text")
        else:
            preview_language = "Text"

        cache_key = (
            w, h, self.theme_cb.currentText(), _font, font_size, 
            _pad, _chrome, _ln, title_str, self.kb_overlay_chk.isChecked(),
            self.kb_layout_cb.currentText(), self.kb_position_cb.currentText(),
            self.kb_opacity_sp.value(), self._bg_image_path, self.wpm_sp.value(),
            self.cursor_glow_chk.isChecked(), self.watermark_chk.isChecked(),
            self.auto_speed_shorts_chk.isChecked(), self.start_pause_sp.value(),
            self.end_pause_sp.value(), self.typo_rate_sp.value(),
            preview_language,  # Added language to cache key
        )
        
        needs_rebuild = False
        if self._cached_preview_animator is None or self._cached_preview_animator.text != text:
            needs_rebuild = True
        if cache_key != self._cached_preview_key:
            needs_rebuild = True
            
        if needs_rebuild:
            self._cached_preview_key = cache_key
            
            renderer = TextRenderer(
                width=w, height=h, theme_name=self.theme_cb.currentText(),
                font_family=_font, font_size=font_size, title_text=title_str,
                language=preview_language,  # Use detected language
                keyboard_overlay=kb_overlay, padding=_pad,
                show_window_chrome=_chrome, show_line_numbers=_ln,
                bg_image_path=self._bg_image_path, total_lines=text.count("\n") + 1,
                cursor_glow=self.cursor_glow_chk.isChecked(),
                show_watermark=self.watermark_chk.isChecked(),
            )
            
            export_wpm = self.wpm_sp.value()
            if self.auto_speed_shorts_chk.isChecked():
                export_wpm = TypingAnimator.find_wpm_for_target_duration(
                    text, 179.0, self.start_pause_sp.value(), self.end_pause_sp.value(), self.typo_rate_sp.value()
                )

            animator = TypingAnimator(
                text, wpm=export_wpm, start_pause=self.start_pause_sp.value(),
                end_pause=self.end_pause_sp.value(), typo_rate=self.typo_rate_sp.value()
            )
            
            self._cached_preview_renderer = renderer
            self._cached_preview_animator = animator
            self._preview_scratch = QImage(w, h, QImage.Format_RGB32)
            
            dur = animator.duration()
            self._preview_duration_lbl.setText(f"Duration: {int(dur // 60):02d}:{int(dur % 60):02d}")
            self._stats_lbl.setText(f"Chars: {len(text)} | WPM: {export_wpm} | Font: {font_size}px | Lang: {preview_language}")

        renderer = self._cached_preview_renderer
        animator = self._cached_preview_animator
        
        if not renderer or not animator:
            return

        t = animator.duration() * self._preview_progress
        nv = animator.visible_at(t)
        
        cur_vis = True
        if nv > 0:
            idx = bisect.bisect_right(animator._timestamps, t)
            if idx > 0:
                last_ts = animator.timeline[idx - 1][0]
                if t - last_ts > 0.25:
                    cur_vis = (int((t - last_ts) / renderer.CURSOR_BLINK) % 2) == 0

        active_char, key_flash = animator.active_key_at(t)
        
        img = renderer.render_frame(
            animator.display_chars, nv, cur_vis, target=self._preview_scratch,
            active_char=active_char, key_flash=key_flash,
        )
        
        self._preview_label.set_preview_image(img)
        
        if not self._preview_animating:
            self._frame_slider.blockSignals(True)
            self._frame_slider.setValue(int(self._preview_progress * 100))
            self._frame_slider.blockSignals(False)
            
        self._frame_lbl.setText(f"{int(self._preview_progress * 100)}% | {t:.2f}s / {animator.duration():.2f}s")

    def _schedule_preview_update(self):
        if self._loading_settings: return
        if not hasattr(self, "_preview_update_timer"):
            self._preview_update_timer = QTimer(self)
            self._preview_update_timer.setSingleShot(True)
            self._preview_update_timer.setInterval(400)
            self._preview_update_timer.timeout.connect(self._update_preview)
        self._preview_update_timer.start()

    def _on_preview_slider(self, value):
        self._stop_preview_animation()
        self._preview_progress = value / 100.0
        self._update_preview()

    def _preview_prev(self):
        self._stop_preview_animation()
        self._preview_progress = max(0, self._preview_progress - 0.05)
        self._update_preview()

    def _preview_next(self):
        self._stop_preview_animation()
        self._preview_progress = min(1.0, self._preview_progress + 0.05)
        self._update_preview()

    def _toggle_preview_animation(self):
        if self._preview_animating:
            self._stop_preview_animation()
        else:
            self._preview_animating = True
            self._play_btn.setText("⏸ Pause")
            self._last_preview_t = _time.perf_counter()
            if self._cached_preview_animator and self._preview_anim_t >= self._cached_preview_animator.duration():
                self._preview_anim_t = 0.0
                self._preview_progress = 0.0
            self._update_preview()
            if self._cached_preview_animator is not None:
                self._preview_anim_t = (self._cached_preview_animator.duration() * self._preview_progress)
                if self.sound_chk.isChecked():
                    try:
                        if self._cached_preview_pcm is None:
                            preset = self.sound_preset_cb.currentText()
                            vol = self.vol_sl.value() / 100.0
                            stereo = self.binaural_chk.isChecked()
                            reverb_amt = self.reverb_amt_sp.value()
                            sound_gen = SimpleSoundGen(preset=preset, stereo=stereo, reverb_amt=reverb_amt)
                            timestamps = self._cached_preview_animator.char_timestamps()
                            # Limit to 30 seconds to prevent UI freeze on large files
                            max_t = 30.0
                            timestamps = [ts for ts in timestamps if ts[0] < max_t]
                            self._cached_preview_pcm = sound_gen.generate_pcm(timestamps, vol)
                            self._cached_preview_pcm_sr = sound_gen.sr
                            self._cached_preview_pcm_channels = 2 if stereo else 1
                        
                        if self._cached_preview_pcm is not None and len(self._cached_preview_pcm) > 0:
                            wav_bytes = _pcm_to_wav_bytes(self._cached_preview_pcm, self._cached_preview_pcm_sr, self._cached_preview_pcm_channels)
                            if self._preview_audio_buf is not None:
                                self._preview_audio_buf.close()
                            self._preview_audio_buf = QBuffer()
                            self._preview_audio_buf.setData(wav_bytes)
                            self._preview_audio_buf.open(QIODevice.ReadOnly)
                            self._preview_audio_out.setVolume(self.vol_sl.value() / 100.0)
                            self._preview_audio_player.setSourceDevice(self._preview_audio_buf, QUrl())
                            self._preview_audio_player.setPosition(int(self._preview_anim_t * 1000))
                            self._preview_audio_player.play()
                    except Exception as e:
                        log.warning("Preview audio synthesis failed: %s", e)
                self._preview_timer.start()

    def _advance_preview_animation(self):
        now = _time.perf_counter()
        if not hasattr(self, '_last_preview_t'):
            self._last_preview_t = now
        dt = now - self._last_preview_t
        self._last_preview_t = now
        
        self._preview_anim_t += dt
        if self._cached_preview_animator is None:
            self._stop_preview_animation()
            return
        total = self._cached_preview_animator.duration()
        if self._preview_anim_t >= total:
            self._preview_anim_t = total
            self._stop_preview_animation()
        self._preview_progress = min(1.0, self._preview_anim_t / total)
        self._update_preview()

    def _stop_preview_animation(self):
        self._preview_animating = False
        self._preview_timer.stop()
        self._play_btn.setText("▶ Animate")
        if self._preview_audio_player is not None:
            self._preview_audio_player.stop()
        if self._preview_audio_buf is not None:
            self._preview_audio_buf.close()
            self._preview_audio_buf = None


# =====================================================================
# 9. APPLICATION ENTRY POINT
# =====================================================================

STYLE = """
QMainWindow, QDialog { background: #1e1e2e; }
QGroupBox {
    color: #cdd6f4; font-weight: bold; font-size: 13px;
    border: 1px solid #45475a; border-radius: 8px;
    margin-top: 12px; padding-top: 16px;
}
QGroupBox::title { subcontrol-origin: margin; left: 12px; }
QLabel { color: #cdd6f4; }
QTableWidget {
    background: #181825; color: #cdd6f4; gridline-color: #313244;
    border: 1px solid #45475a; border-radius: 6px;
    selection-background-color: #45475a;
}
QHeaderView::section {
    background: #313244; color: #cdd6f4; padding: 6px;
    border: none; font-weight: bold;
}
QComboBox, QSpinBox, QDoubleSpinBox, QLineEdit {
    background: #313244; color: #cdd6f4; border: 1px solid #45475a;
    border-radius: 4px; padding: 4px 8px; min-height: 24px;
}
QComboBox::drop-down { border: none; }
QComboBox QAbstractItemView {
    background: #313244; color: #cdd6f4;
    selection-background-color: #45475a;
}
QCheckBox { color: #cdd6f4; spacing: 6px; }
QCheckBox::indicator {
    width: 18px; height: 18px; border-radius: 4px;
    border: 2px solid #45475a; background: #313244;
}
QCheckBox::indicator:checked { background: #89b4fa; border-color: #89b4fa; }
QPushButton {
    background: #313244; color: #cdd6f4; border: 1px solid #45475a;
    border-radius: 6px; padding: 6px 16px; font-size: 13px;
}
QPushButton:hover { background: #45475a; }
QPushButton:disabled { color: #585b70; }
QPushButton#primaryBtn {
    background: #89b4fa; color: #1e1e2e; font-weight: bold;
    border: none; padding: 8px 24px; font-size: 14px;
}
QPushButton#primaryBtn:hover { background: #74c7ec; }
QPushButton#primaryBtn:disabled { background: #45475a; color: #585b70; }
QPushButton#previewBtn {
    background: #a6e3a1; color: #1e1e2e; font-weight: bold;
    border: none; padding: 6px 14px; font-size: 12px;
}
QPushButton#previewBtn:hover { background: #94e2d5; }
QPushButton#previewBtn:disabled { background: #45475a; color: #585b70; }
QProgressBar {
    background: #313244; border: none; border-radius: 4px;
    text-align: center; color: #cdd6f4; min-height: 20px;
}
QProgressBar::chunk { background: #89b4fa; border-radius: 4px; }
QTabWidget::pane {
    border: 1px solid #45475a; border-radius: 6px;
    background: #1e1e2e; top: -1px;
}
QTabBar::tab {
    background: #313244; color: #a6adc8; padding: 8px 18px;
    border: 1px solid #45475a; border-bottom: none;
    border-top-left-radius: 6px; border-top-right-radius: 6px;
    font-size: 12px; font-weight: bold; margin-right: 2px;
}
QTabBar::tab:selected {
    background: #1e1e2e; color: #cdd6f4; border-bottom: 2px solid #89b4fa;
}
QTabBar::tab:hover:!selected {
    background: #45475a; color: #cdd6f4;
}
QStatusBar { color: #a6adc8; font-size: 12px; }
QSplitter::handle {
    background: #45475a;
    border: 1px solid #181825;
    border-radius: 2px;
}
"""

def main():
    app = QApplication(sys.argv)
    app.setStyle("Fusion")
    app.setStyleSheet(STYLE)

    pal = QPalette()
    pal.setColor(QPalette.Window, QColor("#1e1e2e"))
    pal.setColor(QPalette.WindowText, QColor("#cdd6f4"))
    pal.setColor(QPalette.Base, QColor("#313244"))
    pal.setColor(QPalette.Text, QColor("#cdd6f4"))
    pal.setColor(QPalette.Button, QColor("#313244"))
    pal.setColor(QPalette.ButtonText, QColor("#cdd6f4"))
    pal.setColor(QPalette.Highlight, QColor("#89b4fa"))
    pal.setColor(QPalette.HighlightedText, QColor("#1e1e2e"))
    app.setPalette(pal)

    win = MainWindow()
    win.resize(1000, 800)
    win.show()
    return app.exec()


if __name__ == "__main__":
    sys.exit(main())