import asyncio
import logging
import math
import os
import random
import json
import base64
import shutil
import sqlite3
import datetime
import time
import uuid
import glob
import hmac
import hashlib
import urllib.parse
import re
from typing import Dict, Optional, List, Set, Tuple
from dataclasses import dataclass, field
from collections import deque, defaultdict
from concurrent.futures import ThreadPoolExecutor

import requests
import yt_dlp

from aiogram import Bot, Dispatcher, types, F
from aiogram.filters import Command, StateFilter
from aiogram.types import (
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    WebAppInfo,
    FSInputFile,
    KeyboardButton,
    ReplyKeyboardMarkup,
)
from aiogram.exceptions import TelegramForbiddenError, TelegramBadRequest
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.storage.memory import MemoryStorage

from aiohttp import web


# ==================== SETTINGS ====================

def env_flag(name: str, default: str = "0") -> bool:
    return os.getenv(name, default).strip() == "1"


BOT_TOKEN = os.getenv("BOT_TOKEN", "").strip()
LASTFM_API_KEY = os.getenv("LASTFM_API_KEY", "").strip()

if not BOT_TOKEN or not LASTFM_API_KEY:
    raise RuntimeError("Set BOT_TOKEN and LASTFM_API_KEY environment variables")

APP_VERSION = "20260803-2"

WEBAPP_URL = os.getenv(
    "WEBAPP_URL",
    f"https://sorukoma.github.io/QuasWave/index.html?v={APP_VERSION}"
).strip()

EXTERNAL_URL = os.getenv("EXTERNAL_URL", "http://127.0.0.1:8080").strip().rstrip("/")
WEBAPP_ORIGIN = os.getenv("WEBAPP_ORIGIN", "https://sorukoma.github.io").strip()

CORS_ALLOW_ALL = env_flag("CORS_ALLOW_ALL")
DEV_ALLOW_EXPLICIT_USER_ID = env_flag("DEV_ALLOW_EXPLICIT_USER_ID")
DEV_ALLOW_OPEN_AUDIO = env_flag("DEV_ALLOW_OPEN_AUDIO")

DB_PATH = os.getenv("DB_PATH", "quaswave.db").strip()
AUDIO_CACHE_DIR = os.getenv("AUDIO_CACHE_DIR", "audio_cache").strip()
DOWNLOAD_DIR = os.getenv("DOWNLOAD_DIR", "downloads").strip()

REACTIONS_PAGE_SIZE = 10
NEGATIVE_HARD_THRESHOLD = 0.85
MAX_TEXT_LEN = 200

AUDIO_SIGN_SECRET = hashlib.sha256(BOT_TOKEN.encode("utf-8")).digest()
AUDIO_URL_TTL_SECONDS = int(os.getenv("AUDIO_URL_TTL_SECONDS", str(6 * 3600)).strip())
INIT_DATA_MAX_AGE = int(os.getenv("INIT_DATA_MAX_AGE", str(7 * 24 * 3600)).strip())
WEBAPP_AUTH_TTL_SECONDS = int(os.getenv("WEBAPP_AUTH_TTL_SECONDS", str(30 * 24 * 3600)).strip())

DOWNLOAD_TOTAL_TIMEOUT = int(os.getenv("DOWNLOAD_TOTAL_TIMEOUT", "90").strip())
FAILED_TRACK_TTL = int(os.getenv("FAILED_TRACK_TTL", str(10 * 60)).strip())

GLOBAL_POOL_TTL = int(os.getenv("GLOBAL_POOL_TTL", str(15 * 60)).strip())
GLOBAL_POOL_SEEDS = int(os.getenv("GLOBAL_POOL_SEEDS", "40").strip())
GLOBAL_SEEDS_PER_USER = int(os.getenv("GLOBAL_SEEDS_PER_USER", "2").strip())
GLOBAL_DIRECT_FALLBACK = int(os.getenv("GLOBAL_DIRECT_FALLBACK", "30").strip())

PLAYED_HARD_LIMIT = int(os.getenv("PLAYED_HARD_LIMIT", "120").strip())
PLAYED_SOFT_LIMIT = int(os.getenv("PLAYED_SOFT_LIMIT", "500").strip())
SCORE_JITTER = float(os.getenv("SCORE_JITTER", "0.25").strip())

ADMIN_USER_IDS = {
    int(x.strip())
    for x in os.getenv("ADMIN_USER_IDS", "6535315030").split(",")
    if x.strip().isdigit()
}
ADMIN_GETCHAT_LIMIT = 30

YT_PLAYER_CLIENTS = [
    item.strip()
    for item in os.getenv("YT_PLAYER_CLIENTS", "web_embedded,tv_embedded,android,web").split(",")
    if item.strip()
]

AGE_GATE_PATTERNS = [
    item.strip().lower()
    for item in os.getenv(
        "AGE_GATE_PATTERNS",
        "sign in to confirm your age,confirm your age,age-restricted,"
        "inappropriate for some users,login required,video unavailable"
    ).split(",")
    if item.strip()
]

DOWNLOAD_SEMAPHORE: Optional[asyncio.Semaphore] = None

DOWNLOAD_EXECUTOR = ThreadPoolExecutor(max_workers=int(os.getenv("DOWNLOAD_WORKERS", "3").strip()))
LASTFM_EXECUTOR = ThreadPoolExecutor(max_workers=int(os.getenv("LASTFM_WORKERS", "8").strip()))
SEARCH_EXECUTOR = ThreadPoolExecutor(max_workers=int(os.getenv("SEARCH_WORKERS", "2").strip()))

LASTFM_CACHE: Dict[str, tuple] = {}
LASTFM_CACHE_TTL = int(os.getenv("LASTFM_CACHE_TTL", str(6 * 3600)).strip())
LASTFM_SIMILAR_CACHE_TTL = int(os.getenv("LASTFM_SIMILAR_CACHE_TTL", str(2 * 3600)).strip())

USER_ACTION_LOCKS: Dict[int, asyncio.Lock] = {}
USER_STATE_LAST_SEEN: Dict[int, float] = {}
PRELOAD_TASKS: Dict[int, asyncio.Task] = {}

RATE_LIMIT_STATE = defaultdict(list)
BOT_RATE_STATE = defaultdict(list)

RATE_LIMITS = {
    "/api/state": (20, 10),
    "/api/settings": (10, 10),
    "/api/next_track": (8, 10),
    "/api/like": (10, 10),
    "/api/unlike": (10, 10),
    "/api/dislike": (10, 10),
    "/api/likes": (20, 10),
    "/api/search_tracks": (15, 10),
    "/api/search_artists": (15, 10),
    "/api/search_tags": (15, 10),
    "/api/send_track": (5, 30),
    "/api/start_track": (4, 10),
    "/api/start_artist": (4, 10),
    "/api/start_liked_playlist": (4, 10),
    "/api/start_likes_wave": (4, 10),
    "/api/start_global_wave": (4, 10),
    "/api/start_tag": (4, 10),
}

AGE_GATE_URL_CACHE: Dict[str, float] = {}
AGE_GATE_TTL = 6 * 3600

TAG_CACHE: Dict[str, List[str]] = {}
TAG_DIVERSIFY_HEAD = 16
TAG_FETCH_TIMEOUT = 1.5
TAG_SEMAPHORE_LIMIT = 4

GLOBAL_POOL: Dict[str, object] = {
    "ts": 0.0,
    "candidates": [],
}
GLOBAL_POOL_LOCK = asyncio.Lock()

CANON_STOP_WORDS = {
    "remastered", "remaster", "radioedit", "singleversion",
    "explicit", "clean", "mono", "stereo", "bonus",
    "deluxe", "edit", "version", "master", "mix",
}

TAG_DICT = {
    "вичхаус": "witch house",
    "витчхаус": "witch house",
    "техно": "techno",
    "эмбиент": "ambient",
    "хаус": "house",
    "транс": "trance",
    "драм-н-бейс": "drum and bass",
    "драмнбейс": "drum and bass",
    "дабстеп": "dubstep",
    "лофай": "lofi",
    "лоу-фай": "lofi",
    "фонк": "phonk",
    "вейпорвейв": "vaporwave",
    "синтвейв": "synthwave",
    "дарквейв": "darkwave",
    "колдвейв": "coldwave",
    "пост-панк": "post-punk",
    "постпанк": "post-punk",
    "шугейз": "shoegaze",
    "индастриал": "industrial",
    "готик": "gothic",
    "нью-вейв": "new wave",
    "ньювейв": "new wave",
    "панк": "punk",
    "метал": "metal",
    "блэк-метал": "black metal",
    "блэкметал": "black metal",
    "дэт-метал": "death metal",
    "дэтметал": "death metal",
    "дум": "doom",
    "стоунер": "stoner",
    "хардкор": "hardcore",
    "эмо": "emo",
    "инди": "indie",
    "альтернатива": "alternative",
    "гранж": "grunge",
    "фолк": "folk",
    "джаз": "jazz",
    "хип-хоп": "hip hop",
    "хипхоп": "hip hop",
    "рэп": "rap",
    "поп": "pop",
    "электроника": "electronic",
    "идм": "idm",
    "глитч": "glitch",
    "гэридж": "garage",
    "грим": "grime",
    "джангл": "jungle",
    "псайтранс": "psytrance",
    "чиллаут": "chillout",
    "трип-хоп": "trip hop",
    "трипхоп": "trip hop",
}

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s"
)
logger = logging.getLogger(__name__)

bot = Bot(token=BOT_TOKEN)
storage = MemoryStorage()
dp = Dispatcher(storage=storage)


def log_startup_warnings():
    if CORS_ALLOW_ALL:
        logger.critical("CORS_ALLOW_ALL is enabled. This is dangerous in production.")
    if DEV_ALLOW_EXPLICIT_USER_ID:
        logger.warning("DEV_ALLOW_EXPLICIT_USER_ID is enabled. Do not leave this in production.")
    if DEV_ALLOW_OPEN_AUDIO:
        logger.warning("DEV_ALLOW_OPEN_AUDIO is enabled. Audio URLs are not signed.")
    if EXTERNAL_URL.startswith("http://"):
        logger.warning("EXTERNAL_URL uses http://. In production use https://.")
    logger.info("ADMIN_USER_IDS: %s", sorted(ADMIN_USER_IDS))


def get_download_semaphore() -> asyncio.Semaphore:
    global DOWNLOAD_SEMAPHORE
    if DOWNLOAD_SEMAPHORE is None:
        DOWNLOAD_SEMAPHORE = asyncio.Semaphore(int(os.getenv("MAX_CONCURRENT_DOWNLOADS", "2").strip()))
    return DOWNLOAD_SEMAPHORE


# ==================== CANONICAL KEYS ====================

def canonical_artist(artist: str) -> str:
    return re.sub(r"[^a-zа-яё0-9&]+", " ", (artist or "").lower()).strip()


def canonical_artist_primary(artist: str) -> str:
    a = (artist or "").lower().strip()
    a = re.split(r"\s*(?:,|&|\bfeat\b|\bft\b|\bx\b|\bvs\b|\bwith\b)\s*", a, maxsplit=1)[0]
    return re.sub(r"[^a-zа-яё0-9]+", " ", a).strip()


def canonical_track(track: str) -> str:
    t = (track or "").lower()
    t = re.sub(r"\([^)]*\)", " ", t)
    t = re.sub(r"\[[^\]]*\]", " ", t)
    t = re.sub(r"\s+(?:feat|ft)\b.*$", " ", t)
    t = re.sub(r"[^a-zа-яё0-9 &]+", " ", t)
    tokens = [tok for tok in t.split() if tok and tok not in CANON_STOP_WORDS]
    if not tokens:
        tokens = [
            tok
            for tok in re.sub(r"[^a-zа-яё0-9 &]+", " ", (track or "").lower()).split()
            if tok
        ]
    return " ".join(tokens)


def canonical_key(artist: str, track: str) -> str:
    return f"{canonical_artist_primary(artist)}|||{canonical_track(track)}"


# ==================== SQLITE ====================

def db_connect() -> sqlite3.Connection:
    conn = sqlite3.connect(DB_PATH, timeout=30)
    conn.execute("PRAGMA journal_mode=WAL;")
    conn.execute("PRAGMA synchronous=NORMAL;")
    conn.execute("PRAGMA busy_timeout=5000;")
    return conn


def init_db_sync():
    with db_connect() as conn:
        conn.execute("""
        CREATE TABLE IF NOT EXISTS likes (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            artist TEXT NOT NULL,
            track TEXT NOT NULL,
            artist_lower TEXT NOT NULL,
            track_lower TEXT NOT NULL,
            created_at TEXT NOT NULL,
            UNIQUE(user_id, artist_lower, track_lower)
        )
        """)
        conn.execute("""
        CREATE TABLE IF NOT EXISTS dislikes (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            artist TEXT NOT NULL,
            track TEXT NOT NULL,
            artist_lower TEXT NOT NULL,
            track_lower TEXT NOT NULL,
            created_at TEXT NOT NULL,
            UNIQUE(user_id, artist_lower, track_lower)
        )
        """)
        conn.execute("""
        CREATE TABLE IF NOT EXISTS user_settings (
            user_id INTEGER PRIMARY KEY,
            global_use_likes INTEGER NOT NULL DEFAULT 0
        )
        """)
        conn.execute("""
        CREATE TABLE IF NOT EXISTS user_sources (
            user_id INTEGER PRIMARY KEY,
            use_youtube INTEGER NOT NULL DEFAULT 1,
            use_soundcloud INTEGER NOT NULL DEFAULT 1
        )
        """)
        conn.execute("""
        CREATE TABLE IF NOT EXISTS played_tracks (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            artist TEXT NOT NULL,
            track TEXT NOT NULL,
            artist_canon TEXT NOT NULL,
            track_canon TEXT NOT NULL,
            played_at TEXT NOT NULL
        )
        """)
        conn.execute("""
        CREATE TABLE IF NOT EXISTS users (
            user_id INTEGER PRIMARY KEY,
            username TEXT,
            first_name TEXT,
            last_name TEXT,
            created_at TEXT NOT NULL,
            last_seen TEXT NOT NULL
        )
        """)
        conn.execute("CREATE INDEX IF NOT EXISTS idx_likes_user_created ON likes(user_id, created_at DESC)")
        conn.execute("CREATE INDEX IF NOT EXISTS idx_dislikes_user_created ON dislikes(user_id, created_at DESC)")
        conn.execute("CREATE INDEX IF NOT EXISTS idx_likes_created ON likes(created_at DESC)")
        conn.execute("CREATE INDEX IF NOT EXISTS idx_played_user_played ON played_tracks(user_id, played_at DESC)")
        conn.execute("CREATE INDEX IF NOT EXISTS idx_played_user_canon ON played_tracks(user_id, artist_canon, track_canon)")
        conn.commit()
    logger.info("SQLite init done: %s", os.path.abspath(DB_PATH))


def db_upsert_user_sync(user_id, username=None, first_name=None, last_name=None):
    if not user_id:
        return
    now = datetime.datetime.now(datetime.timezone.utc).isoformat()
    with db_connect() as conn:
        conn.execute("""
        INSERT INTO users (user_id, username, first_name, last_name, created_at, last_seen)
        VALUES (?, ?, ?, ?, ?, ?)
        ON CONFLICT(user_id) DO UPDATE SET
            username=COALESCE(excluded.username, users.username),
            first_name=COALESCE(excluded.first_name, users.first_name),
            last_name=COALESCE(excluded.last_name, users.last_name),
            last_seen=excluded.last_seen
        """, (user_id, username, first_name, last_name, now, now))
        conn.commit()


def db_get_admin_stats_sync():
    with db_connect() as conn:
        rows = conn.execute("""
        WITH all_users AS (
            SELECT user_id FROM users
            UNION SELECT user_id FROM played_tracks
            UNION SELECT user_id FROM likes
            UNION SELECT user_id FROM dislikes
        )
        SELECT
            a.user_id, u.username, u.first_name, u.last_name, u.last_seen,
            (SELECT COUNT(*) FROM played_tracks p WHERE p.user_id = a.user_id) AS played,
            (SELECT COUNT(*) FROM likes l WHERE l.user_id = a.user_id) AS likes,
            (SELECT COUNT(*) FROM dislikes d WHERE d.user_id = a.user_id) AS dislikes
        FROM all_users a
        LEFT JOIN users u ON u.user_id = a.user_id
        ORDER BY u.last_seen DESC, a.user_id ASC
        """).fetchall()
    return rows


def db_add_reaction_sync(user_id, artist, track, kind):
    if not artist or not track:
        return 0, 0
    artist = artist.strip()
    track = track.strip()
    artist_lower = artist.lower()
    track_lower = track.lower()
    now = datetime.datetime.now(datetime.timezone.utc).isoformat()
    with db_connect() as conn:
        if kind == "like":
            conn.execute(
                "DELETE FROM dislikes WHERE user_id=? AND artist_lower=? AND track_lower=?",
                (user_id, artist_lower, track_lower)
            )
            conn.execute("""
            INSERT OR IGNORE INTO likes
                (user_id, artist, track, artist_lower, track_lower, created_at)
                VALUES (?, ?, ?, ?, ?, ?)
            """, (user_id, artist, track, artist_lower, track_lower, now))
        else:
            conn.execute(
                "DELETE FROM likes WHERE user_id=? AND artist_lower=? AND track_lower=?",
                (user_id, artist_lower, track_lower)
            )
            conn.execute("""
            INSERT OR IGNORE INTO dislikes
                (user_id, artist, track, artist_lower, track_lower, created_at)
                VALUES (?, ?, ?, ?, ?, ?)
            """, (user_id, artist, track, artist_lower, track_lower, now))
        conn.commit()
        likes_count = conn.execute("SELECT COUNT(*) FROM likes WHERE user_id=?", (user_id,)).fetchone()[0]
        dislikes_count = conn.execute("SELECT COUNT(*) FROM dislikes WHERE user_id=?", (user_id,)).fetchone()[0]
    return likes_count, dislikes_count


def db_remove_like_sync(user_id, artist, track):
    if not artist or not track:
        return 0
    artist_lower = artist.strip().lower()
    track_lower = track.strip().lower()
    with db_connect() as conn:
        conn.execute(
            "DELETE FROM likes WHERE user_id=? AND artist_lower=? AND track_lower=?",
            (user_id, artist_lower, track_lower)
        )
        conn.commit()
        return conn.execute("SELECT COUNT(*) FROM likes WHERE user_id=?", (user_id,)).fetchone()[0]


def db_get_reactions_sync(user_id):
    with db_connect() as conn:
        liked_rows = conn.execute(
            "SELECT artist, track FROM likes WHERE user_id=? ORDER BY created_at DESC LIMIT 1000",
            (user_id,)
        ).fetchall()
        disliked_rows = conn.execute(
            "SELECT artist, track, artist_lower, track_lower FROM dislikes WHERE user_id=? ORDER BY created_at DESC LIMIT 1000",
            (user_id,)
        ).fetchall()
    liked = [{"artist": r[0], "track": r[1]} for r in liked_rows]
    disliked = [{"artist": r[0], "track": r[1]} for r in disliked_rows]
    disliked_keys = {f"{r[2]}|||{r[3]}" for r in disliked_rows}
    return liked, disliked, disliked_keys


def db_page_sync(user_id, kind, page=1, page_size=REACTIONS_PAGE_SIZE):
    table = "likes" if kind == "like" else ("dislikes" if kind == "dislike" else None)
    if not table:
        return [], 0, 1
    page = max(1, page)
    page_size = max(1, page_size)
    with db_connect() as conn:
        total = conn.execute(f"SELECT COUNT(*) FROM {table} WHERE user_id=?", (user_id,)).fetchone()[0]
        pages = max(1, (total + page_size - 1) // page_size)
        page = min(page, pages)
        offset = (page - 1) * page_size
        rows = conn.execute(
            f"SELECT artist, track FROM {table} WHERE user_id=? ORDER BY created_at DESC LIMIT ? OFFSET ?",
            (user_id, page_size, offset)
        ).fetchall()
    return rows, total, pages


def db_clear_sync(user_id, kind):
    table = "likes" if kind == "like" else ("dislikes" if kind == "dislike" else None)
    if not table:
        return
    with db_connect() as conn:
        conn.execute(f"DELETE FROM {table} WHERE user_id=?", (user_id,))
        conn.commit()


def db_get_settings_sync(user_id):
    with db_connect() as conn:
        conn.execute("INSERT OR IGNORE INTO user_settings (user_id, global_use_likes) VALUES (?, 0)", (user_id,))
        conn.commit()
        row = conn.execute("SELECT global_use_likes FROM user_settings WHERE user_id=?", (user_id,)).fetchone()
    return bool(row[0]) if row else False


def db_set_settings_sync(user_id, global_use_likes):
    with db_connect() as conn:
        conn.execute("""
        INSERT INTO user_settings (user_id, global_use_likes) VALUES (?, ?)
        ON CONFLICT(user_id) DO UPDATE SET global_use_likes=excluded.global_use_likes
        """, (user_id, 1 if global_use_likes else 0))
        conn.commit()


def db_get_sources_sync(user_id):
    with db_connect() as conn:
        conn.execute("INSERT OR IGNORE INTO user_sources (user_id, use_youtube, use_soundcloud) VALUES (?, 1, 1)", (user_id,))
        conn.commit()
        row = conn.execute("SELECT use_youtube, use_soundcloud FROM user_sources WHERE user_id=?", (user_id,)).fetchone()
    if row:
        return bool(row[0]), bool(row[1])
    return True, True


def db_set_sources_sync(user_id, use_youtube, use_soundcloud):
    with db_connect() as conn:
        conn.execute("""
        INSERT INTO user_sources (user_id, use_youtube, use_soundcloud) VALUES (?, ?, ?)
        ON CONFLICT(user_id) DO UPDATE SET
            use_youtube=excluded.use_youtube,
            use_soundcloud=excluded.use_soundcloud
        """, (user_id, 1 if use_youtube else 0, 1 if use_soundcloud else 0))
        conn.commit()


def db_get_all_recent_likes_sync(max_per_user=2, max_total=400):
    with db_connect() as conn:
        rows = conn.execute("SELECT user_id, artist, track FROM likes ORDER BY created_at DESC LIMIT 2000").fetchall()
    per_user = defaultdict(int)
    result = []
    for user_id, artist, track in rows:
        if per_user[user_id] >= max_per_user:
            continue
        per_user[user_id] += 1
        result.append({"user_id": user_id, "artist": artist, "track": track})
        if len(result) >= max_total:
            break
    return result


def db_get_cooccurrence_sync(artist, track, limit=20):
    if not artist or not track:
        return []
    artist_lower = artist.strip().lower()
    track_lower = track.strip().lower()
    try:
        with db_connect() as conn:
            rows = conn.execute("""
            SELECT l2.artist, l2.track, COUNT(DISTINCT l2.user_id) AS shared_users
            FROM likes l1
            JOIN likes l2 ON l1.user_id = l2.user_id
            WHERE l1.artist_lower = ? AND l1.track_lower = ?
              AND NOT (l2.artist_lower = ? AND l2.track_lower = ?)
            GROUP BY l2.artist_lower, l2.track_lower
            ORDER BY shared_users DESC
            LIMIT ?
            """, (artist_lower, track_lower, artist_lower, track_lower, limit)).fetchall()
    except Exception as e:
        logger.warning("db_get_cooccurrence_sync failed: %s", e)
        return []

    result = []
    for row in rows:
        shared = int(row[2] or 0)
        result.append({
            "name": row[1],
            "artist": {"name": row[0]},
            "match": str(min(0.95, 0.5 + shared * 0.1)),
            "listeners": shared * 100,
            "source": "cooccurrence",
            "shared_users": shared,
        })
    return result


def db_add_played_sync(user_id, artist, track):
    if not artist or not track:
        return
    artist = artist.strip()
    track = track.strip()
    artist_canon = canonical_artist_primary(artist)
    track_canon = canonical_track(track)
    now = datetime.datetime.now(datetime.timezone.utc).isoformat()
    with db_connect() as conn:
        conn.execute("""
        INSERT INTO played_tracks
            (user_id, artist, track, artist_canon, track_canon, played_at)
            VALUES (?, ?, ?, ?, ?, ?)
        """, (user_id, artist, track, artist_canon, track_canon, now))
        conn.execute("""
        DELETE FROM played_tracks WHERE user_id=?
          AND id NOT IN (
              SELECT id FROM played_tracks WHERE user_id=? ORDER BY played_at DESC LIMIT 1000
          )
        """, (user_id, user_id))
        conn.commit()


def db_get_recent_played_sync(user_id, limit=500):
    with db_connect() as conn:
        return conn.execute("""
        SELECT artist, track, artist_canon, track_canon, played_at
        FROM played_tracks WHERE user_id=? ORDER BY played_at DESC LIMIT ?
        """, (user_id, limit)).fetchall()


# ==================== TELEGRAM WEBAPP AUTH ====================

def sign_user_auth(user_id: int, expires: int) -> str:
    msg = f"webapp_auth:{user_id}:{expires}".encode("utf-8")
    return hmac.new(AUDIO_SIGN_SECRET, msg, hashlib.sha256).hexdigest()


def verify_signed_auth(user_str: Optional[str], expires_str: Optional[str], sig: Optional[str]) -> Optional[int]:
    try:
        if not user_str or not expires_str or not sig:
            return None
        user_id = int(str(user_str))
        expires = int(str(expires_str))
    except Exception:
        return None
    if time.time() > expires:
        return None
    expected = sign_user_auth(user_id, expires)
    if hmac.compare_digest(expected, str(sig)):
        return user_id
    return None


def make_webapp_auth_params(user_id: int) -> str:
    expires = int(time.time()) + WEBAPP_AUTH_TTL_SECONDS
    sig = sign_user_auth(user_id, expires)
    return f"user_id={user_id}&auth_user={user_id}&auth_expires={expires}&auth_sig={sig}"


def verify_telegram_init_data(init_data):
    if not init_data:
        return None
    try:
        parsed = dict(urllib.parse.parse_qsl(init_data, keep_blank_values=True))
        received_hash = parsed.pop("hash", None)
        if not received_hash:
            return None
        data_check_string = "\n".join(f"{k}={v}" for k, v in sorted(parsed.items()))
        secret_key = hmac.new(b"WebAppData", BOT_TOKEN.encode("utf-8"), hashlib.sha256).digest()
        calculated_hash = hmac.new(secret_key, data_check_string.encode("utf-8"), hashlib.sha256).hexdigest()
        if not hmac.compare_digest(calculated_hash, received_hash):
            return None
        try:
            auth_date = int(parsed.get("auth_date", 0))
        except Exception:
            auth_date = 0
        if not auth_date:
            return None
        if INIT_DATA_MAX_AGE > 0 and time.time() - auth_date > INIT_DATA_MAX_AGE:
            return None
        user_raw = parsed.get("user")
        if not user_raw:
            return None
        user = json.loads(user_raw)
        user_id = int(user["id"])
        try:
            db_upsert_user_sync(user_id, user.get("username"), user.get("first_name"), user.get("last_name"))
        except Exception as e:
            logger.warning("db_upsert_user_sync from initData failed: %s", e)
        return user_id
    except Exception as e:
        logger.warning("verify_telegram_init_data failed: %s", e)
        return None


async def resolve_user_id(request, explicit_user_id_str=None):
    init_data = request.headers.get("X-Telegram-Init-Data")
    if init_data:
        verified = await asyncio.to_thread(verify_telegram_init_data, init_data)
        if verified:
            return verified

    signed_user = (
        request.headers.get("X-QuasWave-User")
        or request.query.get("auth_user")
        or request.query.get("user_id")
    )
    signed_expires = request.headers.get("X-QuasWave-Expires") or request.query.get("auth_expires")
    signed_sig = request.headers.get("X-QuasWave-Sig") or request.query.get("auth_sig")
    verified_signed = verify_signed_auth(signed_user, signed_expires, signed_sig)
    if verified_signed:
        return verified_signed

    if DEV_ALLOW_EXPLICIT_USER_ID and explicit_user_id_str:
        try:
            return int(explicit_user_id_str)
        except ValueError:
            return None

    return None


# ==================== USER STATE ====================

@dataclass
class UserState:
    current_artist: Optional[str] = None
    current_track: Optional[str] = None
    similar_tracks_queue: deque = field(default_factory=deque)
    preloaded_file: Optional[str] = None
    preloaded_track: Optional[dict] = None
    preloading_key: Optional[str] = None
    is_preloading: bool = False
    is_initialized: bool = False
    liked_tracks: List[dict] = field(default_factory=list)
    disliked_tracks: List[dict] = field(default_factory=list)
    liked_keys: Set[str] = field(default_factory=set)
    disliked_keys: Set[str] = field(default_factory=set)
    recent_played: deque = field(default_factory=lambda: deque(maxlen=200))
    played_canon_hard: deque = field(default_factory=lambda: deque(maxlen=PLAYED_HARD_LIMIT))
    played_canon_soft: deque = field(default_factory=lambda: deque(maxlen=PLAYED_SOFT_LIMIT))
    played_hard_set: Set[str] = field(default_factory=set)
    played_soft_set: Set[str] = field(default_factory=set)
    played_at: Dict[str, float] = field(default_factory=dict)
    mode: Optional[str] = None
    seed_artist: Optional[str] = None
    seed_track: Optional[str] = None
    seed_tag: Optional[str] = None
    session_positive_seeds: List[dict] = field(default_factory=list)
    negative_similar: Dict[str, float] = field(default_factory=dict)
    negative_canon: Dict[str, float] = field(default_factory=dict)
    negative_dirty: bool = True
    global_use_likes: bool = False
    use_youtube: bool = True
    use_soundcloud: bool = True
    wave_generation: int = 0
    preload_generation: int = 0
    next_pending_key: Optional[str] = None
    next_pending_track: Optional[dict] = None
    next_pending_generation: int = 0
    failed_tracks: Dict[str, Tuple[float, int, str]] = field(default_factory=dict)
    failed_canon: Dict[str, Tuple[float, int]] = field(default_factory=dict)


user_states: Dict[int, UserState] = {}


def reaction_key(artist, track):
    return f"{(artist or '').strip().lower()}|||{(track or '').strip().lower()}"


def extract_artist_name(track):
    if not isinstance(track, dict):
        return None, None
    artist_obj = track.get("artist", {})
    if isinstance(artist_obj, dict):
        artist = artist_obj.get("name")
    elif isinstance(artist_obj, str):
        artist = artist_obj
    else:
        artist = None
    name = track.get("name") or track.get("title") or track.get("track")
    return artist, name


def touch_user(user_id):
    USER_STATE_LAST_SEEN[user_id] = time.time()


def mask_payload(payload):
    if not isinstance(payload, dict):
        return payload
    safe = dict(payload)
    if safe.get("file_url"):
        safe["file_url"] = "<signed>"
    return safe


def _evict_dict_oldest(cache, max_size, keep_ratio=0.8):
    if len(cache) <= max_size:
        return
    keep = int(max_size * keep_ratio)
    for key in list(cache.keys())[:max(0, len(cache) - keep)]:
        cache.pop(key, None)


def _evict_lastfm_cache(max_size=1200):
    if len(LASTFM_CACHE) <= max_size:
        return
    items = sorted(LASTFM_CACHE.items(), key=lambda kv: kv[1][0])
    for key, _ in items[:max(0, len(LASTFM_CACHE) - int(max_size * 0.8))]:
        LASTFM_CACHE.pop(key, None)


def rebuild_played_sets(state):
    state.played_hard_set = set(state.played_canon_hard)
    state.played_soft_set = set(state.played_canon_soft)


def _trim_played_at(state, max_size=1500, keep=1000):
    if len(state.played_at) <= max_size:
        return
    items = sorted(state.played_at.items(), key=lambda kv: kv[1], reverse=True)
    state.played_at = dict(items[:keep])


async def record_played(user_id, state, artist, track):
    if not artist or not track:
        return
    key = reaction_key(artist, track)
    canon = canonical_key(artist, track)
    now = time.time()
    try:
        state.recent_played.remove(key)
    except ValueError:
        pass
    state.recent_played.append(key)
    for dq in (state.played_canon_hard, state.played_canon_soft):
        try:
            dq.remove(canon)
        except ValueError:
            pass
        dq.append(canon)
    state.played_at[canon] = now
    _trim_played_at(state)
    rebuild_played_sets(state)
    await asyncio.to_thread(db_add_played_sync, user_id, artist, track)


def cleanup_failed_tracks(state):
    now = time.time()
    for key in list(state.failed_tracks.keys()):
        if now > state.failed_tracks[key][0]:
            state.failed_tracks.pop(key, None)
    for key in list(state.failed_canon.keys()):
        if now > state.failed_canon[key][0]:
            state.failed_canon.pop(key, None)


def is_failed_exact(state, key):
    item = state.failed_tracks.get(key)
    return bool(item and time.time() <= item[0])


def is_failed_canon(state, canon):
    item = state.failed_canon.get(canon)
    return bool(item and time.time() <= item[0])


def failed_exact_set(state):
    now = time.time()
    return {k for k, v in state.failed_tracks.items() if now <= v[0]}


def failed_canon_set(state):
    now = time.time()
    return {k for k, v in state.failed_canon.items() if now <= v[0]}


def mark_download_failure(state, artist, track):
    key = reaction_key(artist, track)
    canon = canonical_key(artist, track)
    expires = time.time() + FAILED_TRACK_TTL
    count = state.failed_tracks.get(key, (0.0, 0, ""))[1] + 1
    state.failed_tracks[key] = (expires, count, canon)
    canon_count = state.failed_canon.get(canon, (0.0, 0))[1] + 1
    state.failed_canon[canon] = (expires, canon_count)
    return count


def clear_download_failure(state, artist, track):
    state.failed_tracks.pop(reaction_key(artist, track), None)
    state.failed_canon.pop(canonical_key(artist, track), None)


def purge_failed(state):
    state.failed_tracks.clear()
    state.failed_canon.clear()


async def get_or_create_state(user_id):
    state = user_states.get(user_id)
    if state:
        touch_user(user_id)
        return state

    state = UserState()
    liked, disliked, disliked_keys = await asyncio.to_thread(db_get_reactions_sync, user_id)
    settings = await asyncio.to_thread(db_get_settings_sync, user_id)
    use_yt, use_sc = await asyncio.to_thread(db_get_sources_sync, user_id)
    played_rows = await asyncio.to_thread(db_get_recent_played_sync, user_id, PLAYED_SOFT_LIMIT)

    state.liked_tracks = liked
    state.disliked_tracks = disliked
    state.disliked_keys = disliked_keys
    state.liked_keys = {reaction_key(i.get("artist", ""), i.get("track", "")) for i in liked}
    state.negative_dirty = True
    state.global_use_likes = settings
    state.use_youtube = use_yt
    state.use_soundcloud = use_sc

    for row in reversed(played_rows):
        artist, track, artist_canon, track_canon, played_at = row
        state.recent_played.append(reaction_key(artist, track))
        canon = f"{artist_canon}|||{track_canon}"
        state.played_canon_hard.append(canon)
        state.played_canon_soft.append(canon)
        try:
            ts = datetime.datetime.fromisoformat(played_at).timestamp()
        except Exception:
            ts = 0.0
        state.played_at[canon] = ts

    rebuild_played_sets(state)
    user_states[user_id] = state
    touch_user(user_id)
    return state


def remove_first_key_from_queue(state, key):
    new_queue = deque()
    removed = False
    for item in state.similar_tracks_queue:
        a, t = extract_artist_name(item)
        ik = reaction_key(a or "", t or "")
        if not removed and ik == key:
            removed = True
            continue
        new_queue.append(item)
    state.similar_tracks_queue = new_queue
    return removed


def remove_from_queue(state, artist, track):
    remove_first_key_from_queue(state, reaction_key(artist, track))


def add_positive_seed(state, artist, track):
    if not artist or not track:
        return
    key = reaction_key(artist, track)
    state.session_positive_seeds = [
        i for i in state.session_positive_seeds
        if reaction_key(i.get("artist", ""), i.get("track", "")) != key
    ]
    state.session_positive_seeds.append({"artist": artist, "track": track})
    if len(state.session_positive_seeds) > 20:
        state.session_positive_seeds = state.session_positive_seeds[-20:]


def apply_like_to_state(state, artist, track):
    key = reaction_key(artist, track)
    state.disliked_keys.discard(key)
    state.liked_keys.add(key)
    state.liked_tracks = [i for i in state.liked_tracks if reaction_key(i.get("artist", ""), i.get("track", "")) != key]
    state.liked_tracks.insert(0, {"artist": artist, "track": track})
    state.disliked_tracks = [i for i in state.disliked_tracks if reaction_key(i.get("artist", ""), i.get("track", "")) != key]
    state.negative_dirty = True
    add_positive_seed(state, artist, track)


def apply_unlike_to_state(state, artist, track):
    key = reaction_key(artist, track)
    state.liked_keys.discard(key)
    state.liked_tracks = [i for i in state.liked_tracks if reaction_key(i.get("artist", ""), i.get("track", "")) != key]
    state.session_positive_seeds = [i for i in state.session_positive_seeds if reaction_key(i.get("artist", ""), i.get("track", "")) != key]


def apply_dislike_to_state(state, artist, track):
    key = reaction_key(artist, track)
    state.disliked_keys.add(key)
    state.liked_keys.discard(key)
    state.liked_tracks = [i for i in state.liked_tracks if reaction_key(i.get("artist", ""), i.get("track", "")) != key]
    state.disliked_tracks = [i for i in state.disliked_tracks if reaction_key(i.get("artist", ""), i.get("track", "")) != key]
    state.disliked_tracks.insert(0, {"artist": artist, "track": track})
    state.session_positive_seeds = [i for i in state.session_positive_seeds if reaction_key(i.get("artist", ""), i.get("track", "")) != key]
    state.negative_dirty = True
    remove_from_queue(state, artist, track)


def track_is_liked(state, artist, title):
    if not state:
        return False
    return reaction_key(artist or "", title or "") in state.liked_keys


# ==================== FSM ====================

class WaveStates(StatesGroup):
    waiting_for_track_input = State()
    waiting_for_artist_input = State()
    waiting_for_tag_input = State()


# ==================== HTTP HELPERS ====================

def json_response(data, status=200):
    return web.Response(
        text=json.dumps(data, ensure_ascii=False),
        status=status,
        content_type="application/json",
        charset="utf-8",
        headers={"Cache-Control": "no-store"},
    )


def public_error(message="Internal server error"):
    return json_response({"error": message}, status=500)


def clean_text(value, limit=MAX_TEXT_LEN):
    return (value or "").strip()[:limit]


def cors_origin_for_request(request):
    origin = request.headers.get("Origin", "")
    if not origin:
        return WEBAPP_ORIGIN
    if CORS_ALLOW_ALL:
        return origin
    if origin == WEBAPP_ORIGIN:
        return origin
    return WEBAPP_ORIGIN


def get_user_action_lock(user_id):
    lock = USER_ACTION_LOCKS.get(user_id)
    if not lock:
        lock = asyncio.Lock()
        USER_ACTION_LOCKS[user_id] = lock
    return lock


def check_rate_limit(user_id, path):
    limit, window = RATE_LIMITS.get(path, (120, 60))
    now = time.monotonic()
    key = (user_id, path)
    hits = RATE_LIMIT_STATE[key]
    while hits and now - hits[0] > window:
        hits.pop(0)
    if len(hits) >= limit:
        return False
    hits.append(now)
    if len(RATE_LIMIT_STATE) > 20000:
        for sk in list(RATE_LIMIT_STATE.keys()):
            if not RATE_LIMIT_STATE[sk]:
                RATE_LIMIT_STATE.pop(sk, None)
    return True


def bot_rate_limit(user_id, action, limit, window):
    now = time.monotonic()
    key = (user_id, action)
    hits = BOT_RATE_STATE[key]
    while hits and now - hits[0] > window:
        hits.pop(0)
    if len(hits) >= limit:
        return False
    hits.append(now)
    if len(BOT_RATE_STATE) > 20000:
        for sk in list(BOT_RATE_STATE.keys()):
            if not BOT_RATE_STATE[sk]:
                BOT_RATE_STATE.pop(sk, None)
    return True


def sign_audio_path(filename, expires):
    return hmac.new(AUDIO_SIGN_SECRET, f"{filename}:{expires}".encode("utf-8"), hashlib.sha256).hexdigest()


def make_audio_url(filename):
    expires = int(time.time()) + AUDIO_URL_TTL_SECONDS
    sig = sign_audio_path(filename, expires)
    return f"{EXTERNAL_URL}/audio/{filename}?expires={expires}&sig={sig}"


async def parse_json_or_query(request):
    user_id_str = request.query.get("user_id")
    artist = request.query.get("artist")
    track = request.query.get("track") or request.query.get("title")
    page = request.query.get("page", "1")
    page_size = request.query.get("page_size", str(REACTIONS_PAGE_SIZE))
    try:
        if request.method in ("POST", "PUT", "PATCH") and request.can_read_body:
            data = await request.json()
            if isinstance(data, dict):
                user_id_str = data.get("user_id", user_id_str)
                artist = data.get("artist", artist)
                track = data.get("track", data.get("title", track))
                page = data.get("page", page)
                page_size = data.get("page_size", page_size)
    except Exception:
        pass
    return user_id_str, clean_text(artist), clean_text(track), page, page_size


# ==================== LAST.FM API ====================

LASTFM_URL = "https://ws.audioscrobbler.com/2.0/"
LASTFM_SESSION = requests.Session()
LASTFM_SESSION.headers.update({"User-Agent": "QuasWaveBot/1.0 (personal project)"})
COVER_SESSION = requests.Session()


def _lastfm_cache_key(params):
    safe = {k: v for k, v in params.items() if k != "api_key"}
    return hashlib.sha256(json.dumps(safe, sort_keys=True, ensure_ascii=False).encode("utf-8")).hexdigest()


def _lastfm_get(params, timeout=10, cache_ttl=None):
    params = {k: v for k, v in params.items() if v is not None}
    cache_key = _lastfm_cache_key(params)
    now = time.time()
    effective_ttl = cache_ttl if cache_ttl is not None else LASTFM_CACHE_TTL

    cached = LASTFM_CACHE.get(cache_key)
    if cached:
        cached_time, cached_data = cached
        if now - cached_time < effective_ttl:
            return json.loads(json.dumps(cached_data))

    for attempt in range(3):
        try:
            response = LASTFM_SESSION.get(LASTFM_URL, params=params, timeout=timeout)
            if response.status_code == 429 or response.status_code >= 500:
                retry_after = min(max(int(response.headers.get("Retry-After", 1 + attempt)), 1), 5)
                time.sleep(retry_after)
                continue
            if response.status_code >= 400:
                return None
            data = json.loads(response.content.decode("utf-8", "ignore"))
            if not isinstance(data, dict):
                return None
            if data.get("error"):
                if str(data.get("error")) in {"16", "29"}:
                    time.sleep(2 + attempt)
                    continue
                return None
            _evict_lastfm_cache(1200)
            LASTFM_CACHE[cache_key] = (time.time(), data)
            return json.loads(json.dumps(data))
        except Exception as e:
            logger.warning("Last.fm transport error attempt=%s: %s", attempt + 1, e)
            time.sleep(1 + attempt)
    return None


def _safe_int_count(value):
    try:
        return int(str(value).replace(",", "").strip())
    except Exception:
        return 0


def _normalize_tracks(raw_tracks, default_match="0.5"):
    if not raw_tracks:
        return []
    if isinstance(raw_tracks, dict):
        raw_tracks = [raw_tracks]
    if not isinstance(raw_tracks, list):
        return []

    result = []
    for track in raw_tracks:
        if not isinstance(track, dict):
            continue
        name = track.get("name")
        artist = track.get("artist")
        if isinstance(artist, dict):
            artist_name = artist.get("name")
        elif isinstance(artist, str):
            artist_name = artist
        else:
            artist_name = None
        if not name or not artist_name:
            continue
        track["artist"] = {"name": artist_name}
        track.setdefault("match", default_match)
        result.append(track)
    return result


def _extract_tags_recursive(node, depth=0, max_depth=7):
    found = []
    if depth > max_depth or node is None:
        return found

    if isinstance(node, dict):
        name = node.get("name")
        if isinstance(name, str) and name.strip():
            found.append({
                "name": name.strip().lower(),
                "count": _safe_int_count(node.get("count", node.get("listeners", 0))),
            })
        for value in node.values():
            found.extend(_extract_tags_recursive(value, depth + 1, max_depth))
    elif isinstance(node, list):
        for item in node:
            found.extend(_extract_tags_recursive(item, depth + 1, max_depth))

    return found


def get_similar_tracks(artist, track, limit=10):
    if not artist or not track:
        return []
    params = {
        "method": "track.getSimilar",
        "artist": artist,
        "track": track,
        "api_key": LASTFM_API_KEY,
        "format": "json",
        "limit": limit,
        "autocorrect": 1,
    }
    data = _lastfm_get(params, cache_ttl=LASTFM_SIMILAR_CACHE_TTL)
    tracks = []
    if data:
        tracks = _normalize_tracks(data.get("similartracks", {}).get("track", []), default_match="0.9")
    if tracks:
        return tracks[:limit]
    return get_artist_top_tracks(artist, limit)


def get_similar_tracks_raw(artist, track, limit=20):
    if not artist or not track:
        return []
    params = {
        "method": "track.getSimilar",
        "artist": artist,
        "track": track,
        "api_key": LASTFM_API_KEY,
        "format": "json",
        "limit": limit,
        "autocorrect": 1,
    }
    data = _lastfm_get(params, cache_ttl=LASTFM_SIMILAR_CACHE_TTL)
    if not data:
        return []
    return _normalize_tracks(data.get("similartracks", {}).get("track", []), default_match="0")[:limit]


def get_artist_top_tracks(artist, limit=10):
    if not artist:
        return []
    params = {
        "method": "artist.getTopTracks",
        "artist": artist,
        "api_key": LASTFM_API_KEY,
        "format": "json",
        "limit": limit,
        "autocorrect": 1,
    }
    data = _lastfm_get(params)
    if not data:
        return []
    return _normalize_tracks(data.get("toptracks", {}).get("track", []), default_match="0.7")[:limit]


def get_track_tags(artist, track, limit=3):
    if not artist or not track:
        return []
    key = reaction_key(artist, track)
    if key in TAG_CACHE:
        return TAG_CACHE[key]

    params = {
        "method": "track.getTopTags",
        "artist": artist,
        "track": track,
        "api_key": LASTFM_API_KEY,
        "format": "json",
        "limit": limit,
        "autocorrect": 1,
    }
    data = _lastfm_get(params, timeout=3)
    tags = []
    if data:
        raw_tags = data.get("toptags", {}).get("tag", [])
        if isinstance(raw_tags, dict):
            raw_tags = [raw_tags]
        if isinstance(raw_tags, list):
            for tag in raw_tags[:limit]:
                if isinstance(tag, dict) and tag.get("name"):
                    tags.append(tag["name"].strip().lower())

    TAG_CACHE[key] = tags
    _evict_dict_oldest(TAG_CACHE, 3000)
    return tags


def search_tracks(query, limit=10, artist=None):
    if not query:
        return []
    params = {
        "method": "track.search",
        "track": query,
        "api_key": LASTFM_API_KEY,
        "format": "json",
        "limit": limit,
    }
    if artist:
        params["artist"] = artist
    data = _lastfm_get(params)
    if not data:
        return []

    tracks = _normalize_tracks(
        data.get("results", {}).get("trackmatches", {}).get("track", []),
        default_match="0.5"
    )

    result = []
    seen = set()
    for track in tracks:
        tr_artist = track.get("artist", {}).get("name")
        name = track.get("name")
        if not tr_artist or not name:
            continue
        key = reaction_key(tr_artist, name)
        if key in seen:
            continue
        seen.add(key)
        result.append({
            "artist": tr_artist,
            "track": name,
            "listeners": _safe_int_count(track.get("listeners", 0)),
        })
    return result[:limit]


def search_artists(query, limit=10):
    if not query:
        return []
    params = {
        "method": "artist.search",
        "artist": query,
        "api_key": LASTFM_API_KEY,
        "format": "json",
        "limit": limit,
        "autocorrect": 1,
    }
    data = _lastfm_get(params)
    if not data:
        return []

    raw = data.get("results", {}).get("artistmatches", {}).get("artist", [])
    if isinstance(raw, dict):
        raw = [raw]
    if not isinstance(raw, list):
        return []

    result = []
    seen = set()
    for item in raw:
        if not isinstance(item, dict):
            continue
        name = (item.get("name") or "").strip()
        key = name.lower()
        if not name or key in seen:
            continue
        seen.add(key)
        result.append({
            "artist": name,
            "listeners": _safe_int_count(item.get("listeners", 0)),
        })
    return result[:limit]


def search_tags(query, limit=10):
    if not query:
        return []

    q = query.strip().lower()
    params = {
        "method": "tag.search",
        "tag": q,
        "api_key": LASTFM_API_KEY,
        "format": "json",
        "limit": limit,
    }
    data = _lastfm_get(params)

    extracted = []

    if data:
        raw = data.get("results", {}).get("tagmatches", {}).get("tag", [])
        if isinstance(raw, dict):
            raw = [raw]
        if isinstance(raw, list):
            for item in raw:
                if isinstance(item, dict) and item.get("name"):
                    extracted.append({
                        "name": str(item.get("name")).strip().lower(),
                        "count": _safe_int_count(item.get("count", 0)),
                    })

        if not extracted:
            extracted = _extract_tags_recursive(data.get("results", data))

    result = []
    seen = set()
    for item in extracted:
        name = str(item.get("name", "")).strip().lower()
        if not name or name in seen:
            continue
        seen.add(name)
        result.append({
            "name": name,
            "count": _safe_int_count(item.get("count", 0)),
        })

    if result:
        return result[:limit]

    # Fallback: Last.fm tag.search иногда ведёт себя как говно.
    # Если top tracks по тегу есть — считаем тег существующим.
    try:
        top = get_tag_top_tracks(q, 1)
        if top:
            return [{"name": q, "count": 0}]
    except Exception as e:
        logger.warning("search_tags fallback failed: %s", e)

    return []


def get_tag_top_tracks(tag, limit=100):
    if not tag:
        return []
    params = {
        "method": "tag.getTopTracks",
        "tag": tag,
        "api_key": LASTFM_API_KEY,
        "format": "json",
        "limit": limit,
    }
    data = _lastfm_get(params)
    if not data:
        return []
    tracks = data.get("toptracks", data.get("tracks", {})).get("track", [])
    return _normalize_tracks(tracks, default_match="0.8")[:limit]


def get_tag_top_artists(tag, limit=20):
    if not tag:
        return []
    params = {
        "method": "tag.getTopArtists",
        "tag": tag,
        "api_key": LASTFM_API_KEY,
        "format": "json",
        "limit": limit,
    }
    data = _lastfm_get(params)
    if not data:
        return []

    raw = data.get("topartists", {}).get("artist", [])
    if isinstance(raw, dict):
        raw = [raw]
    if not isinstance(raw, list):
        return []

    result = []
    seen = set()
    for item in raw:
        if not isinstance(item, dict):
            continue
        name = (item.get("name") or "").strip()
        key = name.lower()
        if not name or key in seen:
            continue
        seen.add(key)
        result.append({
            "name": name,
            "listeners": _safe_int_count(item.get("listeners", 0)),
        })
    return result[:limit]


def get_similar_tags(tag, limit=5):
    if not tag:
        return []
    params = {
        "method": "tag.getSimilar",
        "tag": tag,
        "api_key": LASTFM_API_KEY,
        "format": "json",
        "limit": limit,
    }
    data = _lastfm_get(params)
    if not data:
        return []

    raw = data.get("similartags", {}).get("tag", [])
    if isinstance(raw, dict):
        raw = [raw]
    if not isinstance(raw, list):
        return []

    result = []
    seen = set()
    for item in raw:
        if not isinstance(item, dict):
            continue
        name = (item.get("name") or "").strip().lower()
        if not name or name in seen:
            continue
        seen.add(name)
        result.append(name)
    return result[:limit]


def get_tracks_from_similar_artists(artist, limit=40):
    if not artist:
        return []
    params = {
        "method": "artist.getSimilar",
        "artist": artist,
        "api_key": LASTFM_API_KEY,
        "format": "json",
        "limit": 20,
        "autocorrect": 1,
    }
    data = _lastfm_get(params)
    if not data:
        return []

    raw = data.get("similarartists", {}).get("artist", [])
    if isinstance(raw, dict):
        raw = [raw]
    if not isinstance(raw, list):
        return []

    names = [i["name"] for i in raw if isinstance(i, dict) and i.get("name")]
    result = []
    seen = set()

    for sa in names[:20]:
        for track in get_artist_top_tracks(sa, 6):
            ta = track.get("artist", {}).get("name")
            tn = track.get("name")
            if not ta or not tn:
                continue
            key = reaction_key(ta, tn)
            if key in seen:
                continue
            seen.add(key)
            result.append(track)
            if len(result) >= limit:
                break

    return result[:limit]


async def _run_limited(semaphore, func, *args):
    async with semaphore:
        loop = asyncio.get_running_loop()
        return await loop.run_in_executor(LASTFM_EXECUTOR, func, *args)


def unique_artist_count(tracks):
    artists = set()
    for track in tracks:
        a, _ = extract_artist_name(track)
        if a:
            artists.add(a.strip().lower())
    return len(artists)


# ==================== RECO / SCORE / SELECT ====================

def candidate_rank(track):
    try:
        match = float(track.get("match", 0.5))
    except Exception:
        match = 0.5

    listeners = 0
    for fn in ("listeners", "playcount"):
        try:
            listeners = int(track.get(fn, 0) or 0)
        except Exception:
            listeners = 0
        if listeners > 0:
            break

    boost = float(track.get("score_boost", 0) or 0)
    return match * 1000.0 + min(listeners, 10_000_000) / 10000.0 + boost * 25.0


def dedupe_candidates(candidates):
    by_canon = {}
    for track in candidates:
        a, n = extract_artist_name(track)
        if not a or not n:
            continue
        track["artist"] = {"name": a}
        canon = canonical_key(a, n)
        old = by_canon.get(canon)
        if not old or candidate_rank(track) > candidate_rank(old):
            by_canon[canon] = track
    return list(by_canon.values())


def score_candidate(track, negative_similar, state=None, ignore_played_soft=False, negative_canon=None):
    a, n = extract_artist_name(track)
    key = reaction_key(a or "", n or "")
    canon = canonical_key(a or "", n or "")

    if track.get("source") == "cooccurrence":
        shared = int(track.get("shared_users", 0) or 0)
        score = 0.35 + min(0.55, shared * 0.08)
    else:
        try:
            match = float(track.get("match", 0.5))
        except Exception:
            match = 0.5
        score = 0.3 + match * 0.7

    listeners = 0
    for fn in ("listeners", "playcount"):
        try:
            listeners = int(track.get(fn, 0) or 0)
        except Exception:
            listeners = 0
        if listeners > 0:
            break

    if listeners > 0:
        score *= min(1.0, math.log10(listeners + 1) / 7.0)

    boost = float(track.get("score_boost", 0) or 0)
    score = max(0.0, score + boost)

    neg = max((negative_similar or {}).get(key, 0.0), (negative_canon or {}).get(canon, 0.0))
    score *= max(0.0, 1.0 - neg)

    if state and not ignore_played_soft and canon in state.played_soft_set:
        score *= 0.15

    if SCORE_JITTER > 0:
        score *= 1.0 + random.uniform(-SCORE_JITTER, SCORE_JITTER)

    return score


def sort_candidates_by_score(candidates, negative_similar, state=None, ignore_played_soft=False, negative_canon=None):
    neg = negative_similar or {}
    nc = negative_canon or {}
    return sorted(
        candidates,
        key=lambda t: score_candidate(t, neg, state=state, ignore_played_soft=ignore_played_soft, negative_canon=nc),
        reverse=True
    )


def lrp_sort_candidates(state, candidates):
    played_at = state.played_at

    def _ts(track):
        a, n = extract_artist_name(track)
        if not a or not n:
            return 0.0
        return played_at.get(canonical_key(a, n), 0.0)

    return sorted(candidates, key=_ts)


def select_diverse(
    tracks,
    desired,
    disliked_keys,
    recent_keys,
    current_artist,
    current_track,
    max_per_artist=1,
    exclude_keys=None,
    exclude_canon_keys=None,
    negative_similar=None,
    negative_canon=None,
    played_hard_set=None,
    failed_exact_keys=None,
    failed_canon_keys=None,
    allow_adjacent_same=False
):
    if desired <= 0:
        return [], set(exclude_keys or set()), set(exclude_canon_keys or set())

    exclude_keys = set(exclude_keys or set())
    exclude_canon_keys = set(exclude_canon_keys or set())
    negative_similar = negative_similar or {}
    negative_canon = negative_canon or {}
    played_hard_set = played_hard_set or set()
    failed_exact_keys = failed_exact_keys or set()
    failed_canon_keys = failed_canon_keys or set()

    result = []
    seen_exact = set(exclude_keys)
    seen_canon = set(exclude_canon_keys)
    seen_canon.update(played_hard_set)

    artist_counts = defaultdict(int)
    current_key = reaction_key(current_artist, current_track) if current_artist and current_track else None
    current_canon = canonical_key(current_artist, current_track) if current_artist and current_track else None
    recent_set = set(recent_keys)
    last_artist_lower = None

    for track in tracks:
        a, n = extract_artist_name(track)
        if not a or not n:
            continue

        track["artist"] = {"name": a}
        key = reaction_key(a, n)
        canon = canonical_key(a, n)

        if key in disliked_keys or key in recent_set or key in seen_exact or canon in seen_canon:
            continue
        if key in failed_exact_keys or canon in failed_canon_keys:
            continue
        if current_key and (key == current_key or canon == current_canon):
            continue

        neg_score = max(negative_similar.get(key, 0.0), negative_canon.get(canon, 0.0))
        if neg_score >= NEGATIVE_HARD_THRESHOLD:
            continue

        al = a.lower()
        if artist_counts[al] >= max_per_artist:
            continue
        if not allow_adjacent_same and last_artist_lower is not None and al == last_artist_lower:
            continue

        artist_counts[al] += 1
        seen_exact.add(key)
        seen_canon.add(canon)
        result.append(track)
        last_artist_lower = al

        if len(result) >= desired:
            break

    return result, seen_exact, seen_canon


async def diversify_by_tags(tracks):
    if not tracks or len(tracks) < 2:
        return tracks

    try:
        semaphore = asyncio.Semaphore(TAG_SEMAPHORE_LIMIT)

        async def fetch_tags(track):
            a, n = extract_artist_name(track)
            if not a or not n:
                return []
            try:
                return await asyncio.wait_for(_run_limited(semaphore, get_track_tags, a, n, 3), timeout=TAG_FETCH_TIMEOUT)
            except Exception:
                return []

        tag_lists = await asyncio.gather(*(fetch_tags(t) for t in tracks), return_exceptions=True)
        enriched = [(t, tags if isinstance(tags, list) else []) for t, tags in zip(tracks, tag_lists)]

        result = []
        remaining = list(enriched)
        last_tag = None

        while remaining:
            chosen_idx = 0
            for i, (_t, tags) in enumerate(remaining):
                primary = tags[0] if tags else None
                if primary and primary == last_tag:
                    continue
                chosen_idx = i
                break

            track, tags = remaining.pop(chosen_idx)
            result.append(track)
            last_tag = tags[0] if tags else None

        return result
    except Exception as e:
        logger.warning("diversify_by_tags failed: %s", e)
        return tracks


async def ensure_negative_similar(state):
    if not state.negative_dirty:
        return

    if not state.disliked_tracks:
        state.negative_similar = {}
        state.negative_canon = {}
        state.negative_dirty = False
        return

    semaphore = asyncio.Semaphore(4)
    tasks = [
        _run_limited(semaphore, get_similar_tracks_raw, d.get("artist", ""), d.get("track", ""), 15)
        for d in state.disliked_tracks[:8]
    ]
    results = await asyncio.gather(*tasks, return_exceptions=True)

    new_neg = {}
    new_neg_canon = {}
    success = False

    for result in results:
        if isinstance(result, Exception) or not isinstance(result, list):
            continue
        success = True
        for track in result:
            a, n = extract_artist_name(track)
            if not a or not n:
                continue
            try:
                score = float(track.get("match", 0))
            except Exception:
                score = 0.0
            key = reaction_key(a, n)
            canon = canonical_key(a, n)
            if score > new_neg.get(key, 0.0):
                new_neg[key] = score
            if score > new_neg_canon.get(canon, 0.0):
                new_neg_canon[canon] = score

    if success:
        state.negative_similar = new_neg
        state.negative_canon = new_neg_canon
        state.negative_dirty = False
    else:
        state.negative_dirty = True


async def collect_track_mode_candidates(state):
    seed_artist = state.seed_artist or state.current_artist
    seed_track = state.seed_track or state.current_track
    if not seed_artist or not seed_track:
        return []

    semaphore = asyncio.Semaphore(5)
    tasks = [
        _run_limited(semaphore, get_similar_tracks, seed_artist, seed_track, 100),
        _run_limited(semaphore, get_artist_top_tracks, seed_artist, 50),
        _run_limited(semaphore, get_tracks_from_similar_artists, seed_artist, 120),
        _run_limited(semaphore, db_get_cooccurrence_sync, seed_artist, seed_track, 30),
    ]

    for ps in state.session_positive_seeds[-6:]:
        tasks.append(_run_limited(semaphore, get_similar_tracks, ps.get("artist", ""), ps.get("track", ""), 30))

    tasks.append(_run_limited(semaphore, get_tracks_from_similar_artists, seed_artist, 60))

    results = await asyncio.gather(*tasks, return_exceptions=True)
    candidates = []
    for r in results:
        if isinstance(r, list):
            candidates.extend(r)

    candidates = dedupe_candidates(candidates)
    if len(candidates) > 250:
        candidates = random.sample(candidates, 250)
    return candidates


async def collect_likes_mode_candidates(state):
    all_seeds = state.liked_tracks
    if not all_seeds:
        return []

    seeds = random.sample(all_seeds, min(10, len(all_seeds)))
    semaphore = asyncio.Semaphore(5)
    tasks = []

    for seed in seeds:
        tasks.append(_run_limited(semaphore, get_similar_tracks, seed.get("artist", ""), seed.get("track", ""), 10))
        tasks.append(_run_limited(semaphore, get_artist_top_tracks, seed.get("artist", ""), 4))

    results = await asyncio.gather(*tasks, return_exceptions=True)
    candidates = []
    for r in results:
        if isinstance(r, list):
            candidates.extend(r)

    candidates = dedupe_candidates(candidates)
    if len(candidates) > 250:
        candidates = random.sample(candidates, 250)
    return candidates


def collect_likes_playlist_candidates(state):
    candidates = [{"name": i["track"], "artist": {"name": i["artist"]}, "match": "❤"} for i in state.liked_tracks]
    return dedupe_candidates(candidates)


async def collect_artist_mode_candidates(state):
    if not state.seed_artist:
        return []

    tracks = await asyncio.to_thread(get_artist_top_tracks, state.seed_artist, 100)

    def pop_score(t):
        for fn in ("playcount", "listeners"):
            try:
                v = int(t.get(fn, 0))
            except Exception:
                v = 0
            if v > 0:
                return v
        return 0

    tracks.sort(key=pop_score, reverse=True)
    return dedupe_candidates(tracks)


async def collect_tag_mode_candidates(state):
    seed_tag = state.seed_tag
    if not seed_tag:
        return []

    semaphore = asyncio.Semaphore(5)

    top_tracks = await _run_limited(semaphore, get_tag_top_tracks, seed_tag, 100)
    top_artists = await _run_limited(semaphore, get_tag_top_artists, seed_tag, 20)
    similar_tags = await _run_limited(semaphore, get_similar_tags, seed_tag, 2)

    candidates = list(top_tracks)
    tasks = []

    for art in top_artists[:20]:
        artist_name = art.get("name")
        if artist_name:
            tasks.append(_run_limited(semaphore, get_artist_top_tracks, artist_name, 5))

    for sim_tag in similar_tags[:2]:
        tasks.append(_run_limited(semaphore, get_tag_top_tracks, sim_tag, 30))

    if tasks:
        results = await asyncio.gather(*tasks, return_exceptions=True)
        for r in results:
            if isinstance(r, list):
                candidates.extend(r)

    candidates = dedupe_candidates(candidates)
    if len(candidates) > 250:
        candidates = random.sample(candidates, 250)

    return candidates


async def _build_global_pool_candidates():
    all_likes = await asyncio.to_thread(db_get_all_recent_likes_sync, GLOBAL_SEEDS_PER_USER, GLOBAL_POOL_SEEDS * 4)

    deduped = []
    seen_canon = set()

    for item in all_likes:
        a = item.get("artist", "")
        t = item.get("track", "")
        if not a or not t:
            continue
        canon = canonical_key(a, t)
        if canon in seen_canon:
            continue
        seen_canon.add(canon)
        deduped.append(item)

    seeds = random.sample(deduped, min(GLOBAL_POOL_SEEDS, len(deduped))) if len(deduped) > GLOBAL_POOL_SEEDS else list(deduped)

    semaphore = asyncio.Semaphore(6)
    tasks = []

    for seed in seeds:
        tasks.append(_run_limited(semaphore, get_similar_tracks, seed.get("artist", ""), seed.get("track", ""), 10))
        tasks.append(_run_limited(semaphore, get_artist_top_tracks, seed.get("artist", ""), 4))

    results = await asyncio.gather(*tasks, return_exceptions=True)
    candidates = []

    for r in results:
        if isinstance(r, list):
            candidates.extend(r)

    candidates = dedupe_candidates(candidates)

    if not candidates:
        for item in seeds[:GLOBAL_DIRECT_FALLBACK]:
            candidates.append({
                "name": item.get("track", ""),
                "artist": {"name": item.get("artist", "")},
                "match": "🌍",
                "source": "global_like_fallback",
                "score_boost": -0.15,
            })

    return dedupe_candidates(candidates)


async def get_global_pool_candidates():
    now = time.time()
    ts = float(GLOBAL_POOL.get("ts", 0.0))
    candidates = GLOBAL_POOL.get("candidates", [])

    if now - ts <= GLOBAL_POOL_TTL and candidates:
        return list(candidates)

    async with GLOBAL_POOL_LOCK:
        ts = float(GLOBAL_POOL.get("ts", 0.0))
        candidates = GLOBAL_POOL.get("candidates", [])
        if now - ts <= GLOBAL_POOL_TTL and candidates:
            return list(candidates)

        candidates = await _build_global_pool_candidates()
        GLOBAL_POOL["candidates"] = candidates
        GLOBAL_POOL["ts"] = time.time()

    return list(candidates)


async def collect_global_mode_candidates(state):
    candidates = list(await get_global_pool_candidates())

    if state.global_use_likes and state.liked_tracks:
        semaphore = asyncio.Semaphore(4)
        tasks = []
        user_seeds = random.sample(state.liked_tracks, min(10, len(state.liked_tracks)))

        for seed in user_seeds:
            tasks.append(_run_limited(semaphore, get_similar_tracks, seed.get("artist", ""), seed.get("track", ""), 10))
            tasks.append(_run_limited(semaphore, get_artist_top_tracks, seed.get("artist", ""), 3))

        results = await asyncio.gather(*tasks, return_exceptions=True)

        for r in results:
            if isinstance(r, list):
                for track in r:
                    track["score_boost"] = 0.15
                candidates.extend(r)

    return dedupe_candidates(candidates)


# ==================== COVERS ====================

COVER_CACHE: Dict[str, Optional[str]] = {}
LASTFM_DEFAULT_IMAGE_HASH = "2a96cbd8b46e442fc41c2b86b821562f"


def extract_lastfm_image(image_obj):
    if not image_obj:
        return None

    images = image_obj if isinstance(image_obj, list) else ([image_obj] if isinstance(image_obj, dict) else [])
    if not images:
        return None

    chosen = None
    for item in images:
        if not isinstance(item, dict):
            continue
        url = item.get("#text") or item.get("url")
        size = item.get("size", "")
        if url and size in ("extralarge", "large", "mega"):
            chosen = url

    if not chosen and images and isinstance(images[0], dict):
        chosen = images[0].get("#text") or images[0].get("url")

    if chosen and LASTFM_DEFAULT_IMAGE_HASH in chosen:
        return None

    return chosen


def get_cover_url(artist, title):
    if not artist or not title:
        return None

    key = reaction_key(artist, title)
    if key in COVER_CACHE:
        return COVER_CACHE[key]

    try:
        response = COVER_SESSION.get(
            "https://itunes.apple.com/search",
            params={"term": f"{artist} {title}", "limit": 1, "media": "music", "entity": "song"},
            timeout=5
        )
        data = response.json()
        results = data.get("results", [])
        if results:
            artwork = results[0].get("artworkUrl100")
            if artwork:
                artwork = artwork.replace("100x100bb", "600x600bb").replace("100x100", "600x600")
                COVER_CACHE[key] = artwork
                _evict_dict_oldest(COVER_CACHE, 1200)
                return artwork
    except Exception:
        pass

    COVER_CACHE[key] = None
    _evict_dict_oldest(COVER_CACHE, 1200)
    return None


async def get_cover_for_track(artist, title, image_obj=None):
    try:
        cover = await asyncio.wait_for(asyncio.to_thread(get_cover_url, artist, title), timeout=4)
    except Exception:
        cover = None
    return cover or extract_lastfm_image(image_obj)


# ==================== YT-DLP / CACHE ====================

download_locks: Dict[str, asyncio.Lock] = {}


def get_download_lock(key):
    lock = download_locks.get(key)
    if not lock:
        lock = asyncio.Lock()
        download_locks[key] = lock
        if len(download_locks) > 10000:
            for lk in list(download_locks.keys()):
                existing = download_locks.get(lk)
                if existing and not existing.locked():
                    download_locks.pop(lk, None)
    return lock


def get_cache_path(artist, title):
    digest = hashlib.sha256(f"{(artist or '').strip().lower()}|||{(title or '').strip().lower()}".encode("utf-8")).hexdigest()
    return os.path.join(AUDIO_CACHE_DIR, f"{digest}.mp3")


async def cleanup_audio_cache(max_files=250, max_bytes=700 * 1024 * 1024):
    def _cleanup():
        os.makedirs(AUDIO_CACHE_DIR, exist_ok=True)
        files = []
        total_bytes = 0

        try:
            for entry in os.scandir(AUDIO_CACHE_DIR):
                if not entry.is_file() or not entry.name.endswith(".mp3"):
                    continue
                try:
                    stat = entry.stat()
                    files.append((entry.path, stat.st_mtime, stat.st_size))
                    total_bytes += stat.st_size
                except Exception:
                    pass
        except Exception:
            return

        files.sort(key=lambda x: x[1], reverse=True)
        kept_files = 0
        kept_bytes = 0

        for path, _mtime, size in files:
            kept_files += 1
            kept_bytes += size
            if kept_files > max_files or kept_bytes > max_bytes:
                try:
                    os.remove(path)
                except Exception:
                    pass

        try:
            os.makedirs(DOWNLOAD_DIR, exist_ok=True)
            for entry in os.scandir(DOWNLOAD_DIR):
                if not entry.is_file():
                    continue
                try:
                    if time.time() - entry.stat().st_mtime > 24 * 3600:
                        os.remove(entry.path)
                except Exception:
                    pass
        except Exception:
            pass

    await asyncio.to_thread(_cleanup)


def _is_age_gate_error(exc):
    msg = str(exc).lower()
    return any(p in msg for p in AGE_GATE_PATTERNS)


def _build_ydl_opts(uid):
    opts = {
        "format": "bestaudio[abr<=192]/bestaudio/best",
        "outtmpl": os.path.join(DOWNLOAD_DIR, f"{uid}.%(ext)s"),
        "postprocessors": [{
            "key": "FFmpegExtractAudio",
            "preferredcodec": "mp3",
            "preferredquality": "192",
        }],
        "quiet": True,
        "no_warnings": True,
        "noplaylist": True,
        "extract_flat": False,
        "restrictfilenames": True,
        "socket_timeout": 15,
        "retries": 2,
        "extractor_retries": 2,
        "max_filesize": 50 * 1024 * 1024,
        "http_headers": {
            "User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36",
            "Accept-Language": "en-US,en;q=0.9",
        },
        "extractor_args": {"youtube": {"player_client": YT_PLAYER_CLIENTS}},
    }

    cookiefile = os.getenv("YT_COOKIEFILE", "").strip()
    if cookiefile and os.path.isfile(cookiefile):
        opts["cookiefile"] = cookiefile

    return opts


def _build_search_opts():
    return {
        "quiet": True,
        "no_warnings": True,
        "extract_flat": True,
        "skip_download": True,
        "noplaylist": True,
        "socket_timeout": 10,
        "retries": 1,
        "http_headers": {
            "User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36",
            "Accept-Language": "en-US,en;q=0.9",
        },
    }


def _entry_url(ent, prefix):
    if not isinstance(ent, dict):
        return None
    url = ent.get("webpage_url") or ent.get("url")
    if url:
        return url
    if prefix.startswith("ytsearch") and ent.get("id"):
        return f"https://www.youtube.com/watch?v={ent['id']}"
    return None


def _entry_is_age_gated(ent):
    try:
        return int(ent.get("age_limit") or 0) >= 18
    except Exception:
        return False


def _mark_age_gate(url):
    AGE_GATE_URL_CACHE[url] = time.time()
    if len(AGE_GATE_URL_CACHE) > 5000:
        cutoff = time.time() - AGE_GATE_TTL
        for k in [k for k, v in AGE_GATE_URL_CACHE.items() if v < cutoff]:
            AGE_GATE_URL_CACHE.pop(k, None)


def _is_known_age_gate(url):
    ts = AGE_GATE_URL_CACHE.get(url)
    if not ts:
        return False
    if time.time() - ts > AGE_GATE_TTL:
        AGE_GATE_URL_CACHE.pop(url, None)
        return False
    return True


def _build_search_prefixes(use_youtube, use_soundcloud):
    prefixes = []
    if use_youtube:
        prefixes.append("ytsearch5")
    if use_soundcloud:
        prefixes.append("scsearch3")
    if not prefixes:
        prefixes = ["ytsearch5"]
    return prefixes


async def _gather_search_candidates(query, loop, use_youtube=True, use_soundcloud=True):
    urls = []

    for prefix in _build_search_prefixes(use_youtube, use_soundcloud):
        if len(urls) >= 3:
            break

        def _search(p=prefix):
            with yt_dlp.YoutubeDL(_build_search_opts()) as ydl:
                return ydl.extract_info(f"{p}:{query}", download=False)

        try:
            info = await loop.run_in_executor(SEARCH_EXECUTOR, _search)
        except Exception as e:
            if _is_age_gate_error(e):
                logger.warning("Search %s age-gate for: %s", prefix, query)
            else:
                logger.warning("Search %s failed for %s: %s", prefix, query, e)
            continue

        if not isinstance(info, dict):
            continue

        for ent in (info.get("entries") or [])[:8]:
            if _entry_is_age_gated(ent):
                continue
            u = _entry_url(ent, prefix)
            if u and u not in urls:
                urls.append(u)

    return urls


async def _download_track_impl(artist, track, use_youtube=True, use_soundcloud=True):
    query = f"{artist} {track}".strip()
    if not query:
        return None

    os.makedirs(AUDIO_CACHE_DIR, exist_ok=True)
    os.makedirs(DOWNLOAD_DIR, exist_ok=True)

    cache_path = get_cache_path(artist, track)

    if os.path.isfile(cache_path) and os.path.getsize(cache_path) > 10000:
        return cache_path

    if os.path.isfile(cache_path):
        try:
            os.remove(cache_path)
        except Exception:
            pass

    loop = asyncio.get_running_loop()
    candidate_urls = await _gather_search_candidates(query, loop, use_youtube, use_soundcloud)
    if not candidate_urls:
        candidate_urls = [f"ytsearch1:{query}"]

    async with get_download_semaphore():
        lock = get_download_lock(cache_path)
        async with lock:
            if os.path.isfile(cache_path) and os.path.getsize(cache_path) > 10000:
                return cache_path

            uid = uuid.uuid4().hex
            age_gate_hits = 0
            other_failures = 0

            for url in candidate_urls:
                if _is_known_age_gate(url):
                    age_gate_hits += 1
                    continue

                def _download_one(u=url):
                    with yt_dlp.YoutubeDL(_build_ydl_opts(uid)) as ydl:
                        return ydl.extract_info(u, download=True)

                try:
                    info = await loop.run_in_executor(DOWNLOAD_EXECUTOR, _download_one)
                except Exception as e:
                    if _is_age_gate_error(e):
                        age_gate_hits += 1
                        _mark_age_gate(url)
                        continue
                    other_failures += 1
                    logger.warning("Candidate failed: %s url=%s err=%s", query, url, e)
                    continue

                if isinstance(info, dict) and _entry_is_age_gated(info):
                    age_gate_hits += 1
                    _mark_age_gate(url)
                    continue

                if not info:
                    other_failures += 1
                    continue

                file_candidates = [os.path.join(DOWNLOAD_DIR, f"{uid}.mp3")]
                for item in (info.get("requested_downloads") or []):
                    if isinstance(item, dict):
                        fp = item.get("filepath") or item.get("_filename")
                        if fp:
                            file_candidates.append(fp)
                file_candidates.extend(glob.glob(os.path.join(DOWNLOAD_DIR, f"{uid}.*")))

                for candidate in file_candidates:
                    if candidate and os.path.isfile(candidate) and candidate.endswith(".mp3"):
                        tmp_cache = f"{cache_path}.{uid}.tmp"
                        try:
                            await asyncio.to_thread(shutil.move, candidate, tmp_cache)
                            size = await asyncio.to_thread(os.path.getsize, tmp_cache)
                            if size > 10000:
                                await asyncio.to_thread(os.replace, tmp_cache, cache_path)
                                return cache_path
                            await asyncio.to_thread(os.remove, tmp_cache)
                        except Exception as e:
                            logger.warning("Cache move failed for %s: %s", query, e)
                            try:
                                if os.path.isfile(tmp_cache):
                                    await asyncio.to_thread(os.remove, tmp_cache)
                            except Exception:
                                pass
                            try:
                                if os.path.isfile(candidate):
                                    await asyncio.to_thread(os.remove, candidate)
                            except Exception:
                                pass
                        other_failures += 1

            if age_gate_hits and not other_failures:
                logger.warning("All %s candidates age-gated for: %s", age_gate_hits, query)
            else:
                logger.error("Download gave up for %s: age_gate=%s other=%s", query, age_gate_hits, other_failures)

            for leftover in glob.glob(os.path.join(DOWNLOAD_DIR, f"{uid}.*")):
                try:
                    await asyncio.to_thread(os.remove, leftover)
                except Exception:
                    pass

            return None


async def download_track(artist, track, use_youtube=True, use_soundcloud=True):
    try:
        return await asyncio.wait_for(
            _download_track_impl(artist, track, use_youtube, use_soundcloud),
            timeout=DOWNLOAD_TOTAL_TIMEOUT,
        )
    except asyncio.TimeoutError:
        logger.error("Download total timeout for %s - %s", artist, track)
        return None
    except Exception as e:
        logger.error("Download critical error for %s - %s: %s", artist, track, e, exc_info=True)
        return None


async def copy_to_audio_files(user_id, source_path):
    os.makedirs(AUDIO_CACHE_DIR, exist_ok=True)
    filename = os.path.basename(source_path)
    dest_path = os.path.join(AUDIO_CACHE_DIR, filename)

    if os.path.abspath(source_path) != os.path.abspath(dest_path):
        await asyncio.to_thread(shutil.copy2, source_path, dest_path)

    return make_audio_url(filename)


# ==================== PRELOAD / QUEUE ====================

async def clear_preloaded_file(state, new_wave=False):
    state.preload_generation += 1
    if new_wave:
        state.wave_generation += 1
    state.preloaded_file = None
    state.preloaded_track = None
    state.is_preloading = False
    state.preloading_key = None


def queue_existing_exact(state):
    keys = set()
    for item in state.similar_tracks_queue:
        a, n = extract_artist_name(item)
        if a and n:
            keys.add(reaction_key(a, n))
    if state.current_artist and state.current_track:
        keys.add(reaction_key(state.current_artist, state.current_track))
    if state.preloaded_track:
        keys.add(reaction_key(state.preloaded_track.get("artist", ""), state.preloaded_track.get("title", "")))
    if state.next_pending_track:
        a, n = extract_artist_name(state.next_pending_track)
        if a and n:
            keys.add(reaction_key(a, n))
    return keys


def queue_existing_canon(state):
    keys = set()
    for item in state.similar_tracks_queue:
        a, n = extract_artist_name(item)
        if a and n:
            keys.add(canonical_key(a, n))
    if state.current_artist and state.current_track:
        keys.add(canonical_key(state.current_artist, state.current_track))
    if state.preloaded_track:
        keys.add(canonical_key(state.preloaded_track.get("artist", ""), state.preloaded_track.get("title", "")))
    if state.next_pending_track:
        a, n = extract_artist_name(state.next_pending_track)
        if a and n:
            keys.add(canonical_key(a, n))
    return keys


def make_liked_track_candidates(state):
    return dedupe_candidates([
        {"name": i["track"], "artist": {"name": i["artist"]}, "match": "❤"}
        for i in state.liked_tracks
    ])


async def refill_queue(user_id, state, limit=18):
    if not state.mode:
        state.mode = "track" if state.seed_artist and state.seed_track else "global"

    if state.mode == "track" and (not state.seed_artist or not state.seed_track):
        state.seed_artist = state.current_artist
        state.seed_track = state.current_track

    if state.mode == "artist" and not state.seed_artist:
        state.mode = "global"

    if state.mode == "tag" and not state.seed_tag:
        state.mode = "global"

    before = len(state.similar_tracks_queue)
    cleanup_failed_tracks(state)

    existing_exact = queue_existing_exact(state)
    existing_canon = queue_existing_canon(state)
    failed_exact = failed_exact_set(state)
    failed_canon = failed_canon_set(state)

    if state.mode == "likes":
        candidates = await collect_likes_mode_candidates(state)
    elif state.mode == "artist":
        candidates = await collect_artist_mode_candidates(state)
    elif state.mode == "likes_playlist":
        candidates = collect_likes_playlist_candidates(state)
        if len(candidates) <= 1:
            candidates.extend(await collect_likes_mode_candidates(state))
    elif state.mode == "global":
        candidates = await collect_global_mode_candidates(state)
    elif state.mode == "tag":
        candidates = await collect_tag_mode_candidates(state)
    else:
        candidates = await collect_track_mode_candidates(state)

    candidates = dedupe_candidates(candidates)
    pool_size = len(candidates)

    if state.mode != "likes_playlist":
        await ensure_negative_similar(state)
        candidates = sort_candidates_by_score(
            candidates,
            state.negative_similar,
            state=state,
            negative_canon=state.negative_canon
        )
        neg_for_sel = state.negative_similar
        neg_canon_sel = state.negative_canon
        state_for_score = state
    else:
        candidates = sort_candidates_by_score(
            candidates,
            {},
            state=None,
            ignore_played_soft=True,
            negative_canon={}
        )
        neg_for_sel = {}
        neg_canon_sel = {}
        state_for_score = None

    cur_artist = state.current_artist or state.seed_artist
    cur_track = state.current_track or state.seed_track

    if state.mode == "global":
        cur_artist = state.current_artist
        cur_track = state.current_track

    played_hard = state.played_hard_set if state.mode != "likes_playlist" else set()

    def _sel(cands, desired, mpa, allow, ex_ex, ex_cn, recent=None, played=None, fe=None, fc=None):
        return select_diverse(
            cands,
            desired=desired,
            disliked_keys=state.disliked_keys,
            recent_keys=state.recent_played if recent is None else recent,
            current_artist=cur_artist,
            current_track=cur_track,
            max_per_artist=mpa,
            exclude_keys=ex_ex,
            exclude_canon_keys=ex_cn,
            negative_similar=neg_for_sel,
            negative_canon=neg_canon_sel,
            played_hard_set=played_hard if played is None else played,
            failed_exact_keys=failed_exact if fe is None else fe,
            failed_canon_keys=failed_canon if fc is None else fc,
            allow_adjacent_same=allow
        )

    selected = []
    used_exact = set(existing_exact)
    used_canon = set(existing_canon)
    lrp_used = False

    if state.mode in ("artist", "likes_playlist"):
        selected, used_exact, used_canon = _sel(candidates, limit, 1000, True, existing_exact, existing_canon)
        if not selected:
            candidates = sort_candidates_by_score(
                candidates,
                neg_for_sel,
                state=state_for_score,
                ignore_played_soft=True,
                negative_canon=neg_canon_sel
            )
            selected, used_exact, used_canon = _sel(candidates, limit, 1000, True, existing_exact, existing_canon)
    else:
        selected, used_exact, used_canon = _sel(candidates, limit, 1, False, existing_exact, existing_canon)
        if len(selected) < max(8, limit // 2):
            more, used_exact, used_canon = _sel(candidates, limit - len(selected), 2, True, used_exact, used_canon)
            selected.extend(more)

        if state.mode == "likes" and state.liked_tracks:
            more, used_exact, used_canon = _sel(make_liked_track_candidates(state), max(4, limit // 4), 2, True, used_exact, used_canon)
            selected.extend(more)

    if not selected:
        lrp_used = True
        selected, used_exact, used_canon = _sel(
            lrp_sort_candidates(state, candidates),
            limit,
            3,
            True,
            existing_exact,
            existing_canon,
            recent=deque(),
            played=set()
        )

    if state.mode != "likes_playlist" and selected:
        try:
            head = await diversify_by_tags(selected[:TAG_DIVERSIFY_HEAD])
            selected = head + selected[TAG_DIVERSIFY_HEAD:]
        except Exception as e:
            logger.warning("refill tag diversify skipped: %s", e)

    state.similar_tracks_queue.extend(selected)
    added = len(state.similar_tracks_queue) - before

    logger.info(
        "refill_queue user=%s mode=%s pool=%s added=%s total=%s unique_artists=%s lrp=%s",
        user_id, state.mode, pool_size, added, len(state.similar_tracks_queue),
        unique_artist_count(list(state.similar_tracks_queue)), lrp_used
    )

    return added


async def preload_next_track(user_id):
    state = user_states.get(user_id)
    if not state:
        return

    if state.preloaded_file and not os.path.exists(state.preloaded_file):
        await clear_preloaded_file(state)

    if state.is_preloading or state.preloaded_file or state.next_pending_key:
        return

    state.is_preloading = True
    token = state.preload_generation
    generation = state.wave_generation

    try:
        for attempt in range(5):
            if state.preload_generation != token or state.wave_generation != generation:
                return

            cleanup_failed_tracks(state)

            if len(state.similar_tracks_queue) < 5:
                await refill_queue(user_id, state)

            if not state.similar_tracks_queue:
                return

            nxt = state.similar_tracks_queue[0]
            artist, title = extract_artist_name(nxt)

            if not artist or not title:
                state.similar_tracks_queue.popleft()
                continue

            key = reaction_key(artist, title)
            canon = canonical_key(artist, title)

            if key in state.disliked_keys or key in state.recent_played or canon in state.played_hard_set:
                state.similar_tracks_queue.popleft()
                continue

            if is_failed_exact(state, key) or is_failed_canon(state, canon):
                state.similar_tracks_queue.popleft()
                continue

            state.preloading_key = key
            filename = await download_track(artist, title, state.use_youtube, state.use_soundcloud)
            state.preloading_key = None

            if state.preload_generation != token or state.wave_generation != generation:
                return

            if filename:
                clear_download_failure(state, artist, title)
                if remove_first_key_from_queue(state, key):
                    state.preloaded_file = filename
                    state.preloaded_track = {
                        "artist": artist,
                        "title": title,
                        "match": nxt.get("match", "N/A"),
                        "image": nxt.get("image"),
                    }
                    return
                continue

            mark_download_failure(state, artist, title)
            remove_first_key_from_queue(state, key)

        logger.error("Preload gave up for user=%s", user_id)

    finally:
        if state.preload_generation == token and not state.preloaded_file:
            state.is_preloading = False
            state.preloading_key = None


def schedule_preload(user_id):
    task = PRELOAD_TASKS.get(user_id)
    if task and not task.done():
        return
    PRELOAD_TASKS[user_id] = asyncio.create_task(preload_next_track(user_id))


# ==================== WAVE LOGIC ====================

async def initialize_wave_by_likes(user_id):
    state = await get_or_create_state(user_id)
    await clear_preloaded_file(state, new_wave=True)
    state.similar_tracks_queue.clear()

    state.mode = "likes"
    state.session_positive_seeds = []
    state.recent_played.clear()

    if not state.liked_tracks:
        state.is_initialized = False
        return None

    cleanup_failed_tracks(state)
    fe = failed_exact_set(state)
    fc = failed_canon_set(state)

    top_seeds = state.liked_tracks[:10]
    available = [
        i for i in top_seeds
        if canonical_key(i.get("artist", ""), i.get("track", "")) not in state.played_hard_set
        and reaction_key(i.get("artist", ""), i.get("track", "")) not in fe
        and canonical_key(i.get("artist", ""), i.get("track", "")) not in fc
    ]

    seed = random.choice(available or top_seeds)

    state.current_artist = seed["artist"]
    state.current_track = seed["track"]
    state.seed_artist = seed["artist"]
    state.seed_track = seed["track"]
    state.is_initialized = True

    state.recent_played.append(reaction_key(seed["artist"], seed["track"]))
    await refill_queue(user_id, state, 18)

    return {
        "artist": state.current_artist,
        "title": state.current_track,
        "match_score": "1.0",
        "mode": state.mode,
        "seed_artist": state.seed_artist,
        "seed_track": state.seed_track,
        "image": None,
    }


async def initialize_wave_by_track(user_id, artist, track):
    state = await get_or_create_state(user_id)
    await clear_preloaded_file(state, new_wave=True)
    state.similar_tracks_queue.clear()

    state.mode = "track"
    state.current_artist = artist
    state.current_track = track
    state.seed_artist = artist
    state.seed_track = track
    state.session_positive_seeds = []
    state.is_initialized = True

    state.recent_played.clear()
    state.recent_played.append(reaction_key(artist, track))
    await refill_queue(user_id, state, 18)

    return {
        "artist": artist,
        "title": track,
        "match_score": "1.0",
        "mode": state.mode,
        "seed_artist": artist,
        "seed_track": track,
        "image": None,
    }


async def initialize_wave_by_artist(user_id, artist):
    state = await get_or_create_state(user_id)
    await clear_preloaded_file(state, new_wave=True)
    state.similar_tracks_queue.clear()

    state.mode = "artist"
    state.seed_artist = artist
    state.seed_track = None
    state.current_artist = artist
    state.current_track = None
    state.session_positive_seeds = []
    state.is_initialized = True

    state.recent_played.clear()
    await ensure_negative_similar(state)
    cleanup_failed_tracks(state)

    candidates = sort_candidates_by_score(
        await collect_artist_mode_candidates(state),
        state.negative_similar,
        state=state,
        negative_canon=state.negative_canon
    )

    fe = failed_exact_set(state)
    fc = failed_canon_set(state)

    selected, _, _ = select_diverse(
        candidates,
        desired=30,
        disliked_keys=state.disliked_keys,
        recent_keys=state.recent_played,
        current_artist=None,
        current_track=None,
        max_per_artist=1000,
        negative_similar=state.negative_similar,
        negative_canon=state.negative_canon,
        played_hard_set=state.played_hard_set,
        failed_exact_keys=fe,
        failed_canon_keys=fc,
        allow_adjacent_same=True
    )

    if not selected:
        selected, _, _ = select_diverse(
            lrp_sort_candidates(state, candidates),
            desired=30,
            disliked_keys=state.disliked_keys,
            recent_keys=deque(),
            current_artist=None,
            current_track=None,
            max_per_artist=1000,
            negative_similar=state.negative_similar,
            negative_canon=state.negative_canon,
            played_hard_set=set(),
            failed_exact_keys=fe,
            failed_canon_keys=fc,
            allow_adjacent_same=True
        )

    if selected:
        try:
            head = await diversify_by_tags(selected[:TAG_DIVERSIFY_HEAD])
            selected = head + selected[TAG_DIVERSIFY_HEAD:]
        except Exception as e:
            logger.warning("artist init tag diversify skipped: %s", e)

    if not selected:
        state.is_initialized = False
        return None

    first = selected[0]
    fa, ft = extract_artist_name(first)
    if not fa or not ft:
        state.is_initialized = False
        return None

    state.current_artist = fa
    state.current_track = ft
    state.seed_track = ft
    state.recent_played.append(reaction_key(fa, ft))
    state.similar_tracks_queue.extend(selected[1:])

    return {
        "artist": fa,
        "title": ft,
        "match_score": "1.0",
        "mode": state.mode,
        "seed_artist": state.seed_artist,
        "seed_track": state.seed_track,
        "image": first.get("image"),
    }


async def initialize_wave_by_likes_playlist(user_id, artist=None, track=None):
    state = await get_or_create_state(user_id)
    await clear_preloaded_file(state, new_wave=True)
    state.similar_tracks_queue.clear()

    state.mode = "likes_playlist"
    state.session_positive_seeds = []
    state.is_initialized = True
    state.recent_played.clear()

    if not state.liked_tracks:
        state.is_initialized = False
        return None

    chosen = None

    if artist and track:
        target_key = reaction_key(artist, track)
        for item in state.liked_tracks:
            if reaction_key(item.get("artist", ""), item.get("track", "")) == target_key:
                chosen = item
                break
        if not chosen:
            state.is_initialized = False
            return None
    else:
        chosen = state.liked_tracks[0]

    state.current_artist = chosen["artist"]
    state.current_track = chosen["track"]
    state.seed_artist = chosen["artist"]
    state.seed_track = chosen["track"]

    state.recent_played.append(reaction_key(chosen["artist"], chosen["track"]))

    cleanup_failed_tracks(state)
    fe = failed_exact_set(state)
    fc = failed_canon_set(state)

    selected, _, _ = select_diverse(
        collect_likes_playlist_candidates(state),
        desired=1000,
        disliked_keys=state.disliked_keys,
        recent_keys=state.recent_played,
        current_artist=state.current_artist,
        current_track=state.current_track,
        max_per_artist=1000,
        failed_exact_keys=fe,
        failed_canon_keys=fc,
        allow_adjacent_same=True
    )

    state.similar_tracks_queue.extend(selected)

    return {
        "artist": state.current_artist,
        "title": state.current_track,
        "match_score": "1.0",
        "mode": state.mode,
        "seed_artist": state.seed_artist,
        "seed_track": state.seed_track,
        "image": None,
    }


async def initialize_wave_by_global(user_id):
    state = await get_or_create_state(user_id)
    await clear_preloaded_file(state, new_wave=True)
    state.similar_tracks_queue.clear()

    state.mode = "global"
    state.seed_artist = "Global"
    state.seed_track = "Bot Likes Wave"
    state.current_artist = None
    state.current_track = None
    state.session_positive_seeds = []
    state.is_initialized = True

    state.recent_played.clear()
    await ensure_negative_similar(state)
    cleanup_failed_tracks(state)

    candidates = sort_candidates_by_score(
        await collect_global_mode_candidates(state),
        state.negative_similar,
        state=state,
        negative_canon=state.negative_canon
    )

    fe = failed_exact_set(state)
    fc = failed_canon_set(state)

    selected, _, _ = select_diverse(
        candidates,
        desired=30,
        disliked_keys=state.disliked_keys,
        recent_keys=state.recent_played,
        current_artist=None,
        current_track=None,
        max_per_artist=2,
        negative_similar=state.negative_similar,
        negative_canon=state.negative_canon,
        played_hard_set=state.played_hard_set,
        failed_exact_keys=fe,
        failed_canon_keys=fc,
        allow_adjacent_same=False
    )

    if not selected:
        selected, _, _ = select_diverse(
            lrp_sort_candidates(state, candidates),
            desired=30,
            disliked_keys=state.disliked_keys,
            recent_keys=deque(),
            current_artist=None,
            current_track=None,
            max_per_artist=2,
            negative_similar=state.negative_similar,
            negative_canon=state.negative_canon,
            played_hard_set=set(),
            failed_exact_keys=fe,
            failed_canon_keys=fc,
            allow_adjacent_same=True
        )

    if selected:
        try:
            head = await diversify_by_tags(selected[:TAG_DIVERSIFY_HEAD])
            selected = head + selected[TAG_DIVERSIFY_HEAD:]
        except Exception as e:
            logger.warning("global init tag diversify skipped: %s", e)

    if not selected:
        state.is_initialized = False
        return None

    first = selected[0]
    fa, ft = extract_artist_name(first)
    if not fa or not ft:
        state.is_initialized = False
        return None

    state.current_artist = fa
    state.current_track = ft
    state.recent_played.append(reaction_key(fa, ft))
    state.similar_tracks_queue.extend(selected[1:])

    return {
        "artist": fa,
        "title": ft,
        "match_score": "1.0",
        "mode": state.mode,
        "seed_artist": state.seed_artist,
        "seed_track": state.seed_track,
        "image": first.get("image"),
    }


async def initialize_wave_by_tag(user_id, tag):
    state = await get_or_create_state(user_id)
    await clear_preloaded_file(state, new_wave=True)
    state.similar_tracks_queue.clear()

    state.mode = "tag"
    state.seed_tag = tag
    state.seed_artist = None
    state.seed_track = None
    state.current_artist = None
    state.current_track = None
    state.session_positive_seeds = []
    state.is_initialized = True

    state.recent_played.clear()
    await ensure_negative_similar(state)
    cleanup_failed_tracks(state)

    candidates = sort_candidates_by_score(
        await collect_tag_mode_candidates(state),
        state.negative_similar,
        state=state,
        negative_canon=state.negative_canon
    )

    fe = failed_exact_set(state)
    fc = failed_canon_set(state)

    selected, _, _ = select_diverse(
        candidates,
        desired=30,
        disliked_keys=state.disliked_keys,
        recent_keys=state.recent_played,
        current_artist=None,
        current_track=None,
        max_per_artist=2,
        negative_similar=state.negative_similar,
        negative_canon=state.negative_canon,
        played_hard_set=state.played_hard_set,
        failed_exact_keys=fe,
        failed_canon_keys=fc,
        allow_adjacent_same=False
    )

    if not selected:
        selected, _, _ = select_diverse(
            lrp_sort_candidates(state, candidates),
            desired=30,
            disliked_keys=state.disliked_keys,
            recent_keys=deque(),
            current_artist=None,
            current_track=None,
            max_per_artist=2,
            negative_similar=state.negative_similar,
            negative_canon=state.negative_canon,
            played_hard_set=set(),
            failed_exact_keys=fe,
            failed_canon_keys=fc,
            allow_adjacent_same=False
        )

    if selected:
        try:
            head = await diversify_by_tags(selected[:TAG_DIVERSIFY_HEAD])
            selected = head + selected[TAG_DIVERSIFY_HEAD:]
        except Exception as e:
            logger.warning("tag init tag diversify skipped: %s", e)

    if not selected:
        state.is_initialized = False
        return None

    first = selected[0]
    fa, ft = extract_artist_name(first)
    if not fa or not ft:
        state.is_initialized = False
        return None

    state.current_artist = fa
    state.current_track = ft
    state.recent_played.append(reaction_key(fa, ft))
    state.similar_tracks_queue.extend(selected[1:])

    return {
        "artist": fa,
        "title": ft,
        "match_score": "1.0",
        "mode": state.mode,
        "seed_tag": tag,
        "image": first.get("image"),
    }


async def prepare_next_candidate(user_id, emergency=False, ignore_recent=False):
    state = user_states.get(user_id)
    if not state:
        return None

    touch_user(user_id)

    if state.preloaded_file and state.preloaded_track:
        meta = state.preloaded_track
        ma = meta.get("artist")
        mt = meta.get("title")

        if ma and mt:
            key = reaction_key(ma, mt)
            canon = canonical_key(ma, mt)
            bad = key in state.disliked_keys

            if not ignore_recent:
                bad = bad or key in state.recent_played or canon in state.played_hard_set

            if not bad:
                old_file = state.preloaded_file
                state.preloaded_file = None
                state.preloaded_track = None
                state.is_preloading = False

                if os.path.exists(old_file):
                    state.current_artist = ma
                    state.current_track = mt
                    clear_download_failure(state, ma, mt)
                    await record_played(user_id, state, ma, mt)
                    schedule_preload(user_id)
                    return {
                        "ready": {
                            "artist": ma,
                            "title": mt,
                            "match_score": meta.get("match", "N/A"),
                            "file": old_file,
                            "image": meta.get("image"),
                        }
                    }

        await clear_preloaded_file(state)

    if len(state.similar_tracks_queue) < 5:
        await refill_queue(user_id, state)

    cleanup_failed_tracks(state)
    fe = failed_exact_set(state)
    fc = failed_canon_set(state)

    cur_key = reaction_key(state.current_artist, state.current_track) if state.current_artist and state.current_track else None
    cur_canon = canonical_key(state.current_artist, state.current_track) if state.current_artist and state.current_track else None

    max_checks = max(25, len(state.similar_tracks_queue) + 10)
    checked = 0

    while checked < max_checks:
        if not state.similar_tracks_queue:
            await refill_queue(user_id, state)
            cleanup_failed_tracks(state)
            fe = failed_exact_set(state)
            fc = failed_canon_set(state)

            if not state.similar_tracks_queue:
                return None

            max_checks = max(max_checks, len(state.similar_tracks_queue) + 10)

        nxt = state.similar_tracks_queue[0]
        a, t = extract_artist_name(nxt)

        if not a or not t:
            state.similar_tracks_queue.popleft()
            checked += 1
            continue

        key = reaction_key(a, t)
        canon = canonical_key(a, t)

        if key in state.disliked_keys:
            state.similar_tracks_queue.popleft()
            checked += 1
            continue

        if cur_key and (key == cur_key or canon == cur_canon):
            state.similar_tracks_queue.popleft()
            checked += 1
            continue

        if not ignore_recent and (key in state.recent_played or canon in state.played_hard_set):
            state.similar_tracks_queue.popleft()
            checked += 1
            continue

        if key in fe or canon in fc:
            if emergency:
                clear_download_failure(state, a, t)
                fe.discard(key)
                fc.discard(canon)
            else:
                state.similar_tracks_queue.popleft()
                checked += 1
                continue

        if state.is_preloading and state.preloading_key == key:
            if len(state.similar_tracks_queue) > 1:
                state.similar_tracks_queue.rotate(-1)
                checked += 1
                continue
            return None

        state.next_pending_generation += 1
        state.next_pending_key = key
        state.next_pending_track = nxt

        return {
            "pending": {
                "artist": a,
                "title": t,
                "track_obj": nxt,
                "token": state.next_pending_generation,
                "wave_generation": state.wave_generation,
            }
        }

    return None


async def finalize_pending_download(user_id, pending, filename):
    state = user_states.get(user_id)
    if not state:
        return None

    token = pending.get("token")
    generation = pending.get("wave_generation")
    artist = pending.get("artist")
    title = pending.get("title")
    key = reaction_key(artist or "", title or "")

    if state.wave_generation != generation or state.next_pending_generation != token:
        state.next_pending_key = None
        state.next_pending_track = None
        return None

    state.next_pending_key = None
    state.next_pending_track = None

    if filename:
        clear_download_failure(state, artist, title)
        remove_first_key_from_queue(state, key)
        state.current_artist = artist
        state.current_track = title
        await record_played(user_id, state, artist, title)
        schedule_preload(user_id)

        track_obj = pending.get("track_obj") or {}
        return {
            "artist": artist,
            "title": title,
            "match_score": track_obj.get("match", "N/A"),
            "file": filename,
            "image": track_obj.get("image"),
        }

    mark_download_failure(state, artist, title)
    remove_first_key_from_queue(state, key)
    return None


async def build_track_payload(user_id, track_obj):
    state = user_states.get(user_id)
    file_url = await copy_to_audio_files(user_id, track_obj["file"])
    cover_url = await get_cover_for_track(track_obj["artist"], track_obj["title"], track_obj.get("image"))
    liked = track_is_liked(state, track_obj["artist"], track_obj["title"])

    return {
        "artist": track_obj["artist"],
        "title": track_obj["title"],
        "file_url": file_url,
        "cover_url": cover_url,
        "mode": state.mode if state else None,
        "seed_artist": state.seed_artist if state else None,
        "seed_track": state.seed_track if state else None,
        "seed_tag": state.seed_tag if state else None,
        "liked": liked,
        "user_id": user_id,
    }


def no_tracks_error_message(state, query_mode=None):
    mode = (state.mode if state else None) or query_mode
    msgs = {
        "global": "Не удалось подобрать следующий трек для глобальной волны. Попробуй ещё раз или смени режим.",
        "likes": "Не удалось подобрать следующий трек по твоим лайкам. Лайкни ещё треков или попробуй другой режим.",
        "likes_playlist": "Плейлист из лайков закончился или не удалось продолжить.",
        "artist": "Не удалось продолжить волну по исполнителю. Попробуй ещё раз или выбери другого исполнителя.",
        "track": "Не удалось продолжить волну по треку. Попробуй ещё раз или выбери другой трек.",
        "tag": "Не удалось продолжить волну по жанру. Попробуй другой жанр или перезапусти волну.",
    }
    return msgs.get(mode, "Не удалось найти следующий трек. Попробуй ещё раз или смени режим.")


async def start_wave_and_download(user_id, init_func, *args):
    track_obj = None

    async with get_user_action_lock(user_id):
        track_data = await init_func(user_id, *args)
        if not track_data:
            return None
        state = user_states.get(user_id)
        if not state:
            return None
        token = state.wave_generation
        artist = track_data["artist"]
        title = track_data["title"]
        image = track_data.get("image")

    filename = await download_track(artist, title, state.use_youtube, state.use_soundcloud)

    async with get_user_action_lock(user_id):
        state = user_states.get(user_id)
        if not state or state.wave_generation != token:
            return None

        if filename:
            clear_download_failure(state, artist, title)
            state.current_artist = artist
            state.current_track = title
            await record_played(user_id, state, artist, title)
            track_obj = {"artist": artist, "title": title, "file": filename, "image": image}
            schedule_preload(user_id)
        else:
            mark_download_failure(state, artist, title)
            return None

    if track_obj:
        return await build_track_payload(user_id, track_obj)

    return None


async def ensure_initialized_from_query(user_id, query_mode, query_artist, query_track, query_tag=None):
    state = user_states.get(user_id)
    if state and state.is_initialized and state.mode:
        return True

    initialized = None

    if query_mode == "artist" and query_artist:
        initialized = await initialize_wave_by_artist(user_id, query_artist)
        if not initialized:
            initialized = await initialize_wave_by_global(user_id)
    elif query_mode == "likes_playlist":
        initialized = await initialize_wave_by_likes_playlist(user_id, query_artist or None, query_track or None)
        if not initialized:
            initialized = await initialize_wave_by_global(user_id)
    elif query_mode == "likes":
        initialized = await initialize_wave_by_likes(user_id)
        if not initialized:
            initialized = await initialize_wave_by_global(user_id)
    elif query_mode == "global":
        initialized = await initialize_wave_by_global(user_id)
    elif query_mode == "tag" and query_tag:
        initialized = await initialize_wave_by_tag(user_id, query_tag)
        if not initialized:
            initialized = await initialize_wave_by_global(user_id)
    elif query_artist and query_track:
        initialized = await initialize_wave_by_track(user_id, query_artist, query_track)
    else:
        state = await get_or_create_state(user_id)
        if state.liked_tracks:
            initialized = await initialize_wave_by_likes(user_id)
            if not initialized:
                initialized = await initialize_wave_by_global(user_id)
        else:
            initialized = await initialize_wave_by_global(user_id)

    return bool(initialized)


# ==================== CORS ====================

@web.middleware
async def cors_middleware(request, handler):
    origin = cors_origin_for_request(request)

    if request.method == "OPTIONS":
        return web.Response(status=204, headers={
            "Access-Control-Allow-Origin": origin,
            "Access-Control-Allow-Methods": "GET, POST, OPTIONS",
            "Access-Control-Allow-Headers": "Content-Type, Range, X-Telegram-Init-Data, X-QuasWave-User, X-QuasWave-Expires, X-QuasWave-Sig",
            "Access-Control-Max-Age": "3600",
        })

    response = await handler(request)
    response.headers.setdefault("Access-Control-Allow-Origin", origin)
    response.headers.setdefault("Access-Control-Expose-Headers", "Content-Length, Content-Range, Accept-Ranges")
    return response


# ==================== HTTP API ====================

async def api_health(request):
    audio_files = 0
    try:
        if os.path.isdir(AUDIO_CACHE_DIR):
            audio_files = len([e for e in os.scandir(AUDIO_CACHE_DIR) if e.name.endswith(".mp3")])
    except Exception:
        pass
    return json_response({"status": "ok", "version": APP_VERSION, "users": len(user_states), "audio_files": audio_files})


async def api_state(request):
    try:
        user_id = await resolve_user_id(request, request.query.get("user_id"))
        if not user_id:
            return json_response({"error": "Unauthorized"}, status=401)
        if not check_rate_limit(user_id, request.path):
            return json_response({"error": "Too many requests"}, status=429)

        touch_user(user_id)

        async with get_user_action_lock(user_id):
            state = await get_or_create_state(user_id)
            return json_response({
                "user_id": user_id,
                "mode": state.mode,
                "seed_artist": state.seed_artist,
                "seed_track": state.seed_track,
                "seed_tag": state.seed_tag,
                "current_artist": state.current_artist,
                "current_title": state.current_track,
                "global_use_likes": state.global_use_likes,
                "use_youtube": state.use_youtube,
                "use_soundcloud": state.use_soundcloud,
                "liked": track_is_liked(state, state.current_artist, state.current_track),
            })
    except Exception as e:
        logger.error("Ошибка в api_state: %s", e, exc_info=True)
        return public_error()


async def api_settings(request):
    try:
        user_id = await resolve_user_id(request, request.query.get("user_id"))
        if not user_id:
            return json_response({"error": "Unauthorized"}, status=401)
        if not check_rate_limit(user_id, request.path):
            return json_response({"error": "Too many requests"}, status=429)

        touch_user(user_id)

        async with get_user_action_lock(user_id):
            state = await get_or_create_state(user_id)

            if request.method == "GET":
                return json_response({
                    "status": "ok",
                    "user_id": user_id,
                    "global_use_likes": state.global_use_likes,
                    "use_youtube": state.use_youtube,
                    "use_soundcloud": state.use_soundcloud,
                })

            data = {}
            try:
                if request.can_read_body:
                    data = await request.json()
                    if not isinstance(data, dict):
                        data = {}
            except Exception:
                pass

            if "global_use_likes" in data:
                val = data["global_use_likes"]
                if isinstance(val, bool):
                    gul = val
                elif isinstance(val, (int, float)):
                    gul = bool(val)
                else:
                    gul = str(val).strip().lower() in ("1", "true", "on", "yes")
                await asyncio.to_thread(db_set_settings_sync, user_id, gul)
                state.global_use_likes = gul

            if "use_youtube" in data:
                val = data["use_youtube"]
                uy = bool(val) if isinstance(val, bool) else (bool(int(val)) if isinstance(val, (int, float)) else str(val).strip().lower() in ("1", "true", "on", "yes"))
                state.use_youtube = uy
                await asyncio.to_thread(db_set_sources_sync, user_id, state.use_youtube, state.use_soundcloud)

            if "use_soundcloud" in data:
                val = data["use_soundcloud"]
                us = bool(val) if isinstance(val, bool) else (bool(int(val)) if isinstance(val, (int, float)) else str(val).strip().lower() in ("1", "true", "on", "yes"))
                state.use_soundcloud = us
                await asyncio.to_thread(db_set_sources_sync, user_id, state.use_youtube, state.use_soundcloud)

            return json_response({
                "status": "ok",
                "user_id": user_id,
                "global_use_likes": state.global_use_likes,
                "use_youtube": state.use_youtube,
                "use_soundcloud": state.use_soundcloud,
            })
    except Exception as e:
        logger.error("Ошибка в api_settings: %s", e, exc_info=True)
        return public_error()


async def api_next_track(request):
    try:
        query_artist = clean_text(request.query.get("artist") or request.query.get("seed_artist"))
        query_track = clean_text(request.query.get("track") or request.query.get("seed_track"))
        query_mode = clean_text(request.query.get("mode"), 50)
        query_tag = clean_text(request.query.get("tag") or request.query.get("seed_tag"))

        user_id = await resolve_user_id(request, request.query.get("user_id"))
        if not user_id:
            return json_response({"error": "Unauthorized"}, status=401)
        if not check_rate_limit(user_id, request.path):
            return json_response({"error": "Too many requests"}, status=429)

        touch_user(user_id)

        async with get_user_action_lock(user_id):
            initialized = await ensure_initialized_from_query(user_id, query_mode, query_artist, query_track, query_tag)
            if not initialized:
                return json_response({"error": no_tracks_error_message(user_states.get(user_id), query_mode)}, status=500)

        decision = None

        decision = await prepare_next_candidate(user_id)
        if decision and "ready" in decision:
            payload = await build_track_payload(user_id, decision["ready"])
            logger.info("Next ready payload: %s", mask_payload(payload))
            return json_response(payload)

        if decision and "pending" in decision:
            pending = decision["pending"]
            state = user_states.get(user_id)
            uy = state.use_youtube if state else True
            us = state.use_soundcloud if state else True
            filename = await download_track(pending["artist"], pending["title"], uy, us)
            async with get_user_action_lock(user_id):
                track_obj = await finalize_pending_download(user_id, pending, filename)
            if track_obj:
                payload = await build_track_payload(user_id, track_obj)
                logger.info("Next downloaded payload: %s", mask_payload(payload))
                return json_response(payload)

        # emergency fallback
        state = user_states.get(user_id)
        if state:
            purge_failed(state)
            cleaned = deque()
            ck = reaction_key(state.current_artist, state.current_track) if state.current_artist and state.current_track else None
            cc = canonical_key(state.current_artist, state.current_track) if state.current_artist and state.current_track else None
            for item in state.similar_tracks_queue:
                ia, it = extract_artist_name(item)
                if not ia or not it:
                    continue
                ik = reaction_key(ia, it)
                ic = canonical_key(ia, it)
                if ik in state.disliked_keys:
                    continue
                if ck and (ik == ck or ic == cc):
                    continue
                cleaned.append(item)
            state.similar_tracks_queue = cleaned
            if len(state.similar_tracks_queue) < 5:
                await refill_queue(user_id, state)

        decision = await prepare_next_candidate(user_id, emergency=True, ignore_recent=True)

        if decision and "ready" in decision:
            payload = await build_track_payload(user_id, decision["ready"])
            logger.info("Next emergency ready payload: %s", mask_payload(payload))
            return json_response(payload)

        if decision and "pending" in decision:
            pending = decision["pending"]
            state = user_states.get(user_id)
            uy = state.use_youtube if state else True
            us = state.use_soundcloud if state else True
            filename = await download_track(pending["artist"], pending["title"], uy, us)
            async with get_user_action_lock(user_id):
                track_obj = await finalize_pending_download(user_id, pending, filename)
            if track_obj:
                payload = await build_track_payload(user_id, track_obj)
                logger.info("Next emergency downloaded payload: %s", mask_payload(payload))
                return json_response(payload)

        return json_response({"error": no_tracks_error_message(user_states.get(user_id), query_mode)}, status=500)
    except Exception as e:
        logger.error("Критическая ошибка в api_next_track: %s", e, exc_info=True)
        return public_error()


async def api_like(request):
    try:
        user_id_str, artist, track, _, _ = await parse_json_or_query(request)
        user_id = await resolve_user_id(request, user_id_str)
        if not user_id:
            return json_response({"error": "Unauthorized"}, status=401)
        if not check_rate_limit(user_id, request.path):
            return json_response({"error": "Too many requests"}, status=429)

        touch_user(user_id)

        async with get_user_action_lock(user_id):
            state = await get_or_create_state(user_id)
            artist = clean_text(artist)
            track = clean_text(track)

            if not artist or not track:
                artist = state.current_artist
                track = state.current_track

            if not artist or not track:
                return json_response({"error": "No current track"}, status=400)

            lc, dc = await asyncio.to_thread(db_add_reaction_sync, user_id, artist, track, "like")
            apply_like_to_state(state, artist, track)
            state.current_artist = artist
            state.current_track = track

            return json_response({
                "status": "ok",
                "artist": artist,
                "track": track,
                "user_id": user_id,
                "likes_count": lc,
                "dislikes_count": dc,
                "liked": True,
            })
    except Exception as e:
        logger.error("Ошибка в api_like: %s", e, exc_info=True)
        return public_error()


async def api_unlike(request):
    try:
        user_id_str, artist, track, _, _ = await parse_json_or_query(request)
        user_id = await resolve_user_id(request, user_id_str)
        if not user_id:
            return json_response({"error": "Unauthorized"}, status=401)
        if not check_rate_limit(user_id, request.path):
            return json_response({"error": "Too many requests"}, status=429)

        touch_user(user_id)

        async with get_user_action_lock(user_id):
            state = await get_or_create_state(user_id)
            artist = clean_text(artist)
            track = clean_text(track)

            if not artist or not track:
                return json_response({"error": "No artist/track provided"}, status=400)

            lc = await asyncio.to_thread(db_remove_like_sync, user_id, artist, track)
            apply_unlike_to_state(state, artist, track)

            return json_response({
                "status": "ok",
                "artist": artist,
                "track": track,
                "user_id": user_id,
                "likes_count": lc,
                "liked": False,
            })
    except Exception as e:
        logger.error("Ошибка в api_unlike: %s", e, exc_info=True)
        return public_error()


async def api_search_tracks(request):
    try:
        user_id_str = request.query.get("user_id")
        query = ""
        artist = ""

        try:
            if request.can_read_body:
                data = await request.json()
                if isinstance(data, dict):
                    user_id_str = data.get("user_id", user_id_str)
                    query = data.get("query", "")
                    artist = data.get("artist", "")
        except Exception:
            pass

        if not query:
            query = request.query.get("query", "")
        if not artist:
            artist = request.query.get("artist", "")

        user_id = await resolve_user_id(request, user_id_str)
        if not user_id:
            return json_response({"error": "Unauthorized"}, status=401)
        if not check_rate_limit(user_id, request.path):
            return json_response({"error": "Too many requests"}, status=429)

        touch_user(user_id)
        query = clean_text(query)
        artist = clean_text(artist)

        if not query:
            return json_response({"error": "No query provided"}, status=400)

        results = await asyncio.to_thread(search_tracks, query, 12, artist or None)
        items = [{"artist": i.get("artist", ""), "track": i.get("track", ""), "listeners": i.get("listeners", 0)} for i in results]

        return json_response({"status": "ok", "query": query, "artist": artist, "items": items})
    except Exception as e:
        logger.error("Ошибка в api_search_tracks: %s", e, exc_info=True)
        return public_error()


async def api_search_artists(request):
    try:
        user_id_str = request.query.get("user_id")
        query = ""

        try:
            if request.can_read_body:
                data = await request.json()
                if isinstance(data, dict):
                    user_id_str = data.get("user_id", user_id_str)
                    query = data.get("query", "")
        except Exception:
            pass

        if not query:
            query = request.query.get("query", "")

        user_id = await resolve_user_id(request, user_id_str)
        if not user_id:
            return json_response({"error": "Unauthorized"}, status=401)
        if not check_rate_limit(user_id, request.path):
            return json_response({"error": "Too many requests"}, status=429)

        touch_user(user_id)
        query = clean_text(query)

        if not query:
            return json_response({"error": "No query provided"}, status=400)

        results = await asyncio.to_thread(search_artists, query, 12)
        items = [{"artist": i.get("artist", ""), "listeners": i.get("listeners", 0)} for i in results]

        return json_response({"status": "ok", "query": query, "items": items})
    except Exception as e:
        logger.error("Ошибка в api_search_artists: %s", e, exc_info=True)
        return public_error()


async def api_search_tags(request):
    try:
        user_id_str = request.query.get("user_id")
        query = ""

        try:
            if request.can_read_body:
                data = await request.json()
                if isinstance(data, dict):
                    user_id_str = data.get("user_id", user_id_str)
                    query = data.get("query", "")
        except Exception:
            pass

        if not query:
            query = request.query.get("query", "")

        user_id = await resolve_user_id(request, user_id_str)
        if not user_id:
            return json_response({"error": "Unauthorized"}, status=401)
        if not check_rate_limit(user_id, request.path):
            return json_response({"error": "Too many requests"}, status=429)

        touch_user(user_id)
        query = clean_text(query).strip().lower()

        if not query:
            return json_response({"error": "No query provided"}, status=400)

        query = TAG_DICT.get(query, query)
        results = await asyncio.to_thread(search_tags, query, 12)

        return json_response({"status": "ok", "query": query, "items": results})
    except Exception as e:
        logger.error("Ошибка в api_search_tags: %s", e, exc_info=True)
        return public_error()


async def api_send_track(request):
    try:
        user_id_str, artist, track, _, _ = await parse_json_or_query(request)
        user_id = await resolve_user_id(request, user_id_str)
        if not user_id:
            return json_response({"error": "Unauthorized"}, status=401)
        if not check_rate_limit(user_id, request.path):
            return json_response({"error": "Too many requests"}, status=429)

        touch_user(user_id)

        cache_path = None
        send_artist = None
        send_track = None

        async with get_user_action_lock(user_id):
            state = await get_or_create_state(user_id)
            send_artist = clean_text(artist) or state.current_artist
            send_track = clean_text(track) or state.current_track

            if not send_artist or not send_track:
                return json_response({"error": "Сейчас ничего не играет"}, status=400)

            key = reaction_key(send_artist, send_track)
            current_key = reaction_key(state.current_artist or "", state.current_track or "")

            preloaded_key = None
            if state.preloaded_track:
                preloaded_key = reaction_key(state.preloaded_track.get("artist", ""), state.preloaded_track.get("title", ""))

            allowed = (
                key == current_key
                or key in state.recent_played
                or key in state.liked_keys
                or key == preloaded_key
            )

            if not allowed:
                return json_response({"error": "Можно отправлять только текущий, недавний или лайкнутый трек"}, status=403)

            cache_path = get_cache_path(send_artist, send_track)
            if not os.path.isfile(cache_path):
                return json_response({"error": "Трек ещё не загружен на сервер. Сначала воспроизведи его, потом жми скачать."}, status=409)

        filename = f"{send_artist[:120]} - {send_track[:120]}.mp3"

        try:
            await bot.send_audio(
                chat_id=user_id,
                audio=FSInputFile(cache_path, filename=filename),
                title=send_track,
                performer=send_artist
            )
        except TelegramForbiddenError:
            return json_response({"error": "Не могу написать тебе в Telegram. Открой бота и нажми /start, потом попробуй снова."}, status=403)
        except TelegramBadRequest as e:
            msg = str(e).lower()
            if "too big" in msg or "file is too big" in msg or "413" in msg:
                return json_response({"error": "Файл слишком большой для отправки в Telegram"}, status=413)
            return public_error("Не удалось отправить трек")
        except Exception:
            return public_error()

        return json_response({"status": "ok", "artist": send_artist, "track": send_track, "user_id": user_id})
    except Exception as e:
        logger.error("Ошибка в api_send_track: %s", e, exc_info=True)
        return public_error()


async def api_dislike(request):
    try:
        user_id_str, artist, track, _, _ = await parse_json_or_query(request)
        user_id = await resolve_user_id(request, user_id_str)
        if not user_id:
            return json_response({"error": "Unauthorized"}, status=401)
        if not check_rate_limit(user_id, request.path):
            return json_response({"error": "Too many requests"}, status=429)

        touch_user(user_id)

        async with get_user_action_lock(user_id):
            state = await get_or_create_state(user_id)
            artist = clean_text(artist)
            track = clean_text(track)

            if not artist or not track:
                artist = state.current_artist
                track = state.current_track

            if not artist or not track:
                return json_response({"error": "No current track"}, status=400)

            lc, dc = await asyncio.to_thread(db_add_reaction_sync, user_id, artist, track, "dislike")
            apply_dislike_to_state(state, artist, track)

            if state.preloaded_track and reaction_key(state.preloaded_track.get("artist", ""), state.preloaded_track.get("title", "")) == reaction_key(artist, track):
                await clear_preloaded_file(state)

            state.current_artist = artist
            state.current_track = track
            schedule_preload(user_id)

            return json_response({
                "status": "ok",
                "artist": artist,
                "track": track,
                "user_id": user_id,
                "likes_count": lc,
                "dislikes_count": dc,
                "liked": False,
            })
    except Exception as e:
        logger.error("Ошибка в api_dislike: %s", e, exc_info=True)
        return public_error()


async def api_likes(request):
    try:
        user_id_str, _, _, page_str, page_size_str = await parse_json_or_query(request)
        user_id = await resolve_user_id(request, user_id_str)
        if not user_id:
            return json_response({"error": "Unauthorized"}, status=401)
        if not check_rate_limit(user_id, request.path):
            return json_response({"error": "Too many requests"}, status=429)

        touch_user(user_id)

        try:
            page = int(page_str)
            page_size = int(page_size_str)
        except ValueError:
            return json_response({"error": "Invalid pagination params"}, status=400)

        page = max(1, page)
        page_size = min(max(1, page_size), 50)

        async with get_user_action_lock(user_id):
            await get_or_create_state(user_id)
            rows, total, pages = await asyncio.to_thread(db_page_sync, user_id, "like", page, page_size)
            items = [{"artist": r[0], "track": r[1]} for r in rows]
            return json_response({"items": items, "page": page, "pages": pages, "total": total, "user_id": user_id})
    except Exception as e:
        logger.error("Ошибка в api_likes: %s", e, exc_info=True)
        return public_error()


async def api_start_track(request):
    try:
        user_id_str, artist, track, _, _ = await parse_json_or_query(request)
        user_id = await resolve_user_id(request, user_id_str)
        if not user_id:
            return json_response({"error": "Unauthorized"}, status=401)
        if not check_rate_limit(user_id, request.path):
            return json_response({"error": "Too many requests"}, status=429)

        touch_user(user_id)
        artist = clean_text(artist)
        track = clean_text(track)

        if not artist or not track:
            return json_response({"error": "No artist/track provided"}, status=400)

        payload = await start_wave_and_download(user_id, initialize_wave_by_track, artist, track)
        if not payload:
            return json_response({"error": "Не удалось запустить трек"}, status=500)

        return json_response(payload)
    except Exception as e:
        logger.error("Ошибка в api_start_track: %s", e, exc_info=True)
        return public_error()


async def api_start_artist(request):
    try:
        user_id_str, artist, _, _, _ = await parse_json_or_query(request)
        user_id = await resolve_user_id(request, user_id_str)
        if not user_id:
            return json_response({"error": "Unauthorized"}, status=401)
        if not check_rate_limit(user_id, request.path):
            return json_response({"error": "Too many requests"}, status=429)

        touch_user(user_id)
        artist = clean_text(artist)

        if not artist:
            return json_response({"error": "No artist provided"}, status=400)

        payload = await start_wave_and_download(user_id, initialize_wave_by_artist, artist)
        if not payload:
            return json_response({"error": "Не удалось запустить волну по исполнителю"}, status=500)

        return json_response(payload)
    except Exception as e:
        logger.error("Ошибка в api_start_artist: %s", e, exc_info=True)
        return public_error()


async def api_start_liked_playlist(request):
    try:
        user_id_str, artist, track, _, _ = await parse_json_or_query(request)
        user_id = await resolve_user_id(request, user_id_str)
        if not user_id:
            return json_response({"error": "Unauthorized"}, status=401)
        if not check_rate_limit(user_id, request.path):
            return json_response({"error": "Too many requests"}, status=429)

        touch_user(user_id)
        artist = clean_text(artist)
        track = clean_text(track)

        payload = await start_wave_and_download(user_id, initialize_wave_by_likes_playlist, artist or None, track or None)
        if not payload:
            return json_response({"error": "Не удалось запустить плейлист из лайков"}, status=500)

        return json_response(payload)
    except Exception as e:
        logger.error("Ошибка в api_start_liked_playlist: %s", e, exc_info=True)
        return public_error()


async def api_start_likes_wave(request):
    try:
        user_id_str, _, _, _, _ = await parse_json_or_query(request)
        user_id = await resolve_user_id(request, user_id_str)
        if not user_id:
            return json_response({"error": "Unauthorized"}, status=401)
        if not check_rate_limit(user_id, request.path):
            return json_response({"error": "Too many requests"}, status=429)

        touch_user(user_id)
        payload = await start_wave_and_download(user_id, initialize_wave_by_likes)

        if not payload:
            return json_response({"error": "Нет лайков для волны"}, status=500)

        return json_response(payload)
    except Exception as e:
        logger.error("Ошибка в api_start_likes_wave: %s", e, exc_info=True)
        return public_error()


async def api_start_global_wave(request):
    try:
        user_id_str, _, _, _, _ = await parse_json_or_query(request)
        user_id = await resolve_user_id(request, user_id_str)
        if not user_id:
            return json_response({"error": "Unauthorized"}, status=401)
        if not check_rate_limit(user_id, request.path):
            return json_response({"error": "Too many requests"}, status=429)

        touch_user(user_id)
        payload = await start_wave_and_download(user_id, initialize_wave_by_global)

        if not payload:
            return json_response({"error": "Глобальная волна пока пустая. Нужно, чтобы пользователи бота лайкали треки."}, status=500)

        return json_response(payload)
    except Exception as e:
        logger.error("Ошибка в api_start_global_wave: %s", e, exc_info=True)
        return public_error()


async def api_start_tag(request):
    try:
        user_id_str = request.query.get("user_id")
        tag = ""

        try:
            if request.can_read_body:
                data = await request.json()
                if isinstance(data, dict):
                    user_id_str = data.get("user_id", user_id_str)
                    tag = data.get("tag", "")
        except Exception:
            pass

        if not tag:
            tag = request.query.get("tag", "")

        user_id = await resolve_user_id(request, user_id_str)
        if not user_id:
            return json_response({"error": "Unauthorized"}, status=401)
        if not check_rate_limit(user_id, request.path):
            return json_response({"error": "Too many requests"}, status=429)

        touch_user(user_id)
        tag = clean_text(tag).strip().lower()

        if not tag:
            return json_response({"error": "No tag provided"}, status=400)

        tag = TAG_DICT.get(tag, tag)
        payload = await start_wave_and_download(user_id, initialize_wave_by_tag, tag)

        if not payload:
            return json_response({"error": "Не удалось запустить волну по жанру"}, status=500)

        return json_response(payload)
    except Exception as e:
        logger.error("Ошибка в api_start_tag: %s", e, exc_info=True)
        return public_error()


# ==================== AUDIO SERVER ====================

async def safe_write(resp, chunk):
    try:
        await resp.write(chunk)
        return True
    except Exception:
        return False


async def handle_audio_file(request):
    filename = request.match_info.get("filename", "")
    origin = cors_origin_for_request(request)

    if not filename or filename in (".", "..") or "/" in filename or "\\" in filename:
        return web.Response(status=400, text="Bad filename", headers={"Access-Control-Allow-Origin": origin})

    if not DEV_ALLOW_OPEN_AUDIO:
        expires_raw = request.query.get("expires")
        sig = request.query.get("sig")

        if not expires_raw or not sig:
            return web.Response(status=403, text="Missing signature", headers={"Access-Control-Allow-Origin": origin})

        try:
            expires = int(expires_raw)
        except ValueError:
            return web.Response(status=403, text="Bad signature", headers={"Access-Control-Allow-Origin": origin})

        if time.time() > expires:
            return web.Response(status=403, text="Link expired", headers={"Access-Control-Allow-Origin": origin})

        if not hmac.compare_digest(sign_audio_path(filename, expires), sig):
            return web.Response(status=403, text="Invalid signature", headers={"Access-Control-Allow-Origin": origin})

    base_dir = os.path.realpath(AUDIO_CACHE_DIR)
    filepath = os.path.realpath(os.path.join(base_dir, filename))

    if not filepath.startswith(base_dir + os.sep):
        return web.Response(status=404, text="File not found", headers={"Access-Control-Allow-Origin": origin})

    try:
        if not os.path.isfile(filepath):
            raise FileNotFoundError()
        file_size = os.path.getsize(filepath)
    except Exception:
        return web.Response(status=404, text="File not found", headers={"Access-Control-Allow-Origin": origin})

    try:
        await asyncio.to_thread(os.utime, filepath, None)
    except Exception:
        pass

    common_headers = {
        "Access-Control-Allow-Origin": origin,
        "Accept-Ranges": "bytes",
        "Cache-Control": "no-cache",
        "Content-Type": "audio/mpeg",
    }

    range_header = request.headers.get("Range")

    if range_header:
        try:
            unit, ranges = range_header.split("=", 1)
            if unit.strip().lower() != "bytes":
                raise ValueError("bad range unit")

            range_spec = ranges.split(",", 1)[0].strip()
            start_str, end_str = range_spec.split("-", 1)

            if not start_str and not end_str:
                raise ValueError("empty range")

            if start_str == "" and end_str != "":
                suffix_length = int(end_str)
                if suffix_length <= 0:
                    raise ValueError("bad suffix range")
                start = max(0, file_size - suffix_length)
                end = file_size - 1
            else:
                start = int(start_str) if start_str else 0
                end = int(end_str) if end_str else file_size - 1
        except Exception:
            headers = dict(common_headers)
            headers["Content-Range"] = f"bytes */{file_size}"
            return web.Response(status=416, headers=headers)

        if start >= file_size:
            headers = dict(common_headers)
            headers["Content-Range"] = f"bytes */{file_size}"
            return web.Response(status=416, headers=headers)

        end = min(end, file_size - 1)

        if start > end:
            headers = dict(common_headers)
            headers["Content-Range"] = f"bytes */{file_size}"
            return web.Response(status=416, headers=headers)

        length = end - start + 1
        headers = dict(common_headers)
        headers.update({
            "Content-Range": f"bytes {start}-{end}/{file_size}",
            "Content-Length": str(length),
        })

        resp = web.StreamResponse(status=206, headers=headers)
        await resp.prepare(request)

        try:
            with open(filepath, "rb") as f:
                f.seek(start)
                remaining = length
                while remaining > 0:
                    chunk = await asyncio.to_thread(f.read, min(65536, remaining))
                    if not chunk:
                        break
                    if not await safe_write(resp, chunk):
                        break
                    remaining -= len(chunk)
        except Exception as e:
            logger.warning("Audio range stream error: %s", e)

        try:
            await resp.write_eof()
        except Exception:
            pass

        return resp

    headers = dict(common_headers)
    headers["Content-Length"] = str(file_size)

    resp = web.StreamResponse(status=200, headers=headers)
    await resp.prepare(request)

    try:
        with open(filepath, "rb") as f:
            while True:
                chunk = await asyncio.to_thread(f.read, 65536)
                if not chunk:
                    break
                if not await safe_write(resp, chunk):
                    break
    except Exception as e:
        logger.warning("Audio stream error: %s", e)

    try:
        await resp.write_eof()
    except Exception:
        pass

    return resp


async def start_http_server():
    os.makedirs(AUDIO_CACHE_DIR, exist_ok=True)
    os.makedirs(DOWNLOAD_DIR, exist_ok=True)
    await cleanup_audio_cache()

    app = web.Application(middlewares=[cors_middleware], client_max_size=100 * 1024 * 1024)

    app.router.add_get("/health", api_health)
    app.router.add_get("/api/state", api_state)
    app.router.add_get("/api/settings", api_settings)
    app.router.add_post("/api/settings", api_settings)
    app.router.add_get("/api/next_track", api_next_track)
    app.router.add_post("/api/like", api_like)
    app.router.add_post("/api/unlike", api_unlike)
    app.router.add_post("/api/dislike", api_dislike)
    app.router.add_get("/api/likes", api_likes)
    app.router.add_post("/api/search_tracks", api_search_tracks)
    app.router.add_post("/api/search_artists", api_search_artists)
    app.router.add_post("/api/search_tags", api_search_tags)
    app.router.add_post("/api/send_track", api_send_track)
    app.router.add_post("/api/start_track", api_start_track)
    app.router.add_post("/api/start_artist", api_start_artist)
    app.router.add_post("/api/start_liked_playlist", api_start_liked_playlist)
    app.router.add_post("/api/start_likes_wave", api_start_likes_wave)
    app.router.add_post("/api/start_global_wave", api_start_global_wave)
    app.router.add_post("/api/start_tag", api_start_tag)
    app.router.add_get("/audio/{filename}", handle_audio_file)

    runner = web.AppRunner(app)
    await runner.setup()
    site = web.TCPSite(runner, "0.0.0.0", 8080)
    await site.start()

    logger.info("HTTP сервер запущен на 0.0.0.0:8080")


# ==================== WEBAPP SENDER / KEYBOARDS ====================

def build_player_reply_keyboard(user_id: int):
    api_b64 = base64.urlsafe_b64encode(EXTERNAL_URL.encode("utf-8")).decode("ascii").rstrip("=")
    separator = "&" if "?" in WEBAPP_URL else "?"
    auth_params = make_webapp_auth_params(user_id)
    player_url = f"{WEBAPP_URL}{separator}api_base={api_b64}&{auth_params}"

    return ReplyKeyboardMarkup(
        keyboard=[[KeyboardButton(text="▶️ Плеер", web_app=WebAppInfo(url=player_url))]],
        resize_keyboard=True,
        is_persistent=True,
    )


def truncate_text(text, limit=60):
    return text if len(text) <= limit else text[:limit - 1] + "…"


async def send_track_webapp(message, track_data):
    try:
        if not message.from_user:
            return

        artist = track_data["artist"]
        title = track_data["title"]
        filename = track_data.get("file")
        user_id = message.from_user.id

        loading_msg = await message.answer(f"Загружаю: {artist} - {title}...")

        if not filename:
            state = user_states.get(user_id)
            uy = state.use_youtube if state else True
            us = state.use_soundcloud if state else True
            filename = await download_track(artist, title, uy, us)

        if not filename:
            try:
                await loading_msg.edit_text("❌ Не удалось скачать трек.")
            except Exception:
                pass
            return

        try:
            await loading_msg.delete()
        except Exception:
            pass

        file_url = await copy_to_audio_files(user_id, filename)
        cover_url = await get_cover_for_track(artist, title, track_data.get("image"))

        state = user_states.get(user_id)
        liked = track_is_liked(state, artist, title)

        app_data = {
            "artist": artist,
            "title": title,
            "file_url": file_url,
            "cover_url": cover_url,
            "user_id": user_id,
            "mode": track_data.get("mode", "track"),
            "seed_artist": track_data.get("seed_artist", artist),
            "seed_track": track_data.get("seed_track", title),
            "seed_tag": track_data.get("seed_tag"),
            "liked": liked,
        }

        data_json = json.dumps(app_data, ensure_ascii=False)
        data_b64 = base64.urlsafe_b64encode(data_json.encode("utf-8")).decode("ascii").rstrip("=")
        api_b64 = base64.urlsafe_b64encode(EXTERNAL_URL.encode("utf-8")).decode("ascii").rstrip("=")
        session_id = uuid.uuid4().hex
        auth_params = make_webapp_auth_params(user_id)

        separator = "&" if "?" in WEBAPP_URL else "?"
        webapp_full_url = f"{WEBAPP_URL}{separator}data={data_b64}&api_base={api_b64}&ts={session_id}&{auth_params}"

        keyboard = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="▶️ Открыть плеер", web_app=WebAppInfo(url=webapp_full_url))]
        ])

        await message.answer(
            f"🎵 {artist} - {title}\nНажми кнопку ниже, чтобы открыть бесшовный плеер.",
            reply_markup=keyboard
        )

    except Exception as e:
        logger.error("WebApp error: %s", e, exc_info=True)
        try:
            await message.answer("❌ Ошибка при запуске плеера.")
        except Exception:
            pass


# ==================== REACTIONS LIST ====================

def build_reaction_keyboard(kind, page, pages):
    if pages <= 1:
        return None

    nav = []

    if page > 1:
        nav.append(InlineKeyboardButton(text="⬅️", callback_data=f"{kind}_page:{page - 1}"))

    nav.append(InlineKeyboardButton(text=f"{page}/{pages}", callback_data="noop"))

    if page < pages:
        nav.append(InlineKeyboardButton(text="➡️", callback_data=f"{kind}_page:{page + 1}"))

    return InlineKeyboardMarkup(inline_keyboard=[nav])


def format_reaction_list(kind, items, page, pages, total, user_id):
    title = "🎵 Лайки" if kind == "like" else "👎 Дизлайки"

    if not items:
        return (
            f"{title} пусты.\nuser_id={user_id}\n\n"
            "Если в мини-аппе лайки есть, а здесь пусто — мини-апп был открыт "
            "под другим user_id или вне Telegram. Открывай плеер кнопкой из бота."
        )

    lines = [f"{title}", f"user_id={user_id}", f"страница {page}/{pages}, всего {total}", ""]
    start_number = (page - 1) * REACTIONS_PAGE_SIZE + 1

    for index, item in enumerate(items):
        lines.append(f"{start_number + index}. {item[0]} — {item[1]}")

    return "\n".join(lines)


async def render_reaction_list(chat_id, kind, page, user_id, message_id=None):
    rows, total, pages = await asyncio.to_thread(db_page_sync, user_id, kind, page, REACTIONS_PAGE_SIZE)
    page = min(max(1, page), pages)

    text = format_reaction_list(kind=kind, items=rows, page=page, pages=pages, total=total, user_id=user_id)
    keyboard = build_reaction_keyboard(kind, page, pages)

    if message_id:
        try:
            await bot.edit_message_text(text=text, chat_id=chat_id, message_id=message_id, reply_markup=keyboard)
        except Exception as e:
            logger.warning("edit_message_text failed: %s", e)
    else:
        await bot.send_message(chat_id=chat_id, text=text, reply_markup=keyboard)


# ==================== ADMIN ====================

def is_admin(user_id):
    return bool(user_id) and user_id in ADMIN_USER_IDS


async def send_admin_panel(message):
    rows = await asyncio.to_thread(db_get_admin_stats_sync)

    total_users = len(rows)
    total_played = sum(int(r[5] or 0) for r in rows)
    total_likes = sum(int(r[6] or 0) for r in rows)

    header = (
        f"📊 Админка QuasWave\n"
        f"Пользователей: {total_users}\n"
        f"Всего прослушано: {total_played}\n"
        f"Всего лайков: {total_likes}\n\n"
    )

    lines = []
    getchat_used = 0

    for r in rows:
        uid = int(r[0])
        username = r[1]
        first_name = r[2]
        last_name = r[3]
        last_seen = r[4]
        played = int(r[5] or 0)
        likes = int(r[6] or 0)
        dislikes = int(r[7] or 0)

        if not username and getchat_used < ADMIN_GETCHAT_LIMIT:
            getchat_used += 1
            try:
                chat = await bot.get_chat(uid)
                username = chat.username
                first_name = first_name or chat.first_name
                last_name = last_name or getattr(chat, "last_name", None)
                await asyncio.to_thread(db_upsert_user_sync, uid, username, first_name, last_name)
            except Exception:
                pass

        name = " ".join(p for p in [first_name or "", last_name or ""] if p).strip() or "(без имени)"

        seen_short = ""
        if last_seen:
            try:
                seen_short = datetime.datetime.fromisoformat(last_seen).strftime("%d.%m %H:%M")
            except Exception:
                pass

        if username:
            line = (
                f"👤 {name} @{username}\n"
                f"   id: {uid}\n"
                f"   https://t.me/{username}\n"
                f"   ▶️ {played} | ❤️ {likes} | 👎 {dislikes}"
            )
        else:
            line = (
                f"👤 {name}\n"
                f"   id: {uid}\n"
                f"   tg://user?id={uid}\n"
                f"   ▶️ {played} | ❤️ {likes} | 👎 {dislikes}"
            )

        if seen_short:
            line += f"\n   🕒 {seen_short}"

        lines.append(line)

    if not lines:
        await message.answer(header + "Пока нет пользователей.")
        return

    chunks = []
    current = header

    for line in lines:
        if len(current) + len(line) + 2 > 3800:
            chunks.append(current)
            current = ""
        current += line + "\n\n"

    if current.strip():
        chunks.append(current)

    for i, chunk in enumerate(chunks):
        if i > 0:
            chunk = f"📊 (продолжение {i + 1}/{len(chunks)})\n\n" + chunk
        await message.answer(chunk)


# ==================== TRACK / ARTIST / TAG INPUT FLOW ====================

async def handle_track_input_message(message, state, user_input):
    if not message.from_user:
        return

    user_id = message.from_user.id

    try:
        await asyncio.to_thread(db_upsert_user_sync, user_id, message.from_user.username, message.from_user.first_name, message.from_user.last_name)
    except Exception:
        pass

    if not bot_rate_limit(user_id, "track_input", 8, 10):
        await message.answer("Слишком часто. Подожди немного.")
        return

    user_input = clean_text(user_input)
    if not user_input:
        return

    artist = None
    track = None

    for sep in (" - ", " — "):
        if sep in user_input:
            parts = user_input.split(sep, 1)
            artist = clean_text(parts[0])
            track = clean_text(parts[1])
            break

    if artist and track:
        await state.clear()
        async with get_user_action_lock(user_id):
            track_data = await initialize_wave_by_track(user_id, artist, track)
        if track_data:
            await send_track_webapp(message, track_data)
        else:
            await message.answer("❌ Не удалось запустить волну.")
        return

    loading_msg = await message.answer("🔍 Ищу варианты...")
    candidates = await asyncio.to_thread(search_tracks, user_input, 10)

    if not candidates:
        try:
            await loading_msg.edit_text("❌ Не нашел. Попробуй еще раз или /start")
        except Exception:
            pass
        return

    if len(candidates) == 1:
        try:
            await loading_msg.delete()
        except Exception:
            pass

        await state.clear()
        chosen = candidates[0]
        await message.answer(f"Найдено: {chosen['artist']} - {chosen['track']}\nЗапускаю...")

        async with get_user_action_lock(user_id):
            track_data = await initialize_wave_by_track(user_id, chosen["artist"], chosen["track"])

        if track_data:
            await send_track_webapp(message, track_data)
        else:
            await message.answer("❌ Не удалось запустить волну.")
        return

    try:
        await loading_msg.delete()
    except Exception:
        pass

    await state.set_state(WaveStates.waiting_for_track_input)
    await state.update_data(search_candidates=candidates)

    buttons = []
    for index, candidate in enumerate(candidates[:10]):
        text = truncate_text(f"{candidate['artist']} — {candidate['track']}", 60)
        buttons.append([InlineKeyboardButton(text=text, callback_data=f"choose_track:{index}")])

    buttons.append([InlineKeyboardButton(text="❌ Отмена", callback_data="cancel_search")])

    await message.answer("Нашёл несколько вариантов. Выбери трек:", reply_markup=InlineKeyboardMarkup(inline_keyboard=buttons))


async def handle_artist_input_message(message, state, user_input):
    if not message.from_user:
        return

    user_id = message.from_user.id

    try:
        await asyncio.to_thread(db_upsert_user_sync, user_id, message.from_user.username, message.from_user.first_name, message.from_user.last_name)
    except Exception:
        pass

    if not bot_rate_limit(user_id, "artist_input", 8, 10):
        await message.answer("Слишком часто. Подожди немного.")
        return

    user_input = clean_text(user_input)
    if not user_input:
        return

    loading_msg = await message.answer("🔍 Ищу исполнителя...")
    candidates = await asyncio.to_thread(search_artists, user_input, 10)

    if not candidates:
        try:
            await loading_msg.edit_text("❌ Не нашел исполнителя. Попробуй еще раз или /start")
        except Exception:
            pass
        return

    exact_first = candidates[0]["artist"].strip().lower() == user_input.lower()

    if len(candidates) == 1 or exact_first:
        try:
            await loading_msg.delete()
        except Exception:
            pass

        await state.clear()
        chosen_artist = candidates[0]["artist"]
        await message.answer(f"Выбран исполнитель: {chosen_artist}\nЗапускаю волну...")

        async with get_user_action_lock(user_id):
            track_data = await initialize_wave_by_artist(user_id, chosen_artist)

        if track_data:
            await send_track_webapp(message, track_data)
        else:
            await message.answer("❌ Не удалось найти треки для этого исполнителя.")
        return

    try:
        await loading_msg.delete()
    except Exception:
        pass

    await state.set_state(WaveStates.waiting_for_artist_input)
    await state.update_data(artist_candidates=candidates)

    buttons = []
    for index, candidate in enumerate(candidates[:10]):
        buttons.append([InlineKeyboardButton(text=truncate_text(candidate["artist"], 60), callback_data=f"choose_artist:{index}")])

    buttons.append([InlineKeyboardButton(text="❌ Отмена", callback_data="cancel_search")])

    await message.answer("Нашёл несколько исполнителей. Выбери нужного:", reply_markup=InlineKeyboardMarkup(inline_keyboard=buttons))


async def handle_tag_input_message(message, state, user_input):
    if not message.from_user:
        return

    user_id = message.from_user.id

    try:
        await asyncio.to_thread(db_upsert_user_sync, user_id, message.from_user.username, message.from_user.first_name, message.from_user.last_name)
    except Exception:
        pass

    if not bot_rate_limit(user_id, "tag_input", 8, 10):
        await message.answer("Слишком часто. Подожди немного.")
        return

    user_input = clean_text(user_input).strip().lower()
    if not user_input:
        return

    user_input = TAG_DICT.get(user_input, user_input)

    loading_msg = await message.answer("🔍 Ищу жанр...")
    candidates = await asyncio.to_thread(search_tags, user_input, 10)

    if not candidates:
        try:
            await loading_msg.edit_text("❌ Не нашёл. Попробуй по-английски: witch house, techno, ambient...")
        except Exception:
            pass
        await state.clear()
        return

    exact_first = candidates[0]["name"] == user_input

    if len(candidates) == 1 or exact_first:
        try:
            await loading_msg.delete()
        except Exception:
            pass

        await state.clear()
        chosen_tag = candidates[0]["name"]
        await message.answer(f"Выбран жанр: {chosen_tag}\nЗапускаю волну...")

        async with get_user_action_lock(user_id):
            track_data = await initialize_wave_by_tag(user_id, chosen_tag)

        if track_data:
            await send_track_webapp(message, track_data)
        else:
            await message.answer("❌ Не удалось запустить волну по жанру.")
        return

    try:
        await loading_msg.delete()
    except Exception:
        pass

    await state.set_state(WaveStates.waiting_for_tag_input)
    await state.update_data(tag_candidates=candidates)

    buttons = []
    for index, candidate in enumerate(candidates[:10]):
        buttons.append([InlineKeyboardButton(text=truncate_text(candidate["name"].title(), 60), callback_data=f"choose_tag:{index}")])

    buttons.append([InlineKeyboardButton(text="❌ Отмена", callback_data="cancel_search")])

    await message.answer("Нашёл несколько жанров. Выбери нужный:", reply_markup=InlineKeyboardMarkup(inline_keyboard=buttons))


# ==================== BOT KEYBOARDS ====================

async def build_start_keyboard(user_id):
    state = await get_or_create_state(user_id)

    toggle_text = "✅ Учитывать лайки в глобальной волне" if state.global_use_likes else "❌ Учитывать лайки в глобальной волне"
    yt_text = "📺 YouTube: вкл" if state.use_youtube else "📺 YouTube: выкл"
    sc_text = "🔊 SoundCloud: вкл" if state.use_soundcloud else "🔊 SoundCloud: выкл"

    keyboard = [
        [InlineKeyboardButton(text="🎵 Волна по моим лайкам", callback_data="wave_likes")],
        [InlineKeyboardButton(text="🎶 Волна по конкретному треку", callback_data="wave_track")],
        [InlineKeyboardButton(text="🎤 Волна по исполнителю", callback_data="wave_artist")],
        [InlineKeyboardButton(text="🎭 Волна по жанру", callback_data="wave_tag")],
        [InlineKeyboardButton(text="🌍 Глобальная волна", callback_data="wave_global")],
        [InlineKeyboardButton(text=toggle_text, callback_data="toggle_global_likes")],
        [
            InlineKeyboardButton(text=yt_text, callback_data="toggle_youtube"),
            InlineKeyboardButton(text=sc_text, callback_data="toggle_soundcloud"),
        ],
    ]

    if is_admin(user_id):
        keyboard.append([InlineKeyboardButton(text="📊 Админка", callback_data="admin_panel")])

    return InlineKeyboardMarkup(inline_keyboard=keyboard)


def is_private_message(message):
    return bool(message and message.chat and message.chat.type == "private")


def is_private_callback(callback):
    return bool(callback and callback.message and callback.message.chat and callback.message.chat.type == "private")


# ==================== BOT HANDLERS ====================

@dp.message(Command("start"), F.chat.type == "private")
async def cmd_start(message, state):
    if not message.from_user:
        return

    await state.clear()
    user_id = message.from_user.id

    try:
        await asyncio.to_thread(db_upsert_user_sync, user_id, message.from_user.username, message.from_user.first_name, message.from_user.last_name)
    except Exception:
        pass

    if user_id in user_states:
        await clear_preloaded_file(user_states[user_id], new_wave=True)
        del user_states[user_id]

    USER_STATE_LAST_SEEN.pop(user_id, None)
    USER_ACTION_LOCKS.pop(user_id, None)
    PRELOAD_TASKS.pop(user_id, None)

    await get_or_create_state(user_id)

    keyboard = await build_start_keyboard(user_id)
    admin_note = "\n/admin — админ-панель (статистика пользователей)" if is_admin(user_id) else ""

    await message.answer(
        "👋 Привет! Выбери режим.\n\n"
        "Можно просто написать название трека или 'Артист - Трек'.\n\n"
        "Глобальная волна строится по похожей музыке на лайки пользователей бота.\n\n"
        "Кнопка ▶️ Плеер внизу — открывает плеер без волны.\n\n"
        "Команды:\n"
        "/whoami — мой user_id\n"
        "/likes — лайки\n"
        "/dislikes — дизлайки\n"
        "/clearlikes — очистить лайки\n"
        "/cleardislikes — очистить дизлайки\n"
        "/reset — сбросить текущую волну"
        f"{admin_note}",
        reply_markup=keyboard,
    )

    await message.answer("▶️", reply_markup=build_player_reply_keyboard(user_id))


@dp.message(Command("whoami"), F.chat.type == "private")
async def cmd_whoami(message):
    if not message.from_user:
        return
    await message.answer(f"Твой Telegram user_id: {message.from_user.id}\nИмя: {message.from_user.full_name}")


@dp.message(Command("reset"), F.chat.type == "private")
async def cmd_reset(message):
    if not message.from_user:
        return

    user_id = message.from_user.id

    if user_id in user_states:
        await clear_preloaded_file(user_states[user_id], new_wave=True)
        del user_states[user_id]

    USER_STATE_LAST_SEEN.pop(user_id, None)
    USER_ACTION_LOCKS.pop(user_id, None)
    PRELOAD_TASKS.pop(user_id, None)

    await message.answer("🔄 Текущая волна сброшена. Лайки/дизлайки сохранены. Нажми /start")


@dp.message(Command("likes"), F.chat.type == "private")
async def cmd_likes(message):
    if not message.from_user:
        return
    await render_reaction_list(chat_id=message.chat.id, kind="like", page=1, user_id=message.from_user.id)


@dp.message(Command("dislikes"), F.chat.type == "private")
async def cmd_dislikes(message):
    if not message.from_user:
        return
    await render_reaction_list(chat_id=message.chat.id, kind="dislike", page=1, user_id=message.from_user.id)


@dp.message(Command("clearlikes"), F.chat.type == "private")
async def cmd_clear_likes(message):
    if not message.from_user:
        return

    user_id = message.from_user.id
    await asyncio.to_thread(db_clear_sync, user_id, "like")

    st = user_states.get(user_id)
    if st:
        st.liked_tracks = []
        st.liked_keys = set()
        st.session_positive_seeds = []
        st.negative_dirty = True

    await message.answer("🧹 Лайки очищены.")


@dp.message(Command("cleardislikes"), F.chat.type == "private")
async def cmd_clear_dislikes(message):
    if not message.from_user:
        return

    user_id = message.from_user.id
    await asyncio.to_thread(db_clear_sync, user_id, "dislike")

    st = user_states.get(user_id)
    if st:
        st.disliked_tracks = []
        st.disliked_keys = set()
        st.negative_similar = {}
        st.negative_canon = {}
        st.negative_dirty = False

    await message.answer("🧹 Дизлайки очищены.")


@dp.message(Command("admin"), F.chat.type == "private")
async def cmd_admin(message):
    if not message.from_user:
        return

    if not is_admin(message.from_user.id):
        await message.answer("⛔ Нет доступа.")
        return

    await send_admin_panel(message)


@dp.message(Command("cancel"), F.chat.type == "private")
async def cmd_cancel(message, state):
    await state.clear()
    await message.answer("❌ Отменено. /start")


@dp.callback_query(F.data == "admin_panel")
async def cb_admin_panel(callback):
    if not is_private_callback(callback) or not callback.from_user:
        return

    if not is_admin(callback.from_user.id):
        await callback.answer("⛔ Нет доступа", show_alert=True)
        return

    await callback.answer()

    if callback.message:
        await send_admin_panel(callback.message)


@dp.callback_query(F.data == "wave_likes")
async def start_wave_likes(callback):
    if not is_private_callback(callback) or not callback.from_user:
        return

    user_id = callback.from_user.id

    if not bot_rate_limit(user_id, "wave_likes", 6, 10):
        await callback.answer("Слишком часто", show_alert=True)
        return

    await callback.answer("Загружаю...")

    if not callback.message:
        return

    async with get_user_action_lock(user_id):
        track = await initialize_wave_by_likes(user_id)

    if track:
        await send_track_webapp(callback.message, track)
    else:
        await callback.message.answer("❌ У тебя пока нет лайков.\nОткрой плеер, лайкни несколько треков кнопкой 👍, а потом снова нажми «Волна по моим лайкам».")


@dp.callback_query(F.data == "wave_track")
async def start_wave_track(callback, state):
    if not is_private_callback(callback):
        return

    await callback.answer()

    if not callback.message:
        return

    await state.set_state(WaveStates.waiting_for_track_input)
    await callback.message.answer("🎶 Введи название трека или 'Артист - Трек':\nЕсли названий несколько — я дам выбрать.\nДля отмены: /cancel")


@dp.callback_query(F.data == "wave_artist")
async def start_wave_artist(callback, state):
    if not is_private_callback(callback):
        return

    await callback.answer()

    if not callback.message:
        return

    await state.set_state(WaveStates.waiting_for_artist_input)
    await callback.message.answer("🎤 Введи имя исполнителя:\nЕсли найдётся несколько — я дам выбрать.\nДля отмены: /cancel")


@dp.callback_query(F.data == "wave_tag")
async def start_wave_tag(callback, state):
    if not is_private_callback(callback):
        return

    await callback.answer()

    if not callback.message:
        return

    await state.set_state(WaveStates.waiting_for_tag_input)
    await callback.message.answer("🎭 Введи жанр (например: witchhouse, techno, ambient):\nLast.fm понимает жанры на английском.\nДля отмены: /cancel")


@dp.callback_query(F.data == "wave_global")
async def start_wave_global(callback):
    if not is_private_callback(callback) or not callback.from_user:
        return

    user_id = callback.from_user.id

    if not bot_rate_limit(user_id, "wave_global", 6, 10):
        await callback.answer("Слишком часто", show_alert=True)
        return

    await callback.answer("Загружаю глобальную волну...")

    if not callback.message:
        return

    async with get_user_action_lock(user_id):
        track = await initialize_wave_by_global(user_id)

    if track:
        await send_track_webapp(callback.message, track)
    else:
        await callback.message.answer("❌ Глобальная волна пока пустая.\nНужно, чтобы пользователи бота лайкали треки.")


@dp.callback_query(F.data == "toggle_global_likes")
async def toggle_global_likes(callback):
    if not is_private_callback(callback) or not callback.from_user:
        return

    user_id = callback.from_user.id

    async with get_user_action_lock(user_id):
        st = await get_or_create_state(user_id)
        new_value = not st.global_use_likes
        st.global_use_likes = new_value
        await asyncio.to_thread(db_set_settings_sync, user_id, new_value)

    await callback.answer("Глобальная волна теперь учитывает твои лайки" if new_value else "Глобальная волна больше не учитывает твои лайки")

    if callback.message:
        try:
            await callback.message.edit_reply_markup(reply_markup=await build_start_keyboard(user_id))
        except Exception as e:
            logger.warning("toggle_global_likes edit failed: %s", e)


@dp.callback_query(F.data == "toggle_youtube")
async def toggle_youtube(callback):
    if not is_private_callback(callback) or not callback.from_user:
        return

    user_id = callback.from_user.id

    async with get_user_action_lock(user_id):
        st = await get_or_create_state(user_id)
        st.use_youtube = not st.use_youtube
        await asyncio.to_thread(db_set_sources_sync, user_id, st.use_youtube, st.use_soundcloud)

    await callback.answer("YouTube: вкл" if st.use_youtube else "YouTube: выкл")

    if callback.message:
        try:
            await callback.message.edit_reply_markup(reply_markup=await build_start_keyboard(user_id))
        except Exception as e:
            logger.warning("toggle_youtube edit failed: %s", e)


@dp.callback_query(F.data == "toggle_soundcloud")
async def toggle_soundcloud(callback):
    if not is_private_callback(callback) or not callback.from_user:
        return

    user_id = callback.from_user.id

    async with get_user_action_lock(user_id):
        st = await get_or_create_state(user_id)
        st.use_soundcloud = not st.use_soundcloud
        await asyncio.to_thread(db_set_sources_sync, user_id, st.use_youtube, st.use_soundcloud)

    await callback.answer("SoundCloud: вкл" if st.use_soundcloud else "SoundCloud: выкл")

    if callback.message:
        try:
            await callback.message.edit_reply_markup(reply_markup=await build_start_keyboard(user_id))
        except Exception as e:
            logger.warning("toggle_soundcloud edit failed: %s", e)


@dp.callback_query(F.data.startswith("choose_track:"))
async def choose_track(callback, state):
    if not is_private_callback(callback) or not callback.from_user:
        return

    user_id = callback.from_user.id

    if not bot_rate_limit(user_id, "choose_track", 8, 10):
        await callback.answer("Слишком часто", show_alert=True)
        return

    await callback.answer()

    if not callback.message:
        return

    try:
        index = int(callback.data.split(":", 1)[1])
    except Exception:
        await callback.message.answer("❌ Не понял выбор. Нажми /start")
        await state.clear()
        return

    data = await state.get_data()
    candidates = data.get("search_candidates", [])

    if index < 0 or index >= len(candidates):
        await callback.message.answer("❌ Вариант уже протух. Нажми /start")
        await state.clear()
        return

    chosen = candidates[index]
    await state.clear()

    await callback.message.answer(f"Выбрано: {chosen['artist']} - {chosen['track']}\nЗапускаю...")

    async with get_user_action_lock(user_id):
        track_data = await initialize_wave_by_track(user_id, chosen["artist"], chosen["track"])

    if track_data:
        await send_track_webapp(callback.message, track_data)
    else:
        await callback.message.answer("❌ Не удалось запустить волну.")


@dp.callback_query(F.data.startswith("choose_artist:"))
async def choose_artist(callback, state):
    if not is_private_callback(callback) or not callback.from_user:
        return

    user_id = callback.from_user.id

    if not bot_rate_limit(user_id, "choose_artist", 8, 10):
        await callback.answer("Слишком часто", show_alert=True)
        return

    await callback.answer()

    if not callback.message:
        return

    try:
        index = int(callback.data.split(":", 1)[1])
    except Exception:
        await callback.message.answer("❌ Не понял выбор. Нажми /start")
        await state.clear()
        return

    data = await state.get_data()
    candidates = data.get("artist_candidates", [])

    if index < 0 or index >= len(candidates):
        await callback.message.answer("❌ Вариант уже протух. Нажми /start")
        await state.clear()
        return

    chosen = candidates[index]
    chosen_artist = chosen.get("artist")
    await state.clear()

    await callback.message.answer(f"Выбран исполнитель: {chosen_artist}\nЗапускаю волну...")

    async with get_user_action_lock(user_id):
        track_data = await initialize_wave_by_artist(user_id, chosen_artist)

    if track_data:
        await send_track_webapp(callback.message, track_data)
    else:
        await callback.message.answer("❌ Не удалось найти треки для этого исполнителя.")


@dp.callback_query(F.data.startswith("choose_tag:"))
async def choose_tag(callback, state):
    if not is_private_callback(callback) or not callback.from_user:
        return

    user_id = callback.from_user.id

    if not bot_rate_limit(user_id, "choose_tag", 8, 10):
        await callback.answer("Слишком часто", show_alert=True)
        return

    await callback.answer()

    if not callback.message:
        return

    try:
        index = int(callback.data.split(":", 1)[1])
    except Exception:
        await callback.message.answer("❌ Не понял выбор. Нажми /start")
        await state.clear()
        return

    data = await state.get_data()
    candidates = data.get("tag_candidates", [])

    if index < 0 or index >= len(candidates):
        await callback.message.answer("❌ Вариант уже протух. Нажми /start")
        await state.clear()
        return

    chosen = candidates[index]
    chosen_tag = chosen.get("name")
    await state.clear()

    await callback.message.answer(f"Выбран жанр: {chosen_tag}\nЗапускаю волну...")

    async with get_user_action_lock(user_id):
        track_data = await initialize_wave_by_tag(user_id, chosen_tag)

    if track_data:
        await send_track_webapp(callback.message, track_data)
    else:
        await callback.message.answer("❌ Не удалось запустить волну по жанру.")


@dp.callback_query(F.data == "cancel_search")
async def cancel_search(callback, state):
    if not is_private_callback(callback):
        return

    await callback.answer()
    await state.clear()

    if callback.message:
        await callback.message.answer("❌ Отменено. /start")


@dp.callback_query(F.data.startswith("like_page:"))
async def cb_likes_page(callback):
    if not is_private_callback(callback) or not callback.from_user:
        return

    await callback.answer()

    if not callback.message:
        return

    try:
        page = int(callback.data.split(":", 1)[1])
    except Exception:
        page = 1

    await render_reaction_list(
        chat_id=callback.message.chat.id,
        kind="like",
        page=page,
        user_id=callback.from_user.id,
        message_id=callback.message.message_id
    )


@dp.callback_query(F.data.startswith("dislike_page:"))
async def cb_dislikes_page(callback):
    if not is_private_callback(callback) or not callback.from_user:
        return

    await callback.answer()

    if not callback.message:
        return

    try:
        page = int(callback.data.split(":", 1)[1])
    except Exception:
        page = 1

    await render_reaction_list(
        chat_id=callback.message.chat.id,
        kind="dislike",
        page=page,
        user_id=callback.from_user.id,
        message_id=callback.message.message_id
    )


@dp.callback_query(F.data == "noop")
async def cb_noop(callback):
    await callback.answer()


@dp.message(WaveStates.waiting_for_track_input, F.text, F.chat.type == "private")
async def process_track_input(message, state):
    if not message.text or message.text.startswith("/"):
        return
    await handle_track_input_message(message, state, message.text)


@dp.message(WaveStates.waiting_for_artist_input, F.text, F.chat.type == "private")
async def process_artist_input(message, state):
    if not message.text or message.text.startswith("/"):
        return
    await handle_artist_input_message(message, state, message.text)


@dp.message(WaveStates.waiting_for_tag_input, F.text, F.chat.type == "private")
async def process_tag_input(message, state):
    if not message.text or message.text.startswith("/"):
        return
    await handle_tag_input_message(message, state, message.text)


@dp.message(StateFilter(None), F.text, F.chat.type == "private")
async def any_text_search(message, state):
    if not message.text or message.text.startswith("/"):
        return
    await handle_track_input_message(message, state, message.text)


# ==================== CLEANUP ====================

async def maintenance_loop():
    while True:
        await asyncio.sleep(900)

        now = time.time()

        for uid in list(user_states.keys()):
            last_seen = USER_STATE_LAST_SEEN.get(uid, now)
            if now - last_seen > 3600:
                lock = USER_ACTION_LOCKS.get(uid)
                if lock and lock.locked():
                    continue
                user_states.pop(uid, None)
                USER_STATE_LAST_SEEN.pop(uid, None)
                USER_ACTION_LOCKS.pop(uid, None)
                PRELOAD_TASKS.pop(uid, None)

        if len(download_locks) > 10000:
            for lk in list(download_locks.keys()):
                lock = download_locks.get(lk)
                if lock and not lock.locked():
                    download_locks.pop(lk, None)

        if len(RATE_LIMIT_STATE) > 20000:
            for key in list(RATE_LIMIT_STATE.keys()):
                if not RATE_LIMIT_STATE[key]:
                    RATE_LIMIT_STATE.pop(key, None)

        if len(BOT_RATE_STATE) > 20000:
            for key in list(BOT_RATE_STATE.keys()):
                if not BOT_RATE_STATE[key]:
                    BOT_RATE_STATE.pop(key, None)

        try:
            await cleanup_audio_cache()
        except Exception as e:
            logger.warning("cleanup_audio_cache failed: %s", e)

        logger.info(
            "Cleanup: users=%s download_locks=%s rate_keys=%s bot_rate_keys=%s",
            len(user_states), len(download_locks), len(RATE_LIMIT_STATE), len(BOT_RATE_STATE)
        )


# ==================== MAIN ====================

async def main():
    logger.info("Запуск бота и HTTP сервера...")
    log_startup_warnings()

    await asyncio.to_thread(init_db_sync)
    await start_http_server()

    maintenance_task = asyncio.create_task(maintenance_loop())

    logger.info("Бот запущен и готов к работе")

    try:
        await dp.start_polling(bot)
    finally:
        maintenance_task.cancel()


if __name__ == "__main__":
    asyncio.run(main())
