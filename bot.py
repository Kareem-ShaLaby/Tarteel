"""ترتيل | Tarteel — بوت تليجرام لتنظيم الورد اليومي من المصحف.

كل مستخدم بيحدد عدد الصفحات في اليوم (أو هدف ختمة) وميعاد التذكير، والبوت
بيبعتله صفحات ورد النهاردة بس من ملف المصحف PDF بتاعك، وبينبّهه قبل الصلوات.

التخزين: كل البيانات في ملف JSON مضغوط (zip) واحد. أي ما بيتغير، البوت بيرفع
الملف في جروب خاص على تليجرام وبيثبّته. وأول ما البوت يشتغل تاني بيقرا الملف
المثبّت، فمفيش حاجة بتضيع لو السيرفر اتغيّر أو البوت اتعمله ريستارت.
"""
import asyncio
import copy
import html
import io
import json
import logging
import math
import os
import re
import zipfile
from contextlib import suppress
from datetime import datetime, time, timedelta, timezone
from pathlib import Path
from zoneinfo import ZoneInfo

import fitz# PyMuPDF
from dotenv import load_dotenv
from telegram import (
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    InputMediaPhoto,
    KeyboardButton,
    ReplyKeyboardMarkup,
    ReplyKeyboardRemove,
    Update,
)
from telegram.error import BadRequest, Forbidden, RetryAfter, TelegramError
from telegram.ext import (
    Application,
    CallbackQueryHandler,
    ChatMemberHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    TypeHandler,
    filters,
)

from prayer import PRAYERS, next_prayer

load_dotenv()
logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
log = logging.getLogger("tarteel")

# حط توكن البوت (من @BotFather) مكان الكلام اللي بين العلامتين، أو سيبه وحطه
# في متغير البيئة BOT_TOKEN. متشاركش الملف ده مع حد ومترفعوش على مكان عام.
BOT_TOKEN = os.getenv("BOT_TOKEN", "PASTE_YOUR_BOT_TOKEN_HERE")
QURAN_PDF = os.getenv("QURAN_PDF", "quran.pdf")
# لو الـ PDF فيه صفحات غلاف/مقدمة قبل صفحة ١ من المصحف، حط عددها هنا.
PDF_OFFSET = int(os.getenv("PDF_OFFSET", "0"))
TOTAL_PAGES = int(os.getenv("TOTAL_PAGES", "604"))
DEFAULT_TZ = os.getenv("DEFAULT_TZ", "Africa/Cairo")
CACHE_DIR = Path(os.getenv("CACHE_DIR", "page_cache"))
CACHE_DIR.mkdir(exist_ok=True)
ZOOM = float(os.getenv("RENDER_ZOOM", "2.0"))

# الجروب اللي بيتثبّت فيه ملف النسخة الاحتياطية (البوت لازم يكون أدمن فيه
# بصلاحية تثبيت الرسايل ومسحها).
BACKUP_CHAT_ID = int(os.getenv("BACKUP_CHAT_ID", "-1004383995976"))
BACKUP_NAME = "tarteel_data.zip"      # الملف المضغوط اللي بيتثبّت في الجروب
LEGACY_NAME = "tarteel_data.json"     # النسخ القديمة (JSON عادي) لسه بتتقرا
JSON_ENTRY = "tarteel_data.json"      # اسم الملف جوه الـ zip
MAX_JSON_BYTES = 50 * 1024 * 1024     # حماية من zip ضخم بشكل مريب
LOCAL_COPY = Path(os.getenv("LOCAL_COPY", "tarteel_data.zip"))
SAVE_INTERVAL = int(os.getenv("SAVE_INTERVAL", "30"))  # ثواني بين كل فحص للنسخة الاحتياطية
# أرقام تليجرام (ID) للأدمنز اللي يقدروا يستخدموا /health و /backup من أي مكان.
# أي حد جوه جروب النسخ الاحتياطي أدمن تلقائياً.
ADMIN_IDS = {940770584} | {
    int(x) for x in os.getenv("ADMIN_IDS", "").replace(" ", "").split(",") if x
}
STATS_KEEP_DAYS = 60

# طابور الإرسال: كل التذكيرات والتنبيهات بتعدّي منه بفاصل بسيط عشان حدود تليجرام.
SEND_GAP = float(os.getenv("SEND_GAP", "0.35"))  # ثواني بين كل مستخدم
SEND_RETRIES = 3
RETRY_PAD = 1.0  # ثواني زيادة فوق مدة الانتظار اللي تليجرام بيطلبها

MIN_GOAL_DAYS = -(-TOTAL_PAGES // 100)  # أقصى ورد ١٠٠ صفحة في اليوم
MAX_GOAL_DAYS = 365

PRAYER_AR = {
    "fajr": "الفجر",
    "dhuhr": "الظهر",
    "asr": "العصر",
    "maghrib": "المغرب",
    "isha": "العشاء",
}
WARN_STAGES = (60, 30)  # دقايق قبل الصلاة
WARN_WINDOW = 5         # لو التيك اتأخر (ريستارت مثلاً) لسه نبعت لحد ٥ دقايق بعد الميعاد

# (الاسم، خط العرض، خط الطول، المنطقة الزمنية)
CITIES = [
    ("القاهرة", 30.0444, 31.2357, "Africa/Cairo"),
    ("الجيزة", 30.0131, 31.2089, "Africa/Cairo"),
    ("الإسكندرية", 31.2001, 29.9187, "Africa/Cairo"),
    ("طنطا", 30.7865, 31.0004, "Africa/Cairo"),
    ("المنصورة", 31.0409, 31.3785, "Africa/Cairo"),
    ("بورسعيد", 31.2653, 32.3019, "Africa/Cairo"),
    ("السويس", 29.9668, 32.5498, "Africa/Cairo"),
    ("الإسماعيلية", 30.5965, 32.2715, "Africa/Cairo"),
    ("أسيوط", 27.1809, 31.1837, "Africa/Cairo"),
    ("الأقصر", 25.6872, 32.6396, "Africa/Cairo"),
    ("أسوان", 24.0889, 32.8998, "Africa/Cairo"),
    ("الرياض", 24.7136, 46.6753, "Asia/Riyadh"),
    ("جدة", 21.4858, 39.1925, "Asia/Riyadh"),
    ("مكة", 21.3891, 39.8579, "Asia/Riyadh"),
    ("المدينة", 24.5247, 39.5692, "Asia/Riyadh"),
    ("دبي", 25.2048, 55.2708, "Asia/Dubai"),
    ("الكويت", 29.3759, 47.9774, "Asia/Kuwait"),
    ("الدوحة", 25.2854, 51.5310, "Asia/Qatar"),
    ("عمّان", 31.9454, 35.9284, "Asia/Amman"),
]
# مناطق زمنية بس (من غير مدينة) — تنبيهات الصلاة محتاجة مدينة أو موقع.
ZONES = [
    ("لندن", "Europe/London"),
    ("نيويورك", "America/New_York"),
    ("إسطنبول", "Europe/Istanbul"),
]
NEAREST_CITY_KM = 400
TZ_LABELS = {
    "Africa/Cairo": "توقيت القاهرة",
    "Asia/Riyadh": "توقيت الرياض",
    "Asia/Dubai": "توقيت دبي",
    "Asia/Kuwait": "توقيت الكويت",
    "Asia/Qatar": "توقيت الدوحة",
    "Asia/Amman": "توقيت عمّان",
    "Europe/London": "توقيت لندن",
    "America/New_York": "توقيت نيويورك",
    "Europe/Istanbul": "توقيت إسطنبول",
}

# ───────────────────────── أرقام عربي ─────────────────────────
_TO_AR = str.maketrans("0123456789.", "٠١٢٣٤٥٦٧٨٩٫")
_TO_EN = str.maketrans("٠١٢٣٤٥٦٧٨٩٫", "0123456789.")


def ar(x) -> str:
    """رقم/نص بأرقام عربي."""
    return str(x).translate(_TO_AR)


def num(x: float) -> str:
    s = f"{x:.1f}"
    if s.endswith(".0"):
        s = s[:-2]
    return ar(s)


def en_digits(text: str) -> str:
    return text.translate(_TO_EN)


def tz_label(tz: str) -> str:
    """اسم المنطقة بالعربي للمناطق الجاهزة، والاسم الأصلي لو كتبها المستخدم بنفسه."""
    return TZ_LABELS.get(tz, tz)


def fmt12(h: int, m: int) -> str:
    """الساعة بنظام ١٢ ساعة بالعربي: ١١:٣٨ ص."""
    return f"{ar(h % 12 or 12)}:{ar(f'{m:02d}')} {'ص' if h < 12 else 'م'}"


# ───────────────────────── الداتا (JSON) ─────────────────────────
DEFAULTS = {
    "pages_per_day": 5,
    "current_page": 1,
    "remind_time": "08:00",
    "tz": DEFAULT_TZ,
    "reminders_on": True,
    "streak": 0,
    "last_done": None,
    "last_sent": None,  # آخر يوم (بتوقيته) ورد النهاردة اتبعتله فيه
    "khatmas": 0,
    # هدف الختمة
    "goal_days": None,
    "goal_start": None,
    "goal_read": 0,
    # المكان وتنبيهات الصلاة (الإحداثيات متقرّبة لخانتين عشان الخصوصية)
    "city": None,
    "lat": None,
    "lon": None,
    "prayer_on": False,
    "prayers": {p: True for p in PRAYERS},
    # المستخدم عامل بلوك للبوت
    "blocked": False,
}

state: dict = {"version": 3, "updated_at": None, "users": {}, "stats": {}}
# كل تغيير بيزوّد revision بواحد. النسخة الاحتياطية "متسخة" (dirty) طول ما
# revision مختلف عن saved_revision، فأي تغيير بيحصل أثناء الرفع مبيضيعش أبداً.
revision = 0
saved_revision = 0
restored = False  # مفيش رفع قبل قراءة النسخة المثبّتة (عشان منكتبش داتا فاضية فوقها)
backup_msg_id: int | None = None
save_lock: asyncio.Lock | None = None
APP: Application | None = None
outbox: "Outbox | None" = None
outbox_task: asyncio.Task | None = None


def utc_stamp() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%S.%fZ")


def now_utc() -> datetime:
    return datetime.now(timezone.utc)


def mark_dirty():
    global revision
    revision += 1
    state["updated_at"] = utc_stamp()


def is_dirty() -> bool:
    return revision != saved_revision


def new_user(chat_id: int) -> dict:
    return {"chat_id": chat_id, **copy.deepcopy(DEFAULTS)}


def get_user(chat_id: int) -> dict:
    key = str(chat_id)
    u = state["users"].get(key)
    if u is None:
        u = new_user(chat_id)
        state["users"][key] = u
        sync_catchup_marker(u)  # مستخدم جديد مفوّتش حاجة
        mark_dirty()
    return u


def update_user(chat_id: int, **fields):
    get_user(chat_id).update(fields)
    mark_dirty()


# ───────────────────────── إحصائيات ─────────────────────────
def stats_day() -> str:
    """تاريخ اليوم بتوقيت الإحصائيات (توقيت DEFAULT_TZ)."""
    return datetime.now(ZoneInfo(DEFAULT_TZ)).strftime("%Y-%m-%d")


def day_stats(day: str) -> dict:
    stats = state.setdefault("stats", {})
    d = stats.get(day)
    if d is None:
        d = stats[day] = {"active": [], "done": 0, "pages": 0}
        while len(stats) > STATS_KEEP_DAYS:
            del stats[min(stats)]
    return d


def record_active(chat_id: int):
    d = day_stats(stats_day())
    if chat_id not in d["active"]:
        d["active"].append(chat_id)
        mark_dirty()


def record_done(chat_id: int, pages: int):
    d = day_stats(stats_day())
    if chat_id not in d["active"]:
        d["active"].append(chat_id)
    d["done"] += 1
    d["pages"] += pages
    mark_dirty()


def window_days(n: int, today: str) -> list[str]:
    """آخر n يوم (من أول يوم فيه داتا، عشان الأيام الفاضية قبل البداية متأثرش المتوسط)."""
    stats = state.get("stats", {})
    first = min(stats) if stats else today
    base = datetime.strptime(today, "%Y-%m-%d")
    days = [(base - timedelta(days=i)).strftime("%Y-%m-%d") for i in range(n)]
    return [d for d in days if d >= first] or [today]


def health_report(today: str | None = None) -> dict:
    today = today or stats_day()
    stats = state.get("stats", {})

    def agg(n: int) -> dict:
        days = window_days(n, today)
        k = len(days)
        active = sum(len(stats.get(d, {}).get("active", [])) for d in days)
        done = sum(stats.get(d, {}).get("done", 0) for d in days)
        pages = sum(stats.get(d, {}).get("pages", 0) for d in days)
        return {
            "requested": n,
            "days": k,
            "active": active / k,
            "done": done / k,
            "pages": pages / k,
            "pages_per_finisher": pages / done if done else 0.0,
        }

    t = stats.get(today, {})
    users = list(state["users"].values())
    live = [u for u in users if not u.get("blocked")]
    return {
        "total_users": len(users),
        "blocked": len(users) - len(live),
        "reminders_on": sum(1 for u in live if u["reminders_on"]),
        "prayer_on": sum(1 for u in live if u.get("prayer_on")),
        "goal": sum(1 for u in live if u.get("goal_days")),
        "today": {
            "active": len(t.get("active", [])),
            "done": t.get("done", 0),
            "pages": t.get("pages", 0),
        },
        "d7": agg(7),
        "d30": agg(30),
    }


def format_health(r: dict) -> str:
    def block(title: str, a: dict) -> str:
        note = ""
        if a["days"] < a["requested"]:
            note = f"\n(الداتا من {ar(a['days'])} يوم بس لحد دلوقتي)"
        return (
            f"<b>{title}</b>{note}\n"
            f"• مستخدمين نشطين: {num(a['active'])}\n"
            f"• أوراد اتخلّصت: {num(a['done'])}\n"
            f"• صفحات اتقرت: {num(a['pages'])}\n"
            f"• متوسط الصفحات للي خلّص وردُه: {num(a['pages_per_finisher'])}"
        )

    t = r["today"]
    return (
        "📊 <b>حالة ترتيل</b>\n\n"
        f"👥 إجمالي المستخدمين: {ar(r['total_users'])}\n"
        f"🚫 حاظرين البوت: {ar(r['blocked'])}\n"
        f"🔔 التذكير شغّال عند: {ar(r['reminders_on'])}\n"
        f"🕌 تنبيهات الصلاة شغّالة عند: {ar(r['prayer_on'])}\n"
        f"🎯 عندهم هدف ختمة: {ar(r['goal'])}\n\n"
        "<b>النهاردة</b>\n"
        f"• مستخدمين نشطين: {ar(t['active'])}\n"
        f"• أوراد اتخلّصت: {ar(t['done'])}\n"
        f"• صفحات اتقرت: {ar(t['pages'])}\n\n"
        + block("متوسط آخر ٧ أيام (في اليوم)", r["d7"])
        + "\n\n"
        + block("متوسط آخر ٣٠ يوم (في اليوم)", r["d30"])
    )


# ───────────────────────── النسخ الاحتياطي ─────────────────────────
def pack_state(data: bytes) -> bytes:
    """JSON -> zip (مضغوط)."""
    buf = io.BytesIO()
    with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED, compresslevel=9) as zf:
        zf.writestr(JSON_ENTRY, data)
    return buf.getvalue()


def unpack_state(blob: bytes) -> bytes:
    """zip -> JSON. ولو الملف JSON عادي (نسخة قديمة) بيرجعه زي ما هو."""
    if zipfile.is_zipfile(io.BytesIO(blob)):
        with zipfile.ZipFile(io.BytesIO(blob)) as zf, zf.open(JSON_ENTRY) as f:
            raw = f.read(MAX_JSON_BYTES + 1)
        if len(raw) > MAX_JSON_BYTES:
            raise ValueError("backup too large")
        return raw
    return blob


def local_today(tz: str) -> str:
    try:
        return datetime.now(ZoneInfo(tz)).strftime("%Y-%m-%d")
    except Exception:
        return datetime.now(ZoneInfo(DEFAULT_TZ)).strftime("%Y-%m-%d")


def parse_state(blob: bytes) -> dict:
    s = json.loads(unpack_state(blob).decode("utf-8"))
    if not isinstance(s, dict) or not isinstance(s.get("users"), dict):
        raise ValueError("not a Tarteel backup file")
    s.setdefault("stats", {})
    for key, u in s["users"].items():
        u["chat_id"] = int(key)
        if "last_sent" not in u:
            # نسخة قديمة قبل التعويض: منبعتش "تعويض" لحد في أول تشغيل بعد الترقية.
            u["last_sent"] = local_today(u.get("tz", DEFAULT_TZ))
        for k, v in DEFAULTS.items():
            u.setdefault(k, copy.deepcopy(v))
        for p in PRAYERS:
            u["prayers"].setdefault(p, True)
    return s


def newest(a: dict | None, b: dict | None) -> dict | None:
    if a is None:
        return b
    if b is None:
        return a
    return a if (a.get("updated_at") or "") >= (b.get("updated_at") or "") else b


async def restore_state(bot):
    """بيحمّل النسخة المثبّتة من الجروب (ولو النسخة المحلية أحدث بياخدها)."""
    global state, backup_msg_id, saved_revision, restored
    remote = None
    try:
        chat = await bot.get_chat(BACKUP_CHAT_ID)
    except TelegramError as e:
        raise RuntimeError(
            f"Cannot reach backup group {BACKUP_CHAT_ID}: {e}. "
            "Add the bot to the group first."
        ) from e

    pm = chat.pinned_message
    if pm is not None and pm.document and pm.document.file_name in (BACKUP_NAME, LEGACY_NAME):
        try:
            f = await pm.document.get_file()
            remote = parse_state(bytes(await f.download_as_bytearray()))
            backup_msg_id = pm.message_id
            log.info("Restored %d users from pinned backup.", len(remote["users"]))
        except Exception as e:
            # مفيش بدء بداتا فاضية فوق نسخة معرفناش نقراها.
            raise RuntimeError(f"Pinned backup exists but could not be read: {e}") from e
    elif pm is not None:
        log.warning("Latest pinned message in the group is not a Tarteel backup; ignoring it.")
    else:
        log.info("No pinned backup found; starting fresh.")

    local = None
    if LOCAL_COPY.exists():
        try:
            local = parse_state(LOCAL_COPY.read_bytes())
        except Exception as e:
            log.warning("Local copy unreadable: %s", e)

    chosen = newest(remote, local)
    if chosen is not None:
        state = chosen
    saved_revision = revision
    restored = True
    if remote is None or chosen is not remote:
        mark_dirty()  # مفيش نسخة مثبّتة، أو النسخة المحلية أحدث -> ارفعها


async def flush(bot, force: bool = False):
    """بيرفع الـ zip للجروب ويثبّته ويمسح النسخة القديمة.

    - بيشتغل واحد واحد (save_lock)، فمفيش رفعتين في نفس الوقت.
    - اللقطة (snapshot) واتسجّل رقم revision بتاعها في نفس اللحظة من غير await،
      فالملف دايماً متسق. ولو حصل تغيير أثناء الرفع، revision بيبقى أكبر من
      saved_revision والدورة الجاية بترفعه.
    """
    global saved_revision, backup_msg_id
    if not restored:
        log.warning("flush skipped: backup not restored yet.")
        return
    async with save_lock:
        if not force and revision == saved_revision:
            return  # حد تاني رفع قبلنا ومفيش جديد
        snap_rev = revision
        data = json.dumps(state, ensure_ascii=False, indent=2).encode("utf-8")
        blob = pack_state(data)
        stamp = state["updated_at"] or utc_stamp()
        users = len(state["users"])

        tmp = LOCAL_COPY.with_suffix(".tmp")
        tmp.write_bytes(blob)
        tmp.replace(LOCAL_COPY)

        try:
            msg = await bot.send_document(
                BACKUP_CHAT_ID,
                document=blob,
                filename=BACKUP_NAME,
                caption=f"🗂 نسخة احتياطية • {ar(users)} مستخدم • {stamp}",
                disable_notification=True,
            )
            await bot.pin_chat_message(
                BACKUP_CHAT_ID, msg.message_id, disable_notification=True
            )
        except TelegramError as e:
            # saved_revision متغيّرش، فالنسخة لسه متسخة وهيحاول تاني.
            log.error(
                "Backup failed: %s — make sure the bot is an admin in the group "
                "with the 'Pin messages' permission.",
                e,
            )
            return

        saved_revision = snap_rev
        old = backup_msg_id
        backup_msg_id = msg.message_id
        if old and old != msg.message_id:
            try:
                await bot.delete_message(BACKUP_CHAT_ID, old)
            except TelegramError as e:
                log.warning("Could not delete old backup %s: %s", old, e)
        log.info(
            "Backup pinned (message %s): %d KB json -> %d KB zip.",
            msg.message_id, len(data) // 1024, len(blob) // 1024,
        )


async def autosave_job(context: ContextTypes.DEFAULT_TYPE):
    await flush(context.bot)


# ───────────────────────── صفحات المصحف ─────────────────────────
_pdf = fitz.open(QURAN_PDF)


def today_pages(user: dict) -> list[int]:
    """أرقام صفحات ورد النهاردة (١..TOTAL_PAGES) وبترجع للأول لما الختمة تخلص."""
    start, n = user["current_page"], user["pages_per_day"]
    return [((start - 1 + i) % TOTAL_PAGES) + 1 for i in range(n)]


def render_page(page_no: int) -> Path:
    out = CACHE_DIR / f"{page_no}.jpg"
    if not out.exists():
        pix = _pdf[page_no - 1 + PDF_OFFSET].get_pixmap(matrix=fitz.Matrix(ZOOM, ZOOM))
        pix.save(str(out), jpg_quality=88)
    return out


async def send_pages(bot, chat_id: int, pages: list[int]):
    paths = await asyncio.to_thread(lambda: [render_page(p) for p in pages])
    # الألبوم في تليجرام بيشيل ١٠ صور بالكتير.
    for i in range(0, len(paths), 10):
        chunk = list(zip(pages[i : i + 10], paths[i : i + 10]))
        if len(chunk) == 1:
            p, path = chunk[0]
            with open(path, "rb") as f:
                await bot.send_photo(chat_id, f, caption=f"📖 صفحة {ar(p)}")
        else:
            media = [
                InputMediaPhoto(path.read_bytes(), caption=f"📖 صفحة {ar(p)}")
                for p, path in chunk
            ]
            await bot.send_media_group(chat_id, media)


# ───────────────────────── أدوات مساعدة ─────────────────────────
def user_now(user) -> datetime:
    return datetime.now(ZoneInfo(user["tz"]))


def is_admin(update: Update) -> bool:
    chat = update.effective_chat
    user = update.effective_user
    return bool(
        (chat and chat.id == BACKUP_CHAT_ID) or (user and user.id in ADMIN_IDS)
    )


def back_row(target: str) -> list:
    return [InlineKeyboardButton("⬅️ رجوع", callback_data=target)]


def done_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [[InlineKeyboardButton("✅ خلّصت وردي", callback_data="done")]]
    )


def main_menu() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [InlineKeyboardButton("📖 ورد النهاردة", callback_data="today")],
            [
                InlineKeyboardButton("📊 تقدّمي", callback_data="progress"),
                InlineKeyboardButton("⚙️ الإعدادات", callback_data="settings"),
            ],
        ]
    )


def settings_menu() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [
                InlineKeyboardButton("📄 عدد الصفحات", callback_data="set_pages"),
                InlineKeyboardButton("🎯 هدف الختمة", callback_data="set_goal"),
            ],
            [
                InlineKeyboardButton("⏰ ميعاد التذكير", callback_data="set_time"),
                InlineKeyboardButton("🌍 المدينة والمنطقة", callback_data="set_tz"),
            ],
            [InlineKeyboardButton("🕌 تنبيهات الصلاة", callback_data="set_prayer")],
            back_row("menu"),
        ]
    )


def settings_text(u: dict) -> str:
    goal = f"ختمة في {ar(u['goal_days'])} يوم" if u["goal_days"] else "مفيش هدف"
    remind = ar(u["remind_time"]) if u["reminders_on"] else "واقف"
    place = html.escape(u["city"] or tz_label(u["tz"]))
    prayer = "شغّالة ✅" if u["prayer_on"] else "واقفة ⏸"
    return (
        "⚙️ <b>الإعدادات</b>\n\n"
        f"📄 الورد: {ar(u['pages_per_day'])} صفحة في اليوم\n"
        f"🎯 الهدف: {goal}\n"
        f"⏰ التذكير: {remind}\n"
        f"🌍 المكان: {place}\n"
        f"🕌 تنبيهات الصلاة: {prayer}"
    )


# ───────────────────────── المدينة والمنطقة ─────────────────────────
TZ_TEXT = (
    "🌍 <b>المدينة والمنطقة</b>\n"
    "اختار مدينتك عشان أظبط ميعاد التذكير ومواعيد الصلاة 👇"
)


def tz_keyboard() -> InlineKeyboardMarkup:
    rows, row = [], []
    for i, city in enumerate(CITIES):
        row.append(InlineKeyboardButton(city[0], callback_data=f"city_{i}"))
        if len(row) == 3:
            rows.append(row)
            row = []
    if row:
        rows.append(row)
    rows.append(
        [InlineKeyboardButton(n, callback_data=f"zone_{i}") for i, (n, _) in enumerate(ZONES)]
    )
    rows.append(
        [
            InlineKeyboardButton("📍 ابعت موقعك", callback_data="loc_share"),
            InlineKeyboardButton("✏️ اكتب المنطقة", callback_data="tz_typed"),
        ]
    )
    rows.append(back_row("settings"))
    return InlineKeyboardMarkup(rows)


def haversine_km(lat1, lon1, lat2, lon2) -> float:
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dp, dl = p2 - p1, math.radians(lon2 - lon1)
    a = math.sin(dp / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * 6371 * math.asin(math.sqrt(a))


def nearest_city(lat: float, lon: float) -> tuple[int, float]:
    dists = [haversine_km(lat, lon, c[1], c[2]) for c in CITIES]
    i = min(range(len(dists)), key=dists.__getitem__)
    return i, dists[i]


# ───────────────────────── هدف الختمة ─────────────────────────
GOAL_TEXT = (
    "🎯 <b>هدف الختمة</b>\n"
    "اختار تخلّص المصحف في كام يوم، وأنا هظبطلك عدد الصفحات اللي تقراها كل يوم 👇"
)


def goal_keyboard(u: dict) -> InlineKeyboardMarkup:
    rows = [
        [InlineKeyboardButton(f"{ar(d)} يوم", callback_data=f"goal_{d}") for d in (15, 30, 60, 90)],
        [InlineKeyboardButton("✏️ عدد أيام تاني", callback_data="goal_custom")],
    ]
    if u["goal_days"]:
        rows.append([InlineKeyboardButton("🚫 إلغاء الهدف", callback_data="goal_off")])
    rows.append(back_row("settings"))
    return InlineKeyboardMarkup(rows)


def goal_ppd(u: dict) -> int:
    return -(-TOTAL_PAGES // u["goal_days"])


def apply_goal(chat_id: int, days: int) -> str:
    u = get_user(chat_id)
    ppd = -(-TOTAL_PAGES // days)
    now = user_now(u)
    today = now.strftime("%Y-%m-%d")
    start = today
    if u["last_done"] == today:  # خلّص ورد النهاردة قبل ما يحدد الهدف
        start = (now + timedelta(days=1)).strftime("%Y-%m-%d")
    update_user(chat_id, goal_days=days, goal_start=start, goal_read=0, pages_per_day=ppd)
    finish = -(-TOTAL_PAGES // ppd)
    text = (
        f"🎯 تمام! هتختم القرآن في {ar(days)} يوم بإذن الله\n"
        f"📄 وردك: {ar(ppd)} صفحة في اليوم\n"
        f"(هتخلّص فعلياً في حوالي {ar(finish)} يوم)"
    )
    if start != today:
        text += "\nالهدف هيبدأ من بكرة لأنك خلّصت ورد النهاردة."
    return text


def goal_status(u: dict) -> dict | None:
    """مقارنة تقدّمك بجدول الهدف (بالصفحات والأيام)."""
    if not u["goal_days"] or not u["goal_start"]:
        return None
    now = user_now(u)
    today = now.strftime("%Y-%m-%d")
    t = datetime.strptime(today, "%Y-%m-%d").date()
    s = datetime.strptime(u["goal_start"], "%Y-%m-%d").date()
    started = t >= s
    elapsed = max(0, (t - s).days)
    bonus = 1 if (started and u["last_done"] == today) else 0
    gp = goal_ppd(u)
    expected = min(TOTAL_PAGES, gp * (elapsed + bonus)) if started else 0
    diff_pages = u["goal_read"] - expected
    remaining = max(0, TOTAL_PAGES - u["goal_read"])
    remaining_days = u["goal_days"] - elapsed - bonus if started else u["goal_days"]
    needed = -(-remaining // remaining_days) if remaining_days > 0 else None
    return {
        "started": started,
        "goal_ppd": gp,
        "expected": expected,
        "diff_pages": diff_pages,
        "diff_days": diff_pages / gp,
        "remaining": remaining,
        "remaining_days": remaining_days,
        "needed": needed,
    }


def goal_lines(u: dict) -> list[str]:
    g = goal_status(u)
    if g is None:
        return []
    lines = [
        f"🎯 هدف الختمة: {ar(u['goal_days'])} يوم ({ar(g['goal_ppd'])} صفحة في اليوم)",
        f"أنجزت {ar(u['goal_read'])} من {ar(TOTAL_PAGES)} صفحة",
    ]
    if not g["started"]:
        lines.append("🕐 الهدف هيبدأ من بكرة")
    elif g["remaining_days"] <= 0 and g["remaining"] > 0:
        lines.append("⏰ ميعاد الهدف عدّى. تقدر تحدد هدف جديد من الإعدادات")
    elif abs(g["diff_days"]) < 0.5:
        lines.append("✅ ماشي على الجدول")
    elif g["diff_days"] > 0:
        lines.append(f"🚀 قدّام الجدول بحوالي {ar(max(1, round(g['diff_days'])))} يوم")
    else:
        lines.append(f"⚠️ ورا الجدول بحوالي {ar(max(1, round(-g['diff_days'])))} يوم")
        if g["needed"] and g["needed"] > u["pages_per_day"]:
            lines.append(f"عشان تلحق محتاج تقرا {ar(g['needed'])} صفحة في اليوم")
    return lines


# ───────────────────────── تذكيرات الورد ─────────────────────────
def reminder_passed_today(u: dict) -> bool:
    now = user_now(u)
    h, m = map(int, u["remind_time"].split(":"))
    return (now.hour, now.minute) >= (h, m)


def sync_catchup_marker(u: dict):
    """بعد تغيير الميعاد/المنطقة: لو ميعاد النهاردة عدّى بنعتبره "فات" عشان
    متجيش رسالة تعويض غلط بعد الريستارت، ولو لسه مجاش بنفضّي العلامة."""
    u["last_sent"] = user_now(u).strftime("%Y-%m-%d") if reminder_passed_today(u) else None
    mark_dirty()


def needs_catchup(u: dict) -> bool:
    """ميعاد وردك فات النهاردة ومبعتناش ولا خلّصت؟"""
    if not u["reminders_on"] or u["blocked"]:
        return False
    today = user_now(u).strftime("%Y-%m-%d")
    if u["last_done"] == today or u.get("last_sent") == today:
        return False
    return reminder_passed_today(u)


def schedule_reminder(app: Application, user: dict):
    name = f"remind_{user['chat_id']}"
    for job in app.job_queue.get_jobs_by_name(name):
        job.schedule_removal()
    if not user["reminders_on"] or user["blocked"]:
        return
    h, m = map(int, user["remind_time"].split(":"))
    app.job_queue.run_daily(
        reminder_job,
        time=time(h, m, tzinfo=ZoneInfo(user["tz"])),
        chat_id=user["chat_id"],
        name=name,
    )


async def reminder_job(context: ContextTypes.DEFAULT_TYPE):
    chat_id = context.job.chat_id
    if get_user(chat_id)["blocked"]:
        return
    outbox.put("wird", chat_id, mode="reminder")


async def catchup_job(context: ContextTypes.DEFAULT_TYPE):
    """بعد أي ريستارت: بيحط في الطابور ورد النهاردة لكل واحد معاده فات والبوت كان واقف."""
    due = [u["chat_id"] for u in list(state["users"].values()) if needs_catchup(u)]
    for chat_id in due:
        outbox.put("wird", chat_id, mode="late")
    if due:
        log.info("Catch-up: %d users missed today's reminder.", len(due))


async def deliver_today(
    bot, chat_id: int, user, reminder: bool = False, late: bool = False
):
    pages = today_pages(user)
    today = user_now(user).strftime("%Y-%m-%d")
    if user["last_done"] == today:
        await bot.send_message(
            chat_id, "✅ إنت خلّصت ورد النهاردة قبل كده، تقبّل الله منك 🤍"
        )
        return
    if late:
        head = "🔔 معاد وردك عدّى والبوت كان واقف شوية، ورد النهاردة أهو"
    elif reminder:
        head = "🔔 جه معاد وردك"
    else:
        head = "📖 ورد النهاردة"
    await bot.send_message(
        chat_id,
        f"{head}\nالصفحات من {ar(pages[0])} لـ {ar(pages[-1])} ({ar(len(pages))} صفحة)",
    )
    await send_pages(bot, chat_id, pages)
    update_user(chat_id, last_sent=today)
    await bot.send_message(
        chat_id, "لما تخلّص دوس على الزرار 👇", reply_markup=done_keyboard()
    )


# ───────────────────────── طابور الإرسال + المستخدمين الحاظرين ─────────────────────────
def is_gone(e: Exception) -> bool:
    """المستخدم عامل بلوك للبوت أو حسابه اتمسح."""
    return isinstance(e, Forbidden) or (
        isinstance(e, BadRequest) and "chat not found" in str(e).lower()
    )


def mark_blocked(chat_id: int):
    u = get_user(chat_id)
    if u["blocked"]:
        return
    update_user(chat_id, blocked=True)
    if APP is not None:
        schedule_reminder(APP, u)  # بيشيل التذكير المجدول
    log.info("User %s blocked the bot; reminders paused.", chat_id)


def unblock(app: Application, chat_id: int):
    u = state["users"].get(str(chat_id))
    if u and u["blocked"]:
        update_user(chat_id, blocked=False)
        schedule_reminder(app, u)
        log.info("User %s is back.", chat_id)


def on_send_failed(kind: str, chat_id: int, data: dict):
    """لو تعويض فشل، نعلّم إننا حاولنا النهاردة عشان منحاولش في كل ريستارت."""
    if kind == "wird" and data.get("mode") == "late":
        u = get_user(chat_id)
        update_user(chat_id, last_sent=user_now(u).strftime("%Y-%m-%d"))


async def dispatch(bot, kind: str, chat_id: int, data: dict):
    u = get_user(chat_id)
    if u["blocked"]:
        return
    if kind == "wird":
        mode = data.get("mode", "reminder")
        if mode == "late" and not needs_catchup(u):
            return  # اتغيّر حاجة وهو في الطابور
        await deliver_today(
            bot, chat_id, u, reminder=(mode == "reminder"), late=(mode == "late")
        )
    elif kind == "prayer":
        await send_prayer_warning(bot, chat_id, **data)


class Outbox:
    """طابور بيبعت للمستخدمين واحد واحد بفاصل SEND_GAP، بيحترم الـ flood-wait
    بتاع تليجرام، ومبيحطّش نفس المهمة مرتين."""

    def __init__(self):
        self.queue: asyncio.Queue = asyncio.Queue()
        self.pending: set = set()

    def put(self, kind: str, chat_id: int, **data) -> bool:
        key = (kind, chat_id, tuple(sorted(data.items())))
        if key in self.pending:
            return False
        self.pending.add(key)
        self.queue.put_nowait((key, kind, chat_id, data, 0))
        return True

    async def process(self, bot, item):
        key, kind, chat_id, data, attempt = item
        requeue = False
        try:
            await dispatch(bot, kind, chat_id, data)
        except RetryAfter as e:
            ra = e.retry_after
            wait = ra.total_seconds() if hasattr(ra, "total_seconds") else float(ra)
            await asyncio.sleep(wait + RETRY_PAD)
            if attempt + 1 < SEND_RETRIES:
                self.queue.put_nowait((key, kind, chat_id, data, attempt + 1))
                requeue = True
            else:
                log.warning("Giving up on %s for %s after flood waits.", kind, chat_id)
                on_send_failed(kind, chat_id, data)
        except TelegramError as e:
            if is_gone(e):
                mark_blocked(chat_id)
            else:
                log.warning("Send %s to %s failed: %s", kind, chat_id, e)
                on_send_failed(kind, chat_id, data)
        except Exception:
            log.exception("Outbox job %s for %s crashed", kind, chat_id)
        finally:
            if not requeue:
                self.pending.discard(key)

    async def run(self, bot):
        while True:
            item = await self.queue.get()
            await self.process(bot, item)
            await asyncio.sleep(SEND_GAP)

    async def drain(self, bot):
        """بيفضّي الطابور فوراً (للاختبارات)."""
        while not self.queue.empty():
            await self.process(bot, self.queue.get_nowait())


# ───────────────────────── تنبيهات الصلاة ─────────────────────────
prayer_sent: set = set()    # (chat_id, يوم, صلاة, مرحلة) اتبعتت
prayer_prayed: set = set()  # (chat_id, يوم, صلاة) المستخدم داس "لقد صليت"
DATE_RE = re.compile(r"^\d{4}-\d{2}-\d{2}$")


def prayer_due(u: dict, now: datetime) -> list:
    """التنبيهات المستحقة دلوقتي للمستخدم: [(صلاة, مرحلة, وقت الصلاة, تاريخها)]."""
    if not u["prayer_on"] or u["lat"] is None or u["blocked"]:
        return []
    n = next_prayer(u["lat"], u["lon"], u["tz"], now)
    if n is None:
        return []
    name, at, day = n
    cid = u["chat_id"]
    if not u["prayers"].get(name, True) or (cid, day, name) in prayer_prayed:
        return []
    mins = (at - now).total_seconds() / 60
    return [
        (name, stage, at, day)
        for stage in WARN_STAGES
        if stage - WARN_WINDOW < mins <= stage and (cid, day, name, stage) not in prayer_sent
    ]


async def prayer_tick(context: ContextTypes.DEFAULT_TYPE):
    now = now_utc()
    for u in list(state["users"].values()):
        for name, stage, at, day in prayer_due(u, now):
            prayer_sent.add((u["chat_id"], day, name, stage))
            outbox.put(
                "prayer", u["chat_id"],
                name=name, stage=stage, day=day, at=at.strftime("%H:%M"),
            )
    old = (now.date() - timedelta(days=2)).isoformat()  # نمسح الذاكرة القديمة
    for s in (prayer_sent, prayer_prayed):
        for k in [k for k in s if k[1] < old]:
            s.discard(k)


async def send_prayer_warning(bot, chat_id: int, name: str, stage: int, day: str, at: str):
    if (chat_id, day, name) in prayer_prayed:
        return
    h, m = map(int, at.split(":"))
    when = "ساعة" if stage == 60 else "نص ساعة"
    tail = "جهّز نفسك 🤍" if stage == 60 else "لو صلّيت دوس على الزرار 👇"
    kb = InlineKeyboardMarkup(
        [[InlineKeyboardButton("✅ لقد صليت", callback_data=f"prayed_{name}_{day}")]]
    )
    await bot.send_message(
        chat_id,
        f"🕌 فاضل {when} على صلاة {PRAYER_AR[name]} ({fmt12(h, m)})\n{tail}",
        reply_markup=kb,
    )


def prayer_text(u: dict) -> str:
    city = html.escape(u["city"]) if u["city"] else "مش محددة ⚠️"
    status = "شغّالة ✅" if u["prayer_on"] else "واقفة ⏸"
    text = (
        "🕌 <b>تنبيهات الصلاة</b>\n"
        "بنبّهك قبل كل صلاة بساعة وبنص ساعة. ولو دوست «لقد صليت» مش هنبّهك تاني "
        "لنفس الصلاة.\n\n"
        f"الحالة: {status}\n"
        f"المدينة: {city}"
    )
    if u["lat"] is not None:
        n = next_prayer(u["lat"], u["lon"], u["tz"], now_utc())
        if n:
            text += f"\nأقرب صلاة: {PRAYER_AR[n[0]]} الساعة {fmt12(n[1].hour, n[1].minute)}"
    text += "\n\n(المواعيد تقريبية، اتأكد منها من مصدر رسمي)"
    return text


def prayer_keyboard(u: dict) -> InlineKeyboardMarkup:
    def btn(p):
        mark = "✅" if u["prayers"].get(p, True) else "⬜"
        return InlineKeyboardButton(f"{mark} {PRAYER_AR[p]}", callback_data=f"pray_{p}")

    toggle = "⏸ إيقاف التنبيهات" if u["prayer_on"] else "✅ تشغيل التنبيهات"
    return InlineKeyboardMarkup(
        [
            [InlineKeyboardButton(toggle, callback_data="pray_toggle")],
            [btn(p) for p in PRAYERS[:3]],
            [btn(p) for p in PRAYERS[3:]],
            [InlineKeyboardButton("📍 اختار المدينة", callback_data="set_tz")],
            back_row("settings"),
        ]
    )


# ───────────────────────── الأوامر ─────────────────────────
WELCOME = (
    "السلام عليكم ورحمة الله 🌙\n"
    "أهلاً بيك في <b>ترتيل</b>\n\n"
    "أنا بظبطلك وردك اليومي من المصحف، وببعتلك صفحات النهاردة بس، "
    "وبفكّرك في الميعاد اللي تحدده.\n\n"
    "يلا نبدأ نظبط الإعدادات 👇"
)


async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = get_user(update.effective_chat.id)
    schedule_reminder(context.application, user)
    await update.message.reply_text(WELCOME, parse_mode="HTML", reply_markup=main_menu())
    await update.message.reply_text(
        settings_text(user), parse_mode="HTML", reply_markup=settings_menu()
    )


async def menu(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text("القائمة", reply_markup=main_menu())


async def settings_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    u = get_user(update.effective_chat.id)
    await update.message.reply_text(
        settings_text(u), parse_mode="HTML", reply_markup=settings_menu()
    )


async def goal_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    u = get_user(update.effective_chat.id)
    await update.message.reply_text(
        GOAL_TEXT, parse_mode="HTML", reply_markup=goal_keyboard(u)
    )


async def prayer_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    u = get_user(update.effective_chat.id)
    await update.message.reply_text(
        prayer_text(u), parse_mode="HTML", reply_markup=prayer_keyboard(u)
    )


async def today_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = get_user(update.effective_chat.id)
    await deliver_today(context.bot, update.effective_chat.id, user)


async def pages_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await ask_pages(context.bot, update.effective_chat.id)


async def time_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await ask_time(context.bot, update.effective_chat.id, context)


async def progress_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await show_progress(context.bot, update.effective_chat.id)


async def stop_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.effective_chat.id
    update_user(chat_id, reminders_on=False)
    schedule_reminder(context.application, get_user(chat_id))
    await update.message.reply_text("🔕 وقّفت التذكير. ابعت /time لو عايز تشغّله تاني.")


async def setpage_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.effective_chat.id
    arg = en_digits(context.args[0]) if context.args else ""
    if arg.isdigit() and 1 <= int(arg) <= TOTAL_PAGES:
        update_user(chat_id, current_page=int(arg))
        await update.message.reply_text(f"✅ وردك هيبدأ من صفحة {ar(arg)}")
    else:
        await update.message.reply_text(
            f"استخدم الأمر كده: /setpage 120   (من ١ لـ {ar(TOTAL_PAGES)})"
        )


async def timezone_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(
        TZ_TEXT, parse_mode="HTML", reply_markup=tz_keyboard()
    )


async def backup_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """بيعمل نسخة احتياطية فوراً (للأدمن بس)."""
    if not is_admin(update):
        return
    await flush(context.bot, force=True)


async def health_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """إحصائيات البوت (للأدمن بس)."""
    if not is_admin(update):
        await update.message.reply_text("الأمر ده للأدمن بس 🙂")
        return
    await update.message.reply_text(format_health(health_report()), parse_mode="HTML")


# ───────────────────────── خطوات الإعدادات ─────────────────────────
async def ask_pages(bot, chat_id: int):
    nums = [1, 2, 3, 4, 5, 10, 20]
    rows = [
        [InlineKeyboardButton(ar(n), callback_data=f"pages_{n}") for n in nums[:4]],
        [InlineKeyboardButton(ar(n), callback_data=f"pages_{n}") for n in nums[4:]],
        [InlineKeyboardButton("✏️ رقم تاني", callback_data="pages_custom")],
    ]
    await bot.send_message(
        chat_id,
        "عايز تقرا كام صفحة في اليوم؟\n(٢٠ صفحة في اليوم = ختمة في شهر تقريباً)",
        reply_markup=InlineKeyboardMarkup(rows),
    )


async def ask_time(bot, chat_id: int, context):
    context.user_data["awaiting"] = "time"
    await bot.send_message(
        chat_id,
        "ابعتلي ميعاد التذكير بنظام ٢٤ ساعة، زي: 05:30 أو 21:00\n"
        "ولو عايز توقّفه ابعت /stop",
    )


async def ask_tz(bot, chat_id: int, context):
    context.user_data["awaiting"] = "tz"
    await bot.send_message(
        chat_id,
        "ابعتلي المنطقة الزمنية بتاعتك، زي:\n"
        "Africa/Cairo\nAsia/Riyadh\nEurope/London\nAmerica/New_York",
    )


async def show_progress(bot, chat_id: int):
    u = get_user(chat_id)
    pages = today_pages(u)
    read = u["current_page"] - 1
    pct = read / TOTAL_PAGES * 100
    left = TOTAL_PAGES - read
    days = -(-left // u["pages_per_day"])
    bar = "█" * int(pct // 10) + "░" * (10 - int(pct // 10))
    reminder = ar(u["remind_time"]) if u["reminders_on"] else "واقف"
    lines = [
        "📊 <b>تقدّمك</b>",
        f"{bar} {num(pct)}٪",
        f"الصفحة الحالية: {ar(u['current_page'])} من {ar(TOTAL_PAGES)}",
        f"ورد النهاردة: من {ar(pages[0])} لـ {ar(pages[-1])}",
        f"🔥 أيام ورا بعض: {ar(u['streak'])}",
        f"📗 الختمات: {ar(u['khatmas'])}",
        f"⏳ فاضل على الختمة: حوالي {ar(days)} يوم",
        f"⏰ التذكير: {reminder} ({html.escape(tz_label(u['tz']))})",
    ]
    goal = goal_lines(u)
    if goal:
        lines += [""] + goal
    await bot.send_message(chat_id, "\n".join(lines), parse_mode="HTML")


async def edit_or_send(q, bot, text: str, markup=None):
    """بيعدّل الرسالة الحالية (عشان الشات ميتملاش)، ولو معرفش بيبعت رسالة جديدة."""
    try:
        await q.edit_message_text(text, reply_markup=markup, parse_mode="HTML")
    except BadRequest as e:
        if "not modified" in str(e).lower():
            return
        await bot.send_message(
            q.message.chat_id, text, reply_markup=markup, parse_mode="HTML"
        )


# ───────────────────────── الأزرار ─────────────────────────
async def on_button(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    chat_id = q.message.chat_id
    data = q.data
    bot = context.bot
    u = get_user(chat_id)

    if data == "today":
        await deliver_today(bot, chat_id, u)
    elif data == "menu":
        await edit_or_send(q, bot, "القائمة", main_menu())
    elif data == "settings":
        await edit_or_send(q, bot, settings_text(u), settings_menu())
    elif data == "progress":
        await show_progress(bot, chat_id)
    elif data == "set_pages":
        await ask_pages(bot, chat_id)
    elif data == "set_time":
        await ask_time(bot, chat_id, context)
    elif data == "set_tz":
        await edit_or_send(q, bot, TZ_TEXT, tz_keyboard())
    elif data == "set_goal":
        await edit_or_send(q, bot, GOAL_TEXT, goal_keyboard(u))
    elif data == "set_prayer":
        await edit_or_send(q, bot, prayer_text(u), prayer_keyboard(u))
    elif data == "tz_typed":
        await ask_tz(bot, chat_id, context)
    elif data == "loc_share":
        await bot.send_message(
            chat_id,
            "دوس على الزرار اللي تحت وابعتلي موقعك 📍\n(بنحفظه تقريبي، من غير عنوانك بالظبط)",
            reply_markup=ReplyKeyboardMarkup(
                [[KeyboardButton("📍 ابعت موقعي", request_location=True)]],
                resize_keyboard=True,
                one_time_keyboard=True,
            ),
        )
    elif data.startswith("city_") and data[5:].isdigit() and int(data[5:]) < len(CITIES):
        name, lat, lon, tz = CITIES[int(data[5:])]
        update_user(chat_id, tz=tz, city=name, lat=lat, lon=lon)
        sync_catchup_marker(u)
        schedule_reminder(context.application, u)
        await edit_or_send(
            q, bot, f"✅ اتحدد مكانك: {name}\n\n" + settings_text(u), settings_menu()
        )
    elif data.startswith("zone_") and data[5:].isdigit() and int(data[5:]) < len(ZONES):
        name, tz = ZONES[int(data[5:])]
        update_user(chat_id, tz=tz, city=None, lat=None, lon=None)
        sync_catchup_marker(u)
        schedule_reminder(context.application, u)
        note = (
            "\n⚠️ تنبيهات الصلاة محتاجة مدينة أو موقع."
            if u["prayer_on"]
            else ""
        )
        await edit_or_send(
            q, bot, f"✅ اتظبطت المنطقة: {name}{note}\n\n" + settings_text(u), settings_menu()
        )
    elif data == "pray_toggle":
        update_user(chat_id, prayer_on=not u["prayer_on"])
        if u["prayer_on"] and u["lat"] is None:
            await edit_or_send(
                q, bot,
                "🕌 اتفعّلت التنبيهات. اختار مدينتك الأول عشان أحسب مواعيد الصلاة 👇",
                tz_keyboard(),
            )
        else:
            await edit_or_send(q, bot, prayer_text(u), prayer_keyboard(u))
    elif data.startswith("pray_") and data[5:] in PRAYERS:
        u["prayers"][data[5:]] = not u["prayers"].get(data[5:], True)
        mark_dirty()
        await edit_or_send(q, bot, prayer_text(u), prayer_keyboard(u))
    elif data.startswith("prayed_"):
        parts = data.split("_", 2)
        if len(parts) == 3 and parts[1] in PRAYERS and DATE_RE.match(parts[2]):
            prayer_prayed.add((chat_id, parts[2], parts[1]))
            await edit_or_send(q, bot, f"✅ تقبّل الله صلاتك 🤍 ({PRAYER_AR[parts[1]]})")
    elif data == "goal_custom":
        context.user_data["awaiting"] = "goal"
        await bot.send_message(
            chat_id, f"ابعت عدد الأيام (من {ar(MIN_GOAL_DAYS)} لـ {ar(MAX_GOAL_DAYS)})"
        )
    elif data == "goal_off":
        update_user(chat_id, goal_days=None, goal_start=None, goal_read=0)
        await edit_or_send(q, bot, "🚫 اتلغى الهدف.\n\n" + settings_text(u), settings_menu())
    elif data.startswith("goal_") and data[5:].isdigit():
        days = int(data[5:])
        if MIN_GOAL_DAYS <= days <= MAX_GOAL_DAYS:
            text = apply_goal(chat_id, days)
            await edit_or_send(q, bot, text + "\n\n" + settings_text(u), settings_menu())
    elif data == "pages_custom":
        context.user_data["awaiting"] = "pages"
        await bot.send_message(chat_id, "ابعت رقم من ١ لـ ١٠٠")
    elif data.startswith("pages_") and data[6:].isdigit():
        n = int(data[6:])
        update_user(chat_id, pages_per_day=n)
        await q.edit_message_text(f"✅ وردك دلوقتي {ar(n)} صفحة في اليوم")
    elif data == "done":
        await mark_done(context, chat_id, q)


async def mark_done(context, chat_id: int, q):
    u = get_user(chat_id)
    now = user_now(u)
    today = now.strftime("%Y-%m-%d")
    if u["last_done"] == today:
        await q.edit_message_text("✅ وردك النهاردة اتسجّل قبل كده 🤍")
        return
    yesterday = (now - timedelta(days=1)).strftime("%Y-%m-%d")
    streak = u["streak"] + 1 if u["last_done"] == yesterday else 1
    done_pages = u["pages_per_day"]
    new_page = u["current_page"] + done_pages
    khatmas = u["khatmas"]
    msg = "🤍 تقبّل الله منك! ورد بكرة هيوصلك إن شاء الله."
    if new_page > TOTAL_PAGES:
        khatmas += 1
        new_page -= TOTAL_PAGES
        msg = "🎉 ما شاء الله! خلّصت ختمة كاملة، تقبّل الله منك وبارك فيك 🤲"

    goal_msg = ""
    if u["goal_days"] and u["goal_start"] and today >= u["goal_start"]:
        goal_read = u["goal_read"] + done_pages
        if goal_read >= TOTAL_PAGES:
            elapsed = (
                datetime.strptime(today, "%Y-%m-%d") - datetime.strptime(u["goal_start"], "%Y-%m-%d")
            ).days + 1
            goal_msg = f"\n🏆 حققت هدفك وخلّصت المصحف في {ar(elapsed)} يوم! تقبّل الله منك 🎉"
            update_user(chat_id, goal_days=None, goal_start=None, goal_read=0)
        else:
            update_user(chat_id, goal_read=goal_read)

    update_user(
        chat_id, current_page=new_page, last_done=today, streak=streak, khatmas=khatmas
    )
    record_done(chat_id, done_pages)
    await q.edit_message_text(f"{msg}\n🔥 {ar(streak)} يوم ورا بعض{goal_msg}")


# ───────────────────────── الرسايل النصية ─────────────────────────
async def on_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_chat.id == BACKUP_CHAT_ID:
        return  # ساكت في جروب النسخ الاحتياطي
    chat_id = update.effective_chat.id
    text = en_digits(update.message.text.strip())
    awaiting = context.user_data.get("awaiting")

    if awaiting == "time":
        m = re.fullmatch(r"([01]?\d|2[0-3])[:.]([0-5]\d)", text)
        if not m:
            await update.message.reply_text("الصيغة مش مظبوطة، جرّب كده: 05:30")
            return
        hhmm = f"{int(m.group(1)):02d}:{m.group(2)}"
        update_user(chat_id, remind_time=hhmm, reminders_on=True)
        u = get_user(chat_id)
        sync_catchup_marker(u)
        schedule_reminder(context.application, u)
        context.user_data.pop("awaiting")
        extra = (
            "\n(ميعاد النهاردة عدّى، فأول تذكير هيوصلك بكرة)"
            if reminder_passed_today(u)
            else ""
        )
        await update.message.reply_text(
            f"⏰ تمام، هفكّرك كل يوم الساعة {ar(hhmm)}{extra}"
        )
    elif awaiting == "pages":
        if not text.isdigit() or not 1 <= int(text) <= 100:
            await update.message.reply_text("ابعت رقم بين ١ و ١٠٠")
            return
        update_user(chat_id, pages_per_day=int(text))
        context.user_data.pop("awaiting")
        await update.message.reply_text(f"✅ وردك دلوقتي {ar(int(text))} صفحة في اليوم")
    elif awaiting == "goal":
        if not text.isdigit() or not MIN_GOAL_DAYS <= int(text) <= MAX_GOAL_DAYS:
            await update.message.reply_text(
                f"ابعت رقم بين {ar(MIN_GOAL_DAYS)} و {ar(MAX_GOAL_DAYS)}"
            )
            return
        context.user_data.pop("awaiting")
        await update.message.reply_text(apply_goal(chat_id, int(text)))
    elif awaiting == "tz":
        try:
            ZoneInfo(text)
        except Exception:
            await update.message.reply_text(
                "المنطقة دي مش معروفة، جرّب مثلاً: Africa/Cairo"
            )
            return
        update_user(chat_id, tz=text, city=None, lat=None, lon=None)
        u = get_user(chat_id)
        sync_catchup_marker(u)
        schedule_reminder(context.application, u)
        context.user_data.pop("awaiting")
        note = (
            "\n⚠️ تنبيهات الصلاة محتاجة مدينة أو موقع، اختارهم من الإعدادات."
            if u["prayer_on"]
            else ""
        )
        await update.message.reply_text(f"🌍 اتظبطت المنطقة الزمنية: {text}{note}")
    else:
        await update.message.reply_text("القائمة", reply_markup=main_menu())


async def on_location(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat = update.effective_chat
    if chat is None or chat.type != "private":
        return
    loc = update.message.location
    lat, lon = round(loc.latitude, 2), round(loc.longitude, 2)  # تقريب ~١ كم للخصوصية
    u = get_user(chat.id)
    i, dist = nearest_city(lat, lon)
    tz = CITIES[i][3] if dist <= NEAREST_CITY_KM else u["tz"]
    update_user(chat.id, lat=lat, lon=lon, city="موقعك", tz=tz)
    sync_catchup_marker(u)
    schedule_reminder(context.application, u)
    await update.message.reply_text(
        f"📍 اتحفظ موقعك. المنطقة الزمنية: {tz_label(tz)}\n"
        "لو مش مظبوطة غيّرها من الإعدادات.",
        reply_markup=ReplyKeyboardRemove(),
    )


async def track_activity(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """بيسجّل إن المستخدم نشط النهاردة (في الخاص بس)، وبيرجّع اللي كان حاظر البوت."""
    chat = update.effective_chat
    if chat is None or chat.type != "private":
        return
    # تحديثات حالة الشات (زي بلوك البوت) مش نشاط من المستخدم.
    if update.message is None and update.callback_query is None:
        return
    record_active(chat.id)
    unblock(context.application, chat.id)


async def on_my_chat_member(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """تليجرام بيبلّغنا فوراً لما مستخدم يعمل بلوك للبوت أو يفكّه."""
    cm = update.my_chat_member
    if cm is None or cm.chat.type != "private":
        return
    status = cm.new_chat_member.status
    if status == "kicked":
        mark_blocked(cm.chat.id)
    elif status == "member":
        unblock(context.application, cm.chat.id)


# ───────────────────────── تشغيل وإيقاف ─────────────────────────
async def post_init(app: Application):
    global save_lock, outbox, outbox_task, APP
    APP = app
    save_lock = asyncio.Lock()
    outbox = Outbox()
    await restore_state(app.bot)
    for u in state["users"].values():
        schedule_reminder(app, u)
    outbox_task = asyncio.create_task(outbox.run(app.bot))
    app.job_queue.run_repeating(autosave_job, interval=SAVE_INTERVAL, first=SAVE_INTERVAL)
    app.job_queue.run_repeating(prayer_tick, interval=60, first=15)
    await flush(app.bot)  # بيرفع النسخة الأولى أو النسخة المحلية الأحدث لو لزم
    app.job_queue.run_once(catchup_job, when=3)  # تعويض التذكيرات اللي فاتت
    log.info("Tarteel started with %d users.", len(state["users"]))


async def post_stop(app: Application):
    if outbox_task is not None:
        outbox_task.cancel()
        with suppress(asyncio.CancelledError):
            await outbox_task
    await flush(app.bot)  # آخر حفظ قبل ما البوت يقفل


def main():
    if BOT_TOKEN == "PASTE_YOUR_BOT_TOKEN_HERE":
        raise SystemExit("حط توكن البوت في BOT_TOKEN جوه bot.py (أو في ملف .env) الأول.")
    app = (
        Application.builder()
        .token(BOT_TOKEN)
        .post_init(post_init)
        .post_stop(post_stop)
        .build()
    )
    app.add_handler(TypeHandler(Update, track_activity), group=-1)
    app.add_handler(ChatMemberHandler(on_my_chat_member, ChatMemberHandler.MY_CHAT_MEMBER))
    app.add_handler(CommandHandler("start", start))
    app.add_handler(CommandHandler("menu", menu))
    app.add_handler(CommandHandler("settings", settings_cmd))
    app.add_handler(CommandHandler("goal", goal_cmd))
    app.add_handler(CommandHandler("prayer", prayer_cmd))
    app.add_handler(CommandHandler("today", today_cmd))
    app.add_handler(CommandHandler("pages", pages_cmd))
    app.add_handler(CommandHandler("time", time_cmd))
    app.add_handler(CommandHandler("progress", progress_cmd))
    app.add_handler(CommandHandler("setpage", setpage_cmd))
    app.add_handler(CommandHandler("timezone", timezone_cmd))
    app.add_handler(CommandHandler("stop", stop_cmd))
    app.add_handler(CommandHandler("backup", backup_cmd))
    app.add_handler(CommandHandler("health", health_cmd))
    app.add_handler(CallbackQueryHandler(on_button))
    app.add_handler(MessageHandler(filters.LOCATION, on_location))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, on_text))
    app.run_polling()


if __name__ == "__main__":
    main()
