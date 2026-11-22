#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
VintedDealBot v2 — surveille les nouvelles annonces Vinted et alerte sur les bonnes affaires.
"""

from __future__ import annotations

import argparse
import html as htmllib
import json
import logging
import os
import random
import re
import shlex
import signal
import sqlite3
import statistics
import threading
import time
import unicodedata
from dataclasses import dataclass, field, asdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any
from urllib.parse import parse_qs, urlparse

import requests

try:
    from curl_cffi import requests as cffi_requests
    HAS_CFFI = True
except Exception:
    cffi_requests = None
    HAS_CFFI = False

try:
    import yaml
    HAS_YAML = True
except Exception:
    HAS_YAML = False

log = logging.getLogger("vintedbot")

CONDITIONS: dict[str, tuple[int, str]] = {
    "neuf_avec_etiquette": (6, "Neuf avec étiquette"),
    "neuf_sans_etiquette": (1, "Neuf sans étiquette"),
    "tres_bon_etat":       (2, "Très bon état"),
    "bon_etat":            (3, "Bon état"),
    "satisfaisant":        (4, "Satisfaisant"),
}

LOCALES = {
    "fr": "fr-FR", "de": "de-DE", "it": "it-IT", "es": "es-ES", "be": "nl-BE",
    "at": "de-AT", "pl": "pl-PL", "pt": "pt-PT", "nl": "nl-NL", "lt": "lt-LT",
    "cz": "cs-CZ", "sk": "sk-SK", "hu": "hu-HU", "ro": "ro-RO", "se": "sv-SE",
    "dk": "da-DK", "fi": "fi-FI", "ie": "en-IE", "lu": "fr-LU", "gr": "el-GR",
    "hr": "hr-HR", "si": "sl-SI", "ee": "et-EE", "lv": "lv-LV",
    "co.uk": "en-GB", "com": "en-US",
}

IMPERSONATE_CANDIDATES = ("chrome", "chrome131", "chrome124", "chrome120")

UA_FALLBACK = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36"
)

BROWSER_HEADERS = {
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8",
    "Accept-Language": "fr-FR,fr;q=0.9,en;q=0.8",
    "Upgrade-Insecure-Requests": "1",
}

STATUS_BONUS = {
    "neuf_avec_etiquette": 12,
    "neuf_sans_etiquette": 10,
    "tres_bon_etat": 8,
    "bon_etat": 4,
    "satisfaisant": 0,
}

DETAIL_JSON_KEYS = (
    "description", "feedback_reputation", "feedback_count", "positive_feedback_count",
    "city", "country_title", "view_count",
)

HELP = """Commandes disponibles :
  list / show / add / rm / pause / resume / scan / seed / ref / help / quit"""


class VintedError(RuntimeError):
    pass


def norm(text: Any) -> str:
    s = unicodedata.normalize("NFKD", str(text or ""))
    s = "".join(c for c in s if not unicodedata.combining(c))
    return re.sub(r"[^a-z0-9]+", " ", s.lower()).strip()


_CONDITION_BY_LABEL = {norm(label): key for key, (_, label) in CONDITIONS.items()}


def condition_key(label: str) -> str | None:
    return _CONDITION_BY_LABEL.get(norm(label))


def make_http_session(proxy: str | None):
    proxies = {"http": proxy, "https": proxy} if proxy else None
    if HAS_CFFI:
        for imp in IMPERSONATE_CANDIDATES:
            try:
                return cffi_requests.Session(impersonate=imp, proxies=proxies)
            except Exception:
                continue
        log.warning("curl_cffi indisponible pour l'impersonation, repli sur requests")
    s = requests.Session()
    s.headers["User-Agent"] = UA_FALLBACK
    if proxy:
        s.proxies.update(proxies)
    return s


def item_age_minutes(iso: Any) -> float | None:
    if not iso:
        return None
    try:
        dt = datetime.fromisoformat(str(iso).replace("Z", "+00:00"))
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return (datetime.now(timezone.utc) - dt).total_seconds() / 60.0
    except Exception:
        return None


def filters_from_url(url: str) -> dict[str, Any]:
    query = urlparse(url).query
    if not query:
        return {}
    out: dict[str, Any] = {}
    for key, values in parse_qs(query, keep_blank_values=True).items():
        if key in ("page", "per_page", "time"):
            continue
        out[key] = values if (key.endswith("[]") or len(values) > 1) else values[0]
    return out


def parse_meta_tags(html_text: str) -> dict[str, str]:
    out: dict[str, str] = {}
    for tag in re.findall(r"<meta\b[^>]*>", html_text, re.I):
        prop = re.search(r'(?:property|name)=["\']([^"\']+)["\']', tag, re.I)
        cont = re.search(r'content=["\']([^"\']*)["\']', tag, re.I)
        if prop and cont:
            out[prop.group(1).lower()] = htmllib.unescape(cont.group(1))
    return out


def grab_json_value(html_text: str, key: str) -> Any:
    m = re.search(
        r'"%s"\s*:\s*("(?:[^"\\]|\\.)*"|-?\d+(?:\.\d+)?|true|false|null)' % re.escape(key),
        html_text,
    )
    if not m:
        return None
    raw = m.group(1)
    try:
        return json.loads(raw)
    except Exception:
        return raw.strip('"')


def normalize_rating(value: Any) -> float | None:
    if value is None:
        return None
    try:
        x = float(str(value).replace(",", "."))
    except (TypeError, ValueError):
        return None
    if 0.0 < x <= 1.0:
        return round(x * 5, 2)
    if x <= 5.0:
        return round(x, 2)
    if x <= 100.0:
        return round(x / 20, 2)
    return None


def parse_item(raw: dict, domain: str) -> dict:
    def price(key: str) -> float | None:
        v = raw.get(key)
        if isinstance(v, dict):
            v = v.get("amount")
        try:
            return float(str(v).replace(",", ".").replace(" ", ""))
        except (TypeError, ValueError):
            return None

    brand = raw.get("brand_title")
    if not brand:
        b = raw.get("brand")
        brand = b.get("title") if isinstance(b, dict) else b

    size = raw.get("size_title")
    if not size:
        s = raw.get("size")
        size = s if isinstance(s, str) else (s or {}).get("title")

    photo = raw.get("photo") or {}
    photo_url = photo.get("url") if isinstance(photo, dict) else None

    user = raw.get("user") or {}
    iid = str(raw.get("id") or "")
    url = raw.get("url") or f"https://{domain}/items/{iid}"
    if url.startswith("/"):
        url = f"https://{domain}{url}"

    p = raw.get("price")
    return {
        "id": iid,
        "title": (raw.get("title") or "").strip(),
        "price": price("price"),
        "total_price": price("total_item_price"),
        "currency": p.get("currency_code") if isinstance(p, dict) else None,
        "status": raw.get("status") or "",
        "brand": brand or "",
        "size": size or "",
        "url": url,
        "photo": photo_url,
        "favourites": raw.get("favourite_count") or 0,
        "seller": user.get("login") if isinstance(user, dict) else "",
        "created_at": raw.get("created_at_ts") or raw.get("updated_at_ts"),
    }


def compute_score(price: float, ref: float | None, cond: str | None,
                  age_min: float | None, detail: dict | None = None) -> int:
    score = 0.0
    if ref and ref > 0:
        score += max(0.0, min(70.0, (1.0 - price / ref) * 100.0 * 1.4))
    score += STATUS_BONUS.get(cond or "", 0)
    if age_min is not None:
        if age_min <= 15:
            score += 15
        elif age_min <= 60:
            score += 8
        elif age_min <= 360:
            score += 3
    if detail:
        rating = detail.get("rating")
        if rating is not None:
            score += max(-6.0, min(6.0, (rating - 4.0) * 4.0))
        if (detail.get("reviews") or 0) >= 10:
            score += 2
    return int(min(100, max(0, round(score))))


@dataclass
class Watch:
    name: str
    search_text: str = ""
    url: str | None = None
    max_price: float = 100000.0
    min_price: float = 0.0
    reference_price: float | None = None
    deal_ratio: float = 0.70
    conditions: list[str] = field(default_factory=lambda: [
        "neuf_avec_etiquette", "neuf_sans_etiquette", "tres_bon_etat", "bon_etat"
    ])
    include_keywords: list[str] = field(default_factory=list)
    exclude_keywords: list[str] = field(default_factory=list)
    min_score: int = 0
    interval: int = 180
    pages: int = 1
    max_age_hours: int = 24
    currency: str = "EUR"
    order: str = "newest_first"
    seed_on_start: bool = True

    verify_detail: bool = True
    detail_strict: bool = False
    detail_ttl_hours: int = 6
    max_detail_checks: int = 10
    exclude_description_keywords: list[str] = field(default_factory=list)
    include_description_keywords: list[str] = field(default_factory=list)
    min_description_chars: int = 0
    min_seller_rating: float | None = None
    min_seller_reviews: int = 0
    skip_reserved: bool = True

    extra_params: dict[str, Any] = field(default_factory=dict)

    @classmethod
    def from_dict(cls, d: dict) -> "Watch":
        known = set(cls.__dataclass_fields__)
        unknown = set(d) - known
        if unknown:
            log.warning("Watch '%s' : clés inconnues ignorées %s", d.get("name"), sorted(unknown))
        kwargs = {k: v for k, v in d.items() if k in known}
        kwargs.setdefault("name", str(d.get("search_text") or d.get("url") or "watch"))
        for k in ("max_price", "min_price", "deal_ratio", "reference_price", "min_seller_rating"):
            if kwargs.get(k) not in (None, ""):
                kwargs[k] = float(kwargs[k])
        for k in ("interval", "pages", "max_age_hours", "min_score", "min_description_chars",
                  "min_seller_reviews", "max_detail_checks", "detail_ttl_hours"):
            if kwargs.get(k) not in (None, ""):
                kwargs[k] = int(kwargs[k])
        w = cls(**kwargs)
        bad = [c for c in w.conditions if c not in CONDITIONS]
        if bad:
            raise ValueError(f"Watch '{w.name}' : états inconnus {bad}. Valides : {list(CONDITIONS)}")
        return w


@dataclass
class NotifySettings:
    telegram_bot_token: str = ""
    telegram_chat_id: str = ""
    discord_webhook: str = ""
    webhook_url: str = ""


@dataclass
class Settings:
    domain: str = "www.vinted.fr"
    proxy: str | None = None
    request_delay: float = 6.0
    jitter: float = 3.0
    per_page: int = 96
    cookie_ttl: int = 5400
    detail_max_bytes: int = 600_000
    db_path: str = "vinted_bot.sqlite3"
    state_dir: str = ".state"
    extra_watches_file: str | None = None
    log_level: str = "INFO"
    notify: NotifySettings = field(default_factory=NotifySettings)
    watches: list[Watch] = field(default_factory=list)


def local_watches_path(main_config: str, override: str | None = None) -> Path:
    if override:
        return Path(override)
    return Path(main_config).with_name("watches.local.yaml")


def load_settings(path: str) -> Settings:
    p = Path(path)
    if not p.exists():
        raise SystemExit(f"Config introuvable : {p}")
    text = p.read_text(encoding="utf-8")
    if p.suffix.lower() == ".json":
        data = json.loads(text)
    else:
        if not HAS_YAML:
            raise SystemExit("PyYAML manquant : pip install pyyaml")
        data = yaml.safe_load(text) or {}

    notify = NotifySettings(**(data.pop("notify", {}) or {}))
    watches_raw = data.pop("watches", []) or []
    known = set(Settings.__dataclass_fields__)
    s = Settings(**{k: v for k, v in data.items() if k in known})
    s.notify = notify

    local_path = local_watches_path(path, s.extra_watches_file)
    local: dict = {}
    if local_path.exists() and HAS_YAML:
        try:
            local = yaml.safe_load(local_path.read_text(encoding="utf-8")) or {}
        except Exception as e:
            log.error("watches.local.yaml illisible (%s), ignoré", e)

    watches = [Watch.from_dict(w) for w in watches_raw]
    watches += [Watch.from_dict(w) for w in (local.get("watches") or [])]

    overrides = local.get("overrides") or {}
    for w in watches:
        for k, v in (overrides.get(w.name) or {}).items():
            if k in Watch.__dataclass_fields__ and k != "name":
                setattr(w, k, v) if isinstance(getattr(w, k), type(v)) else setattr(
                    w, k, float(v) if isinstance(getattr(w, k), float) else v)

    disabled = {norm(x) for x in (local.get("disabled") or [])}
    watches = [w for w in watches if norm(w.name) not in disabled]

    seen_names: dict[str, Watch] = {}
    for w in watches:
        if norm(w.name) in seen_names:
            log.warning("Recherche en double '%s' — la dernière définition gagne", w.name)
        seen_names[norm(w.name)] = w
    s.watches = list(seen_names.values())

    if not s.watches:
        log.warning("Aucune recherche active (utilisez --interactive pour en ajouter).")
    return s


class VintedAPI:
    def __init__(self, settings: Settings):
        self.s = settings
        self.domain = settings.domain
        tld = self.domain.split("vinted.", 1)[1] if "vinted." in self.domain else "fr"
        self.tld = tld
        self.base_domain = f"vinted.{tld}"
        self.api_host = f"api.{self.base_domain}"
        self.locale = LOCALES.get(tld, "fr-FR")
        self.session = None
        self.anon_id: str | None = None
        self.cookie_path = Path(settings.state_dir) / "cookies.json"
        self.preferred_endpoint: str | None = None
        self._last_request = 0.0
        self._req_lock = threading.Lock()

    def _endpoints(self):
        cands = [
            (f"https://{self.api_host}/svc-catalogue/items", "api"),
            (f"https://{self.domain}/api/v2/catalog/items", "www"),
            (f"https://{self.domain}/web/api/core/catalog/items", "www"),
        ]
        if self.preferred_endpoint:
            cands.sort(key=lambda c: c[0] != self.preferred_endpoint)
        return cands

    def api_headers(self) -> dict[str, str]:
        h = {
            "Accept": "application/json, text/plain, */*",
            "Accept-Language": f"{self.locale},en;q=0.8",
            "Locale": self.locale,
            "Referer": f"https://{self.domain}/catalog",
            "X-Requested-With": "XMLHttpRequest",
        }
        if self.anon_id:
            h["X-Anon-Id"] = self.anon_id
        return h

    def _throttle(self):
        delay = max(0.0, self.s.request_delay)
        elapsed = time.time() - self._last_request
        if elapsed < delay:
            time.sleep(delay - elapsed + random.uniform(0, max(0.0, self.s.jitter)))
        self._last_request = time.time()

    def ensure_session(self, force: bool = False) -> None:
        if self.session is not None and not force and self.session.cookies.get_dict():
            return
        if not force and self._load_cookies():
            return
        for attempt in (1, 2):
            if self._bootstrap_http():
                return
            time.sleep(3 * attempt)
        if self._bootstrap_browser():
            return
        raise VintedError(
            "Impossible d'obtenir une session Vinted (DataDome ?). "
            "IP résidentielle recommandée, ou installer playwright pour le repli navigateur."
        )

    def _bootstrap_http(self) -> bool:
        s = make_http_session(self.s.proxy)
        try:
            r = s.get(f"https://{self.domain}/", headers=BROWSER_HEADERS,
                      timeout=30, allow_redirects=True)
        except Exception as e:
            log.warning("Bootstrap HTTP échoué : %s", e)
            return False
        cookies = s.cookies.get_dict()
        has_session = "access_token_web" in cookies or any(k.endswith("_session") for k in cookies)
        if r.status_code != 200 or not has_session:
            log.warning("Bootstrap HTTP : status=%s cookies=%s", r.status_code, list(cookies))
            return False
        self.session = s
        self.anon_id = r.headers.get("x-anon-id") or cookies.get("anon_id")
        log.info("Session obtenue (HTTP) — %d cookies, anon_id=%s", len(cookies),
                 "oui" if self.anon_id else "non")
        self._save_cookies()
        return True

    def _bootstrap_browser(self) -> bool:
        try:
            from playwright.sync_api import sync_playwright
        except Exception:
            log.debug("playwright non installé, repli navigateur indisponible")
            return False
        proxy = None
        if self.s.proxy:
            u = urlparse(self.s.proxy if "://" in self.s.proxy else f"http://{self.s.proxy}")
            proxy = {"server": f"{u.scheme}://{u.hostname}:{u.port}"}
            if u.username:
                proxy["username"] = u.username
                proxy["password"] = u.password or ""
        try:
            with sync_playwright() as pw:
                browser = pw.chromium.launch(headless=True, proxy=proxy)
                ctx = browser.new_context(locale=self.locale, timezone_id="Europe/Paris")
                page = ctx.new_page()
                page.goto(f"https://{self.domain}/", wait_until="domcontentloaded", timeout=45000)
                page.wait_for_timeout(3000)
                try:
                    page.mouse.move(140, 260)
                    page.wait_for_timeout(400)
                except Exception:
                    pass
                cookies = {c["name"]: c["value"] for c in ctx.cookies()}
                anon = None
                try:
                    anon = page.evaluate(
                        "() => { const k = Object.keys(localStorage)"
                        ".find(k => k.toLowerCase().includes('anon'));"
                        " return k ? localStorage.getItem(k) : null; }")
                except Exception:
                    pass
                browser.close()
        except Exception as e:
            log.warning("Bootstrap navigateur échoué : %s", e)
            return False
        if not cookies:
            return False
        s = make_http_session(self.s.proxy)
        for k, v in cookies.items():
            try:
                s.cookies.set(k, v, domain=f".{self.base_domain}", path="/")
            except TypeError:
                s.cookies.set(k, v)
            except Exception:
                pass
        self.session = s
        self.anon_id = anon or cookies.get("anon_id")
        log.info("Session obtenue (navigateur) — %d cookies", len(cookies))
        self._save_cookies()
        return True

    def _save_cookies(self):
        try:
            self.cookie_path.parent.mkdir(parents=True, exist_ok=True)
            self.cookie_path.write_text(json.dumps({
                "ts": time.time(), "anon_id": self.anon_id,
                "cookies": self.session.cookies.get_dict(),
            }), encoding="utf-8")
            os.chmod(self.cookie_path, 0o600)
        except Exception as e:
            log.debug("Sauvegarde cookies : %s", e)

    def _load_cookies(self) -> bool:
        if not self.cookie_path.exists():
            return False
        try:
            data = json.loads(self.cookie_path.read_text(encoding="utf-8"))
        except Exception:
            return False
        if time.time() - float(data.get("ts", 0)) > self.s.cookie_ttl:
            log.info("Cookies persistés expirés → renouvellement")
            return False
        cookies = data.get("cookies") or {}
        if not cookies:
            return False
        s = make_http_session(self.s.proxy)
        for k, v in cookies.items():
            try:
                s.cookies.set(k, v, domain=f".{self.base_domain}", path="/")
            except TypeError:
                s.cookies.set(k, v)
            except Exception:
                pass
        self.session = s
        self.anon_id = data.get("anon_id")
        return True

    def search(self, params: dict, retries: int = 3) -> dict:
        with self._req_lock:
            self.ensure_session()
            last_err: Exception | None = None
            for attempt in range(1, retries + 1):
                need_refresh = False
                for url, _kind in self._endpoints():
                    self._throttle()
                    try:
                        r = self.session.get(url, params=params,
                                             headers=self.api_headers(), timeout=30)
                    except Exception as e:
                        last_err = e
                        continue
                    if r.status_code == 200:
                        try:
                            data = r.json()
                        except ValueError:
                            last_err = VintedError(f"Réponse non JSON depuis {url}")
                            continue
                        if self.preferred_endpoint != url:
                            log.info("Endpoint catalogue retenu : %s", url)
                            self.preferred_endpoint = url
                        return data
                    if r.status_code in (401, 403):
                        last_err = VintedError(f"HTTP {r.status_code} ({url})")
                        need_refresh = True
                        break
                    if r.status_code == 429:
                        wait = 30 * attempt + random.uniform(0, 10)
                        log.warning("429 rate limit — pause %.0fs", wait)
                        time.sleep(wait)
                        last_err = VintedError("HTTP 429")
                        break
                    last_err = VintedError(f"HTTP {r.status_code} ({url})")
                if need_refresh:
                    self.ensure_session(force=True)
                elif attempt < retries:
                    time.sleep(5 * attempt + random.uniform(0, 5))
            raise last_err or VintedError("Recherche impossible")

    def _get_html(self, url: str, max_bytes: int) -> str | None:
        headers = dict(BROWSER_HEADERS)
        headers["Referer"] = f"https://{self.domain}/catalog"
        r = self.session.get(url, headers=headers, timeout=30, stream=True)
        try:
            if r.status_code in (401, 403):
                return None
            if r.status_code != 200:
                log.debug("Fiche %s : HTTP %s", url, r.status_code)
                return None
            chunks: list[bytes] = []
            size = 0
            for chunk in r.iter_content(chunk_size=65536):
                if not chunk:
                    continue
                chunks.append(chunk)
                size += len(chunk)
                if size >= max_bytes:
                    break
            raw = b"".join(chunks)
            enc = getattr(r, "encoding", None) or "utf-8"
        finally:
            try:
                r.close()
            except Exception:
                pass
        try:
            return raw.decode(enc, errors="ignore")
        except Exception:
            return raw.decode("utf-8", errors="ignore")

    @staticmethod
    def _parse_detail(html_text: str) -> dict:
        meta = parse_meta_tags(html_text)
        desc = grab_json_value(html_text, "description")
        desc_known = desc is not None
        if isinstance(desc, str) and "\\n" in desc:
            try:
                desc = json.loads(f'"{desc}"')
            except Exception:
                desc = desc.replace("\\n", "\n")
        if not desc:
            og = meta.get("og:description") or ""
            desc = og
            desc_known = desc_known or bool(og)
        reviews = grab_json_value(html_text, "feedback_count")
        return {
            "description": (desc or "").strip()[:4000],
            "desc_known": bool(desc_known),
            "rating": normalize_rating(grab_json_value(html_text, "feedback_reputation")),
            "reviews": int(reviews) if isinstance(reviews, (int, float)) else None,
            "city": grab_json_value(html_text, "city"),
            "photo": meta.get("og:image"),
            "title": meta.get("og:title"),
            "reserved": bool(re.search(r'"is_reserved"\s*:\s*true', html_text)),
            "closed": bool(re.search(r'"is_closed"\s*:\s*true', html_text)),
        }

    def fetch_item_detail(self, url: str) -> dict | None:
        with self._req_lock:
            for attempt in (1, 2):
                self._throttle()
                try:
                    body = self._get_html(url, self.s.detail_max_bytes)
                except Exception as e:
                    log.warning("Fiche %s : %s", url, e)
                    return None
                if body is None:
                    self.ensure_session(force=True)
                    continue
                return self._parse_detail(body)
        return None


class Database:
    def __init__(self, path: str):
        self._lock = threading.Lock()
        self.conn = sqlite3.connect(path, check_same_thread=False)
        self.conn.execute("PRAGMA journal_mode=WAL")
        with self._lock:
            c = self.conn
            c.execute("""CREATE TABLE IF NOT EXISTS seen(
                watch TEXT NOT NULL, item_id TEXT NOT NULL,
                first_seen TEXT NOT NULL, price REAL, url TEXT,
                PRIMARY KEY(watch, item_id))""")
            c.execute("""CREATE TABLE IF NOT EXISTS price_obs(
                id INTEGER PRIMARY KEY AUTOINCREMENT, watch TEXT, ts TEXT, price REAL)""")
            c.execute("""CREATE TABLE IF NOT EXISTS details(
                item_id TEXT PRIMARY KEY, ts TEXT, rating REAL, reviews INTEGER, data TEXT)""")
            c.execute("""CREATE TABLE IF NOT EXISTS state(key TEXT PRIMARY KEY, value TEXT)""")
            c.execute("CREATE INDEX IF NOT EXISTS idx_price_obs ON price_obs(watch, ts)")
            c.commit()

    def seen_ids(self, watch: str, ids: list[str]) -> set[str]:
        if not ids:
            return set()
        q = f"SELECT item_id FROM seen WHERE watch=? AND item_id IN ({','.join('?' * len(ids))})"
        with self._lock:
            rows = self.conn.execute(q, [watch, *ids]).fetchall()
        return {r[0] for r in rows}

    def mark_seen(self, watch: str, items: list[dict]):
        now = datetime.now(timezone.utc).isoformat(timespec="seconds")
        with self._lock:
            self.conn.executemany(
                "INSERT OR IGNORE INTO seen(watch,item_id,first_seen,price,url) VALUES(?,?,?,?,?)",
                [(watch, i["id"], now, i["price"], i["url"]) for i in items if i.get("id")])
            self.conn.commit()

    def add_prices(self, watch: str, prices: list[float]):
        now = datetime.now(timezone.utc).isoformat(timespec="seconds")
        with self._lock:
            self.conn.executemany(
                "INSERT INTO price_obs(watch,ts,price) VALUES(?,?,?)",
                [(watch, now, p) for p in prices if p is not None])
            self.conn.commit()

    def prices(self, watch: str, days: int = 14) -> list[float]:
        with self._lock:
            rows = self.conn.execute(
                "SELECT price FROM price_obs WHERE watch=? AND ts >= datetime('now', ?)",
                (watch, f"-{days} days")).fetchall()
        return [r[0] for r in rows if r[0] is not None]

    def get_detail(self, item_id: str, max_age_h: float = 6) -> dict | None:
        with self._lock:
            row = self.conn.execute("SELECT ts,data FROM details WHERE item_id=?",
                                    (item_id,)).fetchone()
        if not row:
            return None
        try:
            age_h = (datetime.now(timezone.utc)
                     - datetime.fromisoformat(row[0])).total_seconds() / 3600
        except Exception:
            return None
        if age_h > max_age_h:
            return None
        try:
            return json.loads(row[1])
        except Exception:
            return None

    def save_detail(self, item_id: str, d: dict):
        now = datetime.now(timezone.utc).isoformat(timespec="seconds")
        with self._lock:
            self.conn.execute(
                "INSERT OR REPLACE INTO details(item_id,ts,rating,reviews,data) VALUES(?,?,?,?,?)",
                (item_id, now, d.get("rating"), d.get("reviews"),
                 json.dumps(d, ensure_ascii=False)))
            self.conn.commit()

    def get_state(self, key: str) -> str | None:
        with self._lock:
            row = self.conn.execute("SELECT value FROM state WHERE key=?", (key,)).fetchone()
        return row[0] if row else None

    def set_state(self, key: str, value: str):
        with self._lock:
            self.conn.execute(
                "INSERT INTO state(key,value) VALUES(?,?) "
                "ON CONFLICT(key) DO UPDATE SET value=excluded.value", (key, value))
            self.conn.commit()


class Notifier:
    def __init__(self, cfg: NotifySettings, dry_run: bool = False):
        self.cfg = cfg
        self.dry = dry_run

    @staticmethod
    def format_text(watch: Watch, item: dict, score: int, ref: float | None,
                    ref_src: str, age: float | None, detail: dict | None = None):
        detail = detail or {}
        price = item["price"] or 0.0
        cur = item["currency"] or "EUR"
        sym = {"EUR": "€", "GBP": "£", "USD": "$", "PLN": "zł"}.get(cur, cur)
        disc = f" (−{(1 - price / ref) * 100:.0f} % vs {ref:.2f} {sym})" if ref else ""
        age_txt = ""
        if age is not None:
            age_txt = f"{age:.0f} min" if age < 120 else f"{age / 60:.1f} h"
        meta = " · ".join(x for x in [
            item["status"] or None,
            f"Taille {item['size']}" if item["size"] else None,
            item["brand"] or None,
        ] if x)
        seller_bits = []
        if item["seller"]:
            seller_bits.append(item["seller"])
        if detail.get("rating") is not None:
            seller_bits.append(f"{detail['rating']}/5 ★")
        if detail.get("reviews"):
            seller_bits.append(f"{detail['reviews']} avis")
        if detail.get("city"):
            seller_bits.append(str(detail["city"]))
        extra = " · ".join(x for x in [
            " · ".join(seller_bits) or None,
            f"{item['favourites']} favoris" if item["favourites"] else None,
            f"publiée il y a {age_txt}" if age_txt else None,
        ] if x)
        flags = " · ".join(x for x in [
            "⚠️ RÉSERVÉE" if detail.get("reserved") else None,
            "⚠️ déjà vendue ?" if detail.get("closed") else None,
        ] if x)
        desc = (detail.get("description") or "").replace("\n", " ").strip()
        desc_short = (desc[:180] + "…") if len(desc) > 180 else desc

        plain_lines = [
            f"🔥 Bonne affaire — score {score}/100",
            item["title"],
            f"{price:.2f} {sym}{disc}",
            meta,
            extra,
        ]
        if flags:
            plain_lines.append(flags)
        if desc_short:
            plain_lines.append(f"« {desc_short} »")
        plain_lines += [f"[{watch.name}] référence : {ref_src}", item["url"]]

        html_lines = [
            f"🔥 <b>Bonne affaire</b> — score <b>{score}/100</b>",
            f"<b>{htmllib.escape(item['title'])}</b>",
            f"💶 <b>{price:.2f} {sym}</b>{htmllib.escape(disc)}",
            htmllib.escape(meta),
            htmllib.escape(extra),
        ]
        if flags:
            html_lines.append(f"<b>{htmllib.escape(flags)}</b>")
        if desc_short:
            html_lines.append(f"<i>« {htmllib.escape(desc_short)} »</i>")
        html_lines += [
            f"<i>{htmllib.escape(watch.name)} · réf. {htmllib.escape(ref_src)}</i>",
            htmllib.escape(item["url"]),
        ]
        return "\n".join(plain_lines), "\n".join(html_lines)

    def send(self, watch: Watch, item: dict, score: int, ref: float | None,
             ref_src: str, age: float | None, detail: dict | None = None):
        plain, html_text = self.format_text(watch, item, score, ref, ref_src, age, detail)
        log.info("ALERTE [%s] %s — %.2f %s (score %d) → %s",
                 watch.name, item["title"], item["price"] or 0,
                 item["currency"] or "", score, item["url"])
        if self.dry:
            print(plain + "\n")
            return
        if self.cfg.telegram_bot_token and self.cfg.telegram_chat_id:
            self._telegram(html_text, (detail or {}).get("photo") or item.get("photo"))
        elif not self.cfg.telegram_bot_token:
            print(plain + "\n")

    def _telegram(self, text: str, photo: str | None):
        base = f"https://api.telegram.org/bot{self.cfg.telegram_bot_token}"
        try:
            if photo and len(text) <= 1024:
                r = requests.post(f"{base}/sendPhoto", timeout=25, data={
                    "chat_id": self.cfg.telegram_chat_id, "photo": photo,
                    "caption": text, "parse_mode": "HTML"})
                if r.ok:
                    return
                log.debug("sendPhoto ko (%s), repli sendMessage", r.status_code)
            r = requests.post(f"{base}/sendMessage", timeout=25, data={
                "chat_id": self.cfg.telegram_chat_id, "text": text,
                "parse_mode": "HTML", "disable_web_page_preview": "false"})
            if not r.ok:
                log.error("Telegram : %s %s", r.status_code, r.text[:300])
        except Exception as e:
            log.error("Telegram : %s", e)

    def send_test(self):
        t = "✅ Test VintedDealBot : les notifications fonctionnent."
        if self.cfg.telegram_bot_token and self.cfg.telegram_chat_id:
            r = requests.post(
                f"https://api.telegram.org/bot{self.cfg.telegram_bot_token}/sendMessage",
                data={"chat_id": self.cfg.telegram_chat_id, "text": t}, timeout=25)
            print(t, f"(HTTP {r.status_code})")
        else:
            print("⚠️ token/chat_id Telegram manquant dans la config.")


class VintedBot:
    def __init__(self, settings: Settings, config_path: str, dry_run: bool = False):
        self.config_path = config_path
        self.local_path = local_watches_path(config_path, settings.extra_watches_file)
        self.s = settings
        self.db = Database(settings.db_path)
        self.api = VintedAPI(settings)
        self.notifier = Notifier(settings.notify, dry_run=dry_run)
        self._stop = False
        self._paused: set[str] = set()
        self._mtime = self._config_mtime()

    def _config_mtime(self) -> tuple[float, float]:
        def m(p: Path) -> float:
            try:
                return p.stat().st_mtime
            except OSError:
                return 0.0
        return m(Path(self.config_path)), m(self.local_path)

    def _read_local(self) -> dict:
        if not HAS_YAML:
            raise VintedError("PyYAML requis pour l'édition à chaud")
        if not self.local_path.exists():
            return {}
        try:
            return yaml.safe_load(self.local_path.read_text(encoding="utf-8")) or {}
        except Exception as e:
            raise VintedError(f"{self.local_path} illisible : {e}")

    def _write_local(self, data: dict):
        if not HAS_YAML:
            raise VintedError("PyYAML requis pour l'édition à chaud")
        if self.local_path.exists():
            backup = self.local_path.with_suffix(".yaml.bak")
            try:
                backup.write_text(self.local_path.read_text(encoding="utf-8"), encoding="utf-8")
            except Exception:
                pass
        self.local_path.write_text(
            yaml.safe_dump(data, allow_unicode=True, sort_keys=False, default_flow_style=False),
            encoding="utf-8")

    def find(self, name: str) -> Watch | None:
        key = norm(name)
        for w in self.s.watches:
            if norm(w.name) == key or norm(w.name).startswith(key):
                return w
        return None

    def build_params(self, w: Watch, page: int) -> dict[str, Any]:
        p: dict[str, Any] = {}
        if w.url:
            p.update(filters_from_url(w.url))
        if w.search_text:
            p["search_text"] = w.search_text
        if w.min_price:
            p["price_from"] = w.min_price
        if w.max_price < 100000:
            p["price_to"] = w.max_price
        ids = [CONDITIONS[c][0] for c in w.conditions if c in CONDITIONS]
        if ids:
            p["status_ids[]"] = ids
        p.update({"order": w.order, "currency": w.currency,
                  "page": page, "per_page": self.s.per_page})
        p.update(w.extra_params or {})
        return p

    def reference_price(self, w: Watch, items: list[dict]) -> tuple[float | None, str]:
        if w.reference_price:
            return float(w.reference_price), "prix configuré"
        hist = self.db.prices(w.name, days=14)
        if len(hist) >= 8:
            return float(statistics.median(hist)), f"médiane observée ({len(hist)} annonces)"
        prices = [i["price"] for i in items if i["price"]]
        if len(prices) >= 3:
            return float(statistics.median(prices)), "médiane du scan"
        return None, "inconnue"

    def evaluate(self, w: Watch, it: dict, ref: float | None):
        haystack = norm(f"{it['title']} {it['brand']}")
        if w.exclude_keywords and any(norm(k) in haystack for k in w.exclude_keywords):
            return False, "mot-clé exclu", 0
        if w.include_keywords and not all(norm(k) in haystack for k in w.include_keywords):
            return False, "mot-clé requis absent", 0
        if it["price"] is None:
            return False, "prix illisible", 0
        if it["price"] < w.min_price:
            return False, "sous le prix mini", 0
        if it["price"] > w.max_price:
            return False, "au-dessus du prix max", 0
        cond = condition_key(it["status"])
        if w.conditions and cond and cond not in w.conditions:
            return False, f"état {it['status']}", 0
        if ref and w.deal_ratio < 1.0 and it["price"] > ref * w.deal_ratio:
            return False, f"remise insuffisante ({(1 - it['price'] / ref) * 100:.0f} %)", 0
        age = item_age_minutes(it["created_at"])
        if w.max_age_hours and age is not None and age > w.max_age_hours * 60:
            return False, f"annonce ancienne ({age / 60:.0f} h)", 0
        return True, "ok", compute_score(it["price"], ref, cond, age)

    def verify_detail(self, w: Watch, it: dict) -> tuple[bool, str, dict]:
        if not w.verify_detail:
            return True, "", {}
        d = self.db.get_detail(it["id"], w.detail_ttl_hours)
        if d is None:
            d = self.api.fetch_item_detail(it["url"])
            if d is not None:
                self.db.save_detail(it["id"], d)
        if d is None:
            return (False, "fiche article illisible", {}) if w.detail_strict \
                else (True, "fiche indisponible (toléré)", {})
        if d.get("closed"):
            return False, "annonce clôturée", d
        if w.skip_reserved and d.get("reserved"):
            return False, "annonce réservée", d
        desc = norm(d.get("description"))
        if w.exclude_description_keywords and any(
                norm(k) in desc for k in w.exclude_description_keywords):
            return False, "description : mot-clé exclu", d
        if w.include_description_keywords and not all(
                norm(k) in desc for k in w.include_description_keywords):
            return False, "description : mot-clé requis absent", d
        if w.min_description_chars and d.get("desc_known") and \
                len(d.get("description") or "") < w.min_description_chars:
            return False, "description trop courte", d
        if w.min_seller_rating is not None and d.get("rating") is not None and \
                d["rating"] < w.min_seller_rating:
            return False, f"note vendeur {d['rating']}/5", d
        if w.min_seller_reviews and d.get("reviews") is not None and \
                d["reviews"] < w.min_seller_reviews:
            return False, f"seulement {d['reviews']} avis vendeur", d
        return True, "", d

    def poll(self, w: Watch, seed: bool = False) -> int:
        if norm(w.name) in {norm(p) for p in self._paused}:
            log.debug("[%s] en pause", w.name)
            return 0
        alerts = 0
        all_items: list[dict] = []
        for page in range(1, max(1, w.pages) + 1):
            try:
                data = self.api.search(self.build_params(w, page))
            except Exception as e:
                log.error("[%s] recherche page %d : %s", w.name, page, e)
                break
            raw_items = data.get("items") or []
            items = [parse_item(x, self.s.domain) for x in raw_items]
            items = [i for i in items if i["id"]]
            all_items.extend(items)
            if len(raw_items) < self.s.per_page:
                break

        if not all_items:
            log.info("[%s] aucun résultat", w.name)
            return 0

        ref, ref_src = self.reference_price(w, all_items)
        seeded = self.db.get_state(f"seeded:{w.name}") == "1"
        if seed or (w.seed_on_start and not seeded):
            self.db.mark_seen(w.name, all_items)
            self.db.add_prices(w.name, [i["price"] for i in all_items])
            self.db.set_state(f"seeded:{w.name}", "1")
            log.info("[%s] amorçage : %d annonces marquées comme vues (réf. %s : %s)",
                     w.name, len(all_items), f"{ref:.2f}" if ref else "n/a", ref_src)
            return 0

        known = self.db.seen_ids(w.name, [i["id"] for i in all_items])
        new_items = [i for i in all_items if i["id"] not in known]
        self.db.add_prices(w.name, [i["price"] for i in all_items])
        log.info("[%s] %d annonces, %d nouvelles, réf. %s (%s)",
                 w.name, len(all_items), len(new_items),
                 f"{ref:.2f}" if ref else "n/a", ref_src)

        checks = 0
        for it in new_items:
            ok, reason, score = self.evaluate(w, it, ref)
            detail: dict = {}
            if ok and checks < max(0, w.max_detail_checks):
                checks += 1
                ok, reason, detail = self.verify_detail(w, it)
                if ok:
                    age = item_age_minutes(it["created_at"])
                    score = compute_score(it["price"], ref, condition_key(it["status"]), age,
                                          detail)
                    if score < w.min_score:
                        ok, reason = False, f"score {score} < {w.min_score}"
            if ok:
                age = item_age_minutes(it["created_at"])
                self.notifier.send(w, it, score, ref, ref_src, age, detail)
                alerts += 1
            else:
                log.debug("[%s] rejeté %s (%s)", w.name, it["id"], reason)
        self.db.mark_seen(w.name, new_items)
        return alerts

    def run_once(self, seed: bool = False) -> int:
        total = 0
        for w in list(self.s.watches):
            total += self.poll(w, seed=seed)
        log.info("Cycle terminé — %d alerte(s)", total)
        return total

    def maybe_reload(self):
        mtime = self._config_mtime()
        if mtime != self._mtime:
            self.reload()

    def reload(self):
        try:
            s = load_settings(self.config_path)
        except SystemExit as e:
            log.error("Rechargement impossible : %s", e)
            return
        except Exception as e:
            log.error("Rechargement impossible : %s", e)
            return
        self.s = s
        self.api.s = s
        self.notifier.cfg = s.notify
        self._mtime = self._config_mtime()
        log.info("Config rechargée : %d recherche(s)", len(s.watches))

    def run_forever(self, interactive: bool = False):
        next_run = {w.name: 0.0 for w in self.s.watches}
        log.info("Surveillance de %d recherche(s) sur %s", len(self.s.watches), self.s.domain)
        while not self._stop:
            self.maybe_reload()
            names = {w.name for w in self.s.watches}
            for name in list(next_run):
                if name not in names:
                    next_run.pop(name, None)
            now = time.time()
            for w in self.s.watches:
                if self._stop:
                    break
                next_run.setdefault(w.name, 0.0)
                if next_run[w.name] <= now:
                    try:
                        self.poll(w)
                    except Exception as e:
                        log.exception("[%s] erreur de scan : %s", w.name, e)
                    next_run[w.name] = time.time() + w.interval * random.uniform(0.9, 1.2)
            time.sleep(2)
        log.info("Arrêt demandé.")

    def add_watch(self, d: dict) -> Watch:
        w = Watch.from_dict(d)
        local = self._read_local()
        local.setdefault("watches", [])
        local["watches"] = [x for x in local["watches"] if norm(x.get("name")) != norm(w.name)]
        local["watches"].append(d)
        self._write_local(local)
        self.reload()
        return self.find(w.name) or w

    def remove_watch(self, name: str) -> bool:
        local = self._read_local()
        before = len(local.get("watches") or [])
        local["watches"] = [x for x in (local.get("watches") or [])
                            if norm(x.get("name")) != norm(name)]
        if len(local["watches"]) != before:
            self._write_local(local)
            self.reload()
            return True
        disabled = local.setdefault("disabled", [])
        if norm(name) not in {norm(x) for x in disabled}:
            disabled.append(name)
        self._write_local(local)
        self.reload()
        return True

    def set_override(self, name: str, key: str, value: Any):
        local = self._read_local()
        ov = local.setdefault("overrides", {})
        ov.setdefault(name, {})[key] = value
        self._write_local(local)
        self.reload()

    def stop(self, *_: Any):
        self._stop = True


class Interactive:
    def __init__(self, bot: VintedBot):
        self.bot = bot

    def start(self):
        threading.Thread(target=self.loop, name="console", daemon=True).start()

    def loop(self):
        print(HELP)
        while not self.bot._stop:
            try:
                line = input("vinted> ").strip()
            except (EOFError, KeyboardInterrupt):
                print()
                return
            if not line:
                continue
            try:
                self.dispatch(line)
            except Exception as e:
                print(f"! {e}")

    def dispatch(self, line: str):
        try:
            args = shlex.split(line)
        except ValueError as e:
            print(f"! {e}")
            return
        cmd = args[0].lower()
        rest = args[1:]
        bot = self.bot

        if cmd in ("quit", "exit", "q"):
            bot.stop()
        elif cmd in ("help", "h", "?"):
            print(HELP)
        elif cmd in ("list", "ls"):
            for w in bot.s.watches:
                ref = f"{w.reference_price:.0f}" if w.reference_price else "auto"
                print(f"- {w.name} | max={w.max_price:.0f} ratio={w.deal_ratio} réf={ref} "
                      f"toutesles={w.interval}s score>{w.min_score} "
                      f"fiche={'oui' if w.verify_detail else 'non'}")
        elif cmd == "show":
            w = bot.find(" ".join(rest)) if rest else None
            if not w:
                print("introuvable.")
                return
            for k, v in asdict(w).items():
                print(f"  {k}: {v}")
        elif cmd == "add":
            if not rest:
                print("format : add \"nom\" | \"recherche\" | prix_max | ratio")
                return
            self.cmd_add_quick(" | ".join(rest))
        elif cmd in ("rm", "remove", "del"):
            if not rest:
                print("usage : rm <nom>")
                return
            ok = bot.remove_watch(" ".join(rest))
            print("supprimée/désactivée." if ok else "introuvable.")
        elif cmd in ("pause", "resume"):
            targets = [bot.find(" ".join(rest))] if rest else list(bot.s.watches)
            targets = [w for w in targets if w]
            for w in targets:
                if cmd == "pause":
                    bot._paused.add(w.name)
                else:
                    bot._paused.discard(w.name)
            print(f"{cmd} : {', '.join(w.name for w in targets) or 'rien'}")
        elif cmd in ("scan", "check", "seed"):
            targets = [bot.find(" ".join(rest))] if rest else list(bot.s.watches)
            targets = [w for w in targets if w]
            for w in targets:
                n = bot.poll(w, seed=(cmd == "seed"))
                print(f"[{w.name}] {cmd} ok — {n} alerte(s)")
        elif cmd == "ref":
            if len(rest) < 2:
                print("usage : ref <nom> <prix>")
                return
            w = bot.find(" ".join(rest[:-1]))
            if not w:
                print("introuvable.")
                return
            bot.set_override(w.name, "reference_price", float(rest[-1].replace(",", ".")))
            print(f"référence de '{w.name}' fixée à {rest[-1]}.")
        else:
            print(f"commande inconnue : {cmd} (help pour l'aide)")

    def cmd_add_quick(self, line: str):
        parts = [p.strip() for p in line.split("|")]
        if len(parts) < 2:
            print("format : add \"nom\" | \"recherche\" | prix_max | ratio")
            return
        name, query = parts[0], parts[1]
        d: dict[str, Any] = {"name": name}
        if query.startswith("http"):
            d["url"] = query
        else:
            d["search_text"] = query
        if len(parts) > 2 and parts[2]:
            d["max_price"] = float(parts[2].replace(",", "."))
        if len(parts) > 3 and parts[3]:
            d["deal_ratio"] = float(parts[3].replace(",", "."))
        self.bot.add_watch(d)
        print(f"'{name}' ajoutée et active (scan au prochain cycle).")


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Bot de surveillance des bonnes affaires Vinted")
    ap.add_argument("-c", "--config", default=os.environ.get("VINTED_CONFIG", "config.yaml"))
    ap.add_argument("--once", action="store_true", help="un seul cycle puis sortie")
    ap.add_argument("--seed", action="store_true", help="marque les annonces actuelles comme vues")
    ap.add_argument("--dry-run", action="store_true", help="affiche sans notifier")
    ap.add_argument("--test-notify", action="store_true", help="message de test")
    ap.add_argument("--interactive", action="store_true", help="surveillance + console de commandes")
    ap.add_argument("--debug", action="store_true")
    a = ap.parse_args(argv)

    settings = load_settings(a.config)
    logging.basicConfig(
        level=logging.DEBUG if a.debug else getattr(logging, settings.log_level.upper(),
                                                    logging.INFO),
        format="%(asctime)s %(levelname)-7s %(message)s", datefmt="%H:%M:%S")

    bot = VintedBot(settings, a.config, dry_run=a.dry_run)
    if a.test_notify:
        bot.notifier.send_test()
        return 0
    if a.seed:
        bot.run_once(seed=True)
        return 0
    if a.once:
        bot.run_once()
        return 0

    signal.signal(signal.SIGTERM, bot.stop)
    signal.signal(signal.SIGINT, bot.stop)
    if a.interactive:
        Interactive(bot).start()
    bot.run_forever()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
