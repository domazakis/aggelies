"""Καθημερινή συλλογή αγγελιών εργασίας.

Τρέχει στο GitHub Actions λίγο πριν από το scheduled task του Claude.
Μαζεύει αγγελίες από τις πηγές που ανοίγουν κανονικά από τους servers του GitHub
(kariera.gr, Workable, jobfind.gr, Ωνάσειο, alfavita, proson), ανοίγει κάθε ΝΕΑ αγγελία
για να πάρει το πλήρες κείμενο και τον σύνδεσμο αίτησης, και γράφει:

  data/recent.json        οι αγγελίες που εμφανίστηκαν για πρώτη φορά τις τελευταίες 3 ημέρες
  data/details/<πηγή>/<id>.md   πλήρες κείμενο κάθε αγγελίας
  data/excluded.json      όσες κόπηκαν αυτόματα από τον τίτλο (με τον λόγο)
  data/run_report.md      τι διαβάστηκε από κάθε πηγή και τι απέτυχε
  data/seen.json          μνήμη όλων όσων έχουν ήδη δει (για να μη θεωρούνται ξανά νέες)

Το φιλτράρισμα με τα πραγματικά κριτήρια (περιοχή, επίπεδο, ρόλος) το κάνει το Claude.
Εδώ κόβονται μόνο όσα είναι προφανώς άσχετα από τον τίτλο, για να μένει μικρή η λίστα.
Σέβεται το robots.txt κάθε site.
"""

from __future__ import annotations

import json
import re
import sys
import time
import unicodedata
import urllib.parse
import urllib.robotparser
from datetime import date, datetime, timedelta, timezone
from pathlib import Path

import requests
from bs4 import BeautifulSoup

# ---------------------------------------------------------------- ρυθμίσεις

UA = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/130.0 Safari/537.36"
)
HEADERS = {
    "User-Agent": UA,
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,application/json;q=0.8,*/*;q=0.7",
    "Accept-Language": "el-GR,el;q=0.9,en;q=0.8",
}
TIMEOUT = 30
PAUSE = 1.5            # δευτερόλεπτα ανάμεσα στα αιτήματα στο ίδιο site
RECENT_DAYS = 3        # πόσες μέρες μένει μια αγγελία στο recent.json
WORKABLE_MAX_AGE = 21  # αγγελίες Workable παλαιότερες από τόσες μέρες αγνοούνται
SEEN_KEEP_DAYS = 180
DETAILS_KEEP_DAYS = 30
MAX_TEXT = 7000        # χαρακτήρες κειμένου ανά αγγελία
DETAIL_BUDGET = 18 * 60  # μέγιστος χρόνος (δευτ.) για άνοιγμα σελίδων αγγελιών ανά εκτέλεση·
                         # όσες δεν προλάβουν μένουν για την επόμενη εκτέλεση

KARIERA_TERMS = [
    "επικοινωνία", "communications", "δημόσιες σχέσεις", "PR", "εκδηλώσεις", "events",
    "project manager", "programme manager", "υπεύθυνος επικοινωνίας",
    "marketing τουρισμός", "marketing πολιτισμός",
]
KARIERA_CATEGORIES = [
    "public-relations-jobs",
    "marketing-or-advertising-jobs",
    "tourism-jobs",
    "strategy-or-planning-jobs",
]
KARIERA_PAGES = 4

WORKABLE_QUERIES = [
    "communications", "επικοινωνία", "public relations", "δημόσιες σχέσεις", "PR",
    "events", "εκδηλώσεις", "event manager", "project manager", "programme manager",
    "program manager", "marketing",
]
WORKABLE_PAGES = 4

JOBFIND_CATEGORIES = [
    "https://www.jobfind.gr/JobAdsSearchCatCity/GR/Theseis-Ergasias-ana-Eidikotita/6/Marketing",
    "https://www.jobfind.gr/JobAdsSearchCatCity/GR/Theseis-Ergasias-ana-Eidikotita/4/Stelexi_Epixeiriseon",
    "https://www.jobfind.gr/JobAdsSearchCatCity/GR/Theseis-Ergasias-ana-Eidikotita/13/Tourismos",
]

# alfavita / proson: κρατάμε μόνο ό,τι αφορά πολιτισμό / ιδρύματα / επικοινωνία
NEWS_KEEP = [
    "μουσει", "πολιτισμ", "ιδρυμ", "κπισν", "στεγη", "θεατρ", "φεστιβαλ", "μεγαρο",
    "επικοινων", "δημοσιων σχεσεων", "εκδηλωσ", "λυρικη", "οπερα", "ορχηστρ",
    "γαστρονομ", "τουρισμ", "εοτ",
]

# Τίτλοι που κόβονται αυτόματα (ήδη αποκλεισμένοι από τα κριτήρια ή εντελώς εκτός ρόλου)
EXCLUDE_TITLE = [  # κανονικές εκφράσεις πάνω σε πεζά χωρίς τόνους (ς -> σ)
    (r"πωλητ", "πωλήσεις/λιανική"), (r"\bταμι(ασ|εσ|α)\b", "λιανική"),
    (r"sales (advisor|agent|associate|representative)", "πωλήσεις"), (r"εκπροσωπ\w* πωλησ", "πωλήσεις"),
    (r"πωλησεισ μεσω", "πωλήσεις"), (r"telesales", "πωλήσεις"), (r"door.to.door", "πωλήσεις"),
    (r"promoter", "πωλήσεις/promoter"), (r"προωθησ", "πωλήσεις/promoter"),
    (r"event representative", "πωλήσεις/ΜΚΟ"), (r"\bμκο\b", "πωλήσεις/ΜΚΟ"),
    (r"campaign representative", "πωλήσεις/ΜΚΟ"), (r"brand representative", "πωλήσεις"),
    (r"call.?cent", "τηλεφωνικό κέντρο"), (r"τηλεφωνικ", "τηλεφωνικό κέντρο"), (r"\bagents?\b", "τηλεφωνικό κέντρο"),
    (r"εξυπηρετησ\w* πελατ", "τηλεφωνικό κέντρο"), (r"back.?office", "υπαλληλική θέση"),
    (r"\bοδηγ", "εκτός ρόλου"), (r"διανομ", "εκτός ρόλου"), (r"courier", "εκτός ρόλου"),
    (r"αποθηκ", "εκτός ρόλου"), (r"picker", "εκτός ρόλου"), (r"warehouse", "εκτός ρόλου"),
    (r"μαγειρ", "εστίαση"), (r"σερβιτ", "εστίαση"), (r"barista", "εστίαση"), (r"εστιατορ", "εστίαση"),
    (r"καθαρισ", "εκτός ρόλου"), (r"\bsecurity\b", "εκτός ρόλου"), (r"φυλακ", "εκτός ρόλου"),
    (r"λογιστ", "εκτός ρόλου"), (r"μηχανικ", "εκτός ρόλου"), (r"\bτεχνικ", "εκτός ρόλου"),
    (r"developer", "εκτός ρόλου"), (r"engineer", "εκτός ρόλου"), (r"νοσηλ", "εκτός ρόλου"),
    (r"κομμω", "εκτός ρόλου"), (r"αισθητικ", "εκτός ρόλου"), (r"ηλεκτρολογ", "εκτός ρόλου"),
    (r"υπαλληλ\w* καταστηματ", "λιανική"), (r"\bretail\b", "λιανική"),
    (r"\bjunior\b", "entry level/junior"), (r"entry.level", "entry level/junior"),
    (r"\bintern(ship)?s?\b", "πρακτική άσκηση"), (r"πρακτικη ασκηση", "πρακτική άσκηση"),
    (r"ασκουμεν", "πρακτική άσκηση"), (r"χωρισ προυπηρεσια", "entry level/junior"),
    (r"εποχικ", "εποχική"), (r"christmas season", "εποχική"),
]

APPLY_HINT = re.compile(
    r"(workable\.com|smartcv\.co|greenhouse\.io|lever\.co|teamtailor|recruitee|bamboohr|personio|"
    r"successfactors|taleo|myworkday|forms\.gle|docs\.google\.com/forms|/apply|apply now|"
    r"κάνε αίτηση|υποβολή αίτησης|αίτηση|careers?\.)",
    re.I,
)
EMAIL_RE = re.compile(r"[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}")

ROOT = Path(__file__).parent
DATA = ROOT / "data"
TODAY = datetime.now(timezone.utc).astimezone(timezone(timedelta(hours=3))).date()  # ώρα Ελλάδας (περίπου)

# ---------------------------------------------------------------- βοηθητικά

session = requests.Session()
session.headers.update(HEADERS)
_robots: dict[str, urllib.robotparser.RobotFileParser | None] = {}
_last_hit: dict[str, float] = {}
report: dict[str, dict] = {}


def norm(s: str) -> str:
    """πεζά, χωρίς τόνους, για συγκρίσεις"""
    s = unicodedata.normalize("NFD", s.lower())
    s = "".join(c for c in s if unicodedata.category(c) != "Mn")
    return re.sub(r"\s+", " ", s.replace("ς", "σ")).strip()


def allowed(url: str) -> bool:
    p = urllib.parse.urlsplit(url)
    root = f"{p.scheme}://{p.netloc}"
    if root not in _robots:
        rp = urllib.robotparser.RobotFileParser()
        try:
            r = session.get(root + "/robots.txt", timeout=TIMEOUT)
            if r.status_code in (401, 403):
                rp.disallow_all = True
            elif r.status_code >= 400:
                rp.allow_all = True
            else:
                rp.parse(r.text.splitlines())
        except requests.RequestException:
            rp.allow_all = True
        _robots[root] = rp
    return _robots[root].can_fetch("*", url)


def get(url: str, src: str, **kw) -> requests.Response | None:
    rep = report.setdefault(src, {"requests": 0, "ok": 0, "errors": [], "found": 0, "new": 0, "excluded": 0})
    if not allowed(url):
        rep["errors"].append(f"robots.txt απαγορεύει: {url}")
        return None
    host = urllib.parse.urlsplit(url).netloc
    wait = PAUSE - (time.time() - _last_hit.get(host, 0))
    if wait > 0:
        time.sleep(wait)
    rep["requests"] += 1
    for attempt in (1, 2):
        try:
            r = session.get(url, timeout=TIMEOUT, **kw)
            _last_hit[host] = time.time()
            if r.status_code == 200:
                rep["ok"] += 1
                return r
            if attempt == 2 or r.status_code not in (429, 500, 502, 503, 504):
                rep["errors"].append(f"HTTP {r.status_code}: {url}")
                return None
        except requests.RequestException as e:
            if attempt == 2:
                rep["errors"].append(f"{type(e).__name__}: {url}")
                return None
        time.sleep(5)
    return None


def clean_text(soup: BeautifulSoup) -> str:
    for t in soup(["script", "style", "noscript", "header", "footer", "nav", "form", "svg", "iframe"]):
        t.decompose()
    main = soup.find("main") or soup.find("article") or soup.body or soup
    text = main.get_text("\n", strip=True)
    lines = [l for l in (x.strip() for x in text.split("\n")) if l]
    out, prev = [], None
    for l in lines:
        if l != prev:
            out.append(l)
        prev = l
    return "\n".join(out)[:MAX_TEXT]


def apply_from_soup(soup: BeautifulSoup, base: str, page_host: str) -> list[str]:
    found = []
    for a in soup.find_all("a", href=True):
        href = a["href"].strip()
        txt = " ".join(a.get_text(" ", strip=True).split())
        if href.startswith("mailto:"):
            found.append(href.split("?")[0])
            continue
        full = urllib.parse.urljoin(base, href)
        host = urllib.parse.urlsplit(full).netloc
        if not host or "career-guide" in full or "career/home" in full:
            continue
        if host.endswith(page_host) and "apply" not in full.lower():
            continue
        if APPLY_HINT.search(full) or APPLY_HINT.search(txt):
            found.append(full)
    return list(dict.fromkeys(found))[:5]


def emails_in(text: str) -> list[str]:
    bad = ("example.", "sentry", "wixpress", "@2x", ".png", ".jpg")
    return [e for e in dict.fromkeys(EMAIL_RE.findall(text)) if not any(b in e.lower() for b in bad)][:5]


def exclusion_reason(title: str) -> str | None:
    t = norm(title)
    for pattern, reason in EXCLUDE_TITLE:
        if re.search(pattern, t):
            return reason
    return None


# ---------------------------------------------------------------- πηγές
# Κάθε συνάρτηση επιστρέφει λίστα από dict: source, id, title, url (+ ό,τι άλλο ξέρει)

def src_kariera() -> list[dict]:
    items: dict[str, dict] = {}
    rx = re.compile(r"/jobs/[a-z0-9-]+/(\d{5,})")

    def scan(url: str):
        r = get(url, "kariera")
        if not r:
            return 0
        soup = BeautifulSoup(r.text, "lxml")
        n = 0
        for a in soup.find_all("a", href=True):
            m = rx.search(a["href"])
            title = " ".join(a.get_text(" ", strip=True).split())
            if not m or not title:
                continue
            jid = m.group(1)
            if jid not in items:
                items[jid] = {"source": "kariera", "id": jid, "title": title[:200],
                              "url": f"https://www.kariera.gr/jobs/{a['href'].split('/jobs/')[-1].split('?')[0]}"}
                n += 1
        return n

    for term in KARIERA_TERMS:
        for page in range(1, KARIERA_PAGES + 1):
            u = f"https://www.kariera.gr/jobs?title={urllib.parse.quote(term)}&location=Athens"
            if page > 1:
                u += f"&page={page}"
            if scan(u) == 0 and page > 1:
                break
    for cat in KARIERA_CATEGORIES:
        for page in range(1, KARIERA_PAGES + 1):
            u = f"https://www.kariera.gr/en/jobs/{cat}" + (f"?page={page}" if page > 1 else "")
            if scan(u) == 0 and page > 1:
                break
    return list(items.values())


def detail_kariera(it: dict) -> None:
    r = get(it["url"], "kariera")
    if not r:
        return
    soup = BeautifulSoup(r.text, "lxml")
    t = soup.title.string if soup.title and soup.title.string else ""
    # μορφή: "Τίτλος — Εταιρεία | Περιοχή"
    m = re.match(r"\s*(.*?)\s+—\s+(.*?)\s*\|\s*(.*?)\s*$", t or "")
    if m:
        it["company"], it["location"] = m.group(2), m.group(3)
    it["apply"] = apply_from_soup(soup, r.url, "kariera.gr")
    text = clean_text(soup)
    it["emails"] = emails_in(text)
    it["text"] = text


def src_workable() -> list[dict]:
    items: dict[str, dict] = {}
    cutoff = TODAY - timedelta(days=WORKABLE_MAX_AGE)
    for q in WORKABLE_QUERIES:
        token = None
        for _ in range(WORKABLE_PAGES):
            params = {"query": q, "location": "Athens"}
            if token:
                params["pageToken"] = token
            u = "https://jobs.workable.com/api/v1/jobs?" + urllib.parse.urlencode(params)
            r = get(u, "workable")
            if not r:
                break
            try:
                js = r.json()
            except ValueError:
                report["workable"]["errors"].append(f"όχι JSON: {u}")
                break
            for j in js.get("jobs", []):
                jid = j.get("id")
                if not jid or jid in items:
                    continue
                created = (j.get("created") or "")[:10]
                try:
                    if created and date.fromisoformat(created) < cutoff:
                        continue
                except ValueError:
                    pass
                comp = j.get("company") or {}
                loc = j.get("location") or {}
                parts = [j.get("description") or "", j.get("requirementsSection") or "", j.get("benefitsSection") or ""]
                text = BeautifulSoup("\n".join(parts), "lxml").get_text("\n", strip=True)[:MAX_TEXT]
                items[jid] = {
                    "source": "workable", "id": jid, "title": (j.get("title") or "")[:200],
                    "company": comp.get("title") if isinstance(comp, dict) else str(comp),
                    "location": ", ".join(x for x in [loc.get("city"), loc.get("subregion")] if x) if isinstance(loc, dict) else str(loc),
                    "posted": created, "employment": j.get("employmentType") or "",
                    "workplace": j.get("workplace") or "",
                    "url": j.get("url") or "", "apply": [(j.get("url") or "").rstrip("/") + "/apply"] if j.get("url") else [],
                    "text": text, "emails": emails_in(text), "_detail_done": True,
                }
            token = js.get("nextPageToken")
            if not token:
                break
    return list(items.values())


def src_jobfind() -> list[dict]:
    items: dict[str, dict] = {}
    rx = re.compile(r"/JobAd/View/GR/Theseis_Ergasias/([0-9a-fA-F-]{36})")
    for url in JOBFIND_CATEGORIES:
        r = get(url, "jobfind")
        if not r:
            continue
        soup = BeautifulSoup(r.text, "lxml")
        for a in soup.find_all("a", href=True):
            m = rx.search(a["href"])
            title = " ".join(a.get_text(" ", strip=True).split())
            if not m or not title:
                continue
            jid = m.group(1).lower()
            items.setdefault(jid, {"source": "jobfind", "id": jid, "title": title[:200],
                                   "url": f"https://www.jobfind.gr/JobAd/View/GR/Theseis_Ergasias/{m.group(1)}/"})
    return list(items.values())


def detail_jobfind(it: dict) -> None:
    r = get(it["url"], "jobfind")
    if not r:
        return
    soup = BeautifulSoup(r.text, "lxml")
    t = soup.title.string if soup.title and soup.title.string else ""
    m = re.match(r"\s*Θέσεις Εργασίας:\s*(.*?)\s+-\s+(.*)$", t or "")
    if m:
        it["location"] = m.group(2).strip()
    it["apply"] = apply_from_soup(soup, r.url, "jobfind.gr")
    text = clean_text(soup)
    it["emails"] = emails_in(text)
    it["text"] = text


def src_onassis() -> list[dict]:
    r = get("https://apply.smartcv.co/onassis-group/", "onassis")
    if not r:
        return []
    soup = BeautifulSoup(r.text, "lxml")
    out = {}
    for a in soup.find_all("a", href=True):
        m = re.search(r"/onassis-group/job/(\w+)", a["href"])
        title = " ".join(a.get_text(" ", strip=True).split())
        if m and title and "future openings" not in title.lower():
            out.setdefault(m.group(1), {"source": "onassis", "id": m.group(1), "title": title[:200],
                                        "company": "Ίδρυμα Ωνάση (Onassis Group)",
                                        "url": f"https://apply.smartcv.co/onassis-group/job/{m.group(1)}"})
    return list(out.values())


def detail_generic(it: dict, src: str) -> None:
    r = get(it["url"], src)
    if not r:
        return
    soup = BeautifulSoup(r.text, "lxml")
    host = urllib.parse.urlsplit(r.url).netloc.replace("www.", "")
    it["apply"] = apply_from_soup(soup, r.url, host) or ([it["url"]] if src == "onassis" else [])
    text = clean_text(soup)
    it["emails"] = emails_in(text)
    it["text"] = text


def src_news(src: str, url: str, rx: str, base: str) -> list[dict]:
    r = get(url, src)
    if not r:
        return []
    soup = BeautifulSoup(r.text, "lxml")
    out = {}
    for a in soup.find_all("a", href=True):
        m = re.search(rx, a["href"])
        title = " ".join(a.get_text(" ", strip=True).split())
        if m and title and len(title) > 20:
            out.setdefault(m.group(1), {"source": src, "id": m.group(1), "title": title[:220],
                                        "url": urllib.parse.urljoin(base, a["href"].split("?")[0])})
    return list(out.values())


# ---------------------------------------------------------------- κύρια ροή

def load(path: Path, default):
    try:
        return json.loads(path.read_text())
    except (OSError, ValueError):
        return default


def main() -> int:
    DATA.mkdir(exist_ok=True)
    seen: dict = load(DATA / "seen.json", {})
    recent_old: list = load(DATA / "recent.json", {}).get("listings", []) if (DATA / "recent.json").exists() else []
    first_run = not seen

    collected: list[dict] = []
    collectors = [
        ("kariera", src_kariera),
        ("workable", src_workable),
        ("jobfind", src_jobfind),
        ("onassis", src_onassis),
        ("alfavita", lambda: src_news("alfavita", "https://www.alfavita.gr/ergasia", r"/ergasia/(\d{6})_", "https://www.alfavita.gr")),
        ("proson", lambda: src_news("proson", "https://www.proson.gr/ergasia/prokiryxeis", r"/ergasia/prokiryxeis/(\d+)_", "https://www.proson.gr")),
    ]
    for name, fn in collectors:
        report.setdefault(name, {"requests": 0, "ok": 0, "errors": [], "found": 0, "new": 0, "excluded": 0})
        try:
            got = fn()
        except Exception as e:  # μια πηγή που σπάει δεν σταματά τις άλλες
            report[name]["errors"].append(f"σφάλμα script: {type(e).__name__}: {e}")
            got = []
        report[name]["found"] = len(got)
        collected.extend(got)
        print(f"{name}: {len(got)}")

    excluded, new_items = [], []
    for it in collected:
        key = f"{it['source']}:{it['id']}"
        if key in seen:
            seen[key]["last_seen"] = TODAY.isoformat()
            continue
        if it["source"] in ("alfavita", "proson"):
            reason = None if any(k in norm(it["title"]) for k in NEWS_KEEP) else "είδηση εκτός πολιτισμού/ιδρυμάτων"
        else:
            reason = exclusion_reason(it["title"])
        seen[key] = {"first_seen": TODAY.isoformat(), "last_seen": TODAY.isoformat(), "title": it["title"][:120]}
        if reason:
            excluded.append({"source": it["source"], "title": it["title"], "url": it["url"], "reason": reason})
            report[it["source"]]["excluded"] += 1
            continue
        it["first_seen"] = TODAY.isoformat()
        new_items.append(it)
        report[it["source"]]["new"] += 1

    # πλήρες κείμενο για κάθε νέα αγγελία, μέσα σε χρονικό όριο
    t_start = time.time()
    postponed = []
    for it in list(new_items):
        if it.pop("_detail_done", False):
            continue
        if time.time() - t_start > DETAIL_BUDGET:
            # δεν προλάβαμε: ξεχνάμε ότι την είδαμε, θα ξαναβρεθεί αύριο ως νέα
            postponed.append(it)
            new_items.remove(it)
            seen.pop(f"{it['source']}:{it['id']}", None)
            report[it["source"]]["new"] -= 1
            continue
        try:
            if it["source"] == "kariera":
                detail_kariera(it)
            elif it["source"] == "jobfind":
                detail_jobfind(it)
            else:
                detail_generic(it, it["source"])
        except Exception as e:  # noqa: BLE001
            report[it["source"]]["errors"].append(f"σελίδα αγγελίας: {type(e).__name__}: {it['url']}")

    # αποθήκευση κειμένων
    for it in new_items:
        d = DATA / "details" / it["source"]
        d.mkdir(parents=True, exist_ok=True)
        path = d / f"{re.sub(r'[^A-Za-z0-9_-]', '_', it['id'])}.md"
        head = [f"# {it['title']}", "", f"- Πηγή: {it['source']}", f"- Σύνδεσμος αγγελίας: {it['url']}"]
        for k, label in (("company", "Εργοδότης"), ("location", "Περιοχή"), ("posted", "Δημοσίευση"),
                         ("employment", "Απασχόληση"), ("workplace", "Τρόπος εργασίας")):
            if it.get(k):
                head.append(f"- {label}: {it[k]}")
        head.append(f"- Αίτηση (σύνδεσμοι που βρέθηκαν στη σελίδα): {', '.join(it.get('apply') or []) or '—'}")
        head.append(f"- Emails στο κείμενο: {', '.join(it.get('emails') or []) or '—'}")
        head.append(f"- Πρώτη φορά: {it['first_seen']}")
        body = it.get("text") or "(Δεν διαβάστηκε το κείμενο της σελίδας.)"
        path.write_text("\n".join(head) + "\n\n---\n\n" + body + "\n")
        it["detail_file"] = str(path.relative_to(ROOT))

    # recent.json: νέες σήμερα + όσες ήταν νέες τις προηγούμενες RECENT_DAYS ημέρες
    cutoff = (TODAY - timedelta(days=RECENT_DAYS - 1)).isoformat()
    keep_old = [x for x in recent_old if x.get("first_seen", "") >= cutoff
                and f"{x['source']}:{x['id']}" not in {f"{n['source']}:{n['id']}" for n in new_items}]
    compact = []
    for it in new_items:
        c = {k: it.get(k) for k in ("source", "id", "title", "company", "location", "posted", "employment",
                                    "workplace", "url", "apply", "emails", "first_seen", "detail_file") if it.get(k)}
        c["text_chars"] = len(it.get("text") or "")
        compact.append(c)
    listings = sorted(keep_old + compact, key=lambda x: (x.get("first_seen", ""), x["source"]), reverse=True)

    (DATA / "recent.json").write_text(json.dumps({
        "_perigrafi": ("Αγγελίες που εμφανίστηκαν για πρώτη φορά τις τελευταίες "
                       f"{RECENT_DAYS} ημέρες. Το πλήρες κείμενο κάθε αγγελίας είναι στο detail_file. "
                       "Έχουν ήδη αφαιρεθεί όσες είναι προφανώς άσχετες από τον τίτλο (δες excluded.json)."),
        "enimerosi": datetime.now(timezone.utc).isoformat(timespec="minutes"),
        "proti_ektelesi": first_run,
        "listings": listings,
    }, ensure_ascii=False, indent=1))
    (DATA / "excluded.json").write_text(json.dumps({"imerominia": TODAY.isoformat(), "excluded": excluded},
                                                   ensure_ascii=False, indent=1))

    # καθάρισμα μνήμης και παλιών κειμένων
    old = (TODAY - timedelta(days=SEEN_KEEP_DAYS)).isoformat()
    seen = {k: v for k, v in seen.items() if v.get("last_seen", v.get("first_seen", "")) >= old}
    (DATA / "seen.json").write_text(json.dumps(seen, ensure_ascii=False, indent=0, sort_keys=True))
    det_cut = time.time() - DETAILS_KEEP_DAYS * 86400
    for f in (DATA / "details").glob("*/*.md"):
        if f.stat().st_mtime < det_cut:
            f.unlink()

    # αναφορά εκτέλεσης
    lines = [f"# Συλλογή {TODAY.isoformat()} ({datetime.now(timezone.utc).strftime('%H:%M')} UTC)", "",
             "| Πηγή | Αιτήματα OK | Βρέθηκαν | Νέες | Κόπηκαν από τίτλο | Σφάλματα |", "|---|---|---|---|---|---|"]
    for name, rep in report.items():
        lines.append(f"| {name} | {rep['ok']}/{rep['requests']} | {rep['found']} | {rep['new']} | {rep['excluded']} | {len(rep['errors'])} |")
    lines += ["", f"Στο recent.json: {len(listings)} αγγελίες (από τις οποίες {len(compact)} νέες σήμερα)."]
    if postponed:
        lines.append(f"Αναβλήθηκαν για την επόμενη εκτέλεση λόγω χρόνου: {len(postponed)} αγγελίες.")
    lines.append("")
    for name, rep in report.items():
        if rep["errors"]:
            lines.append(f"## Σφάλματα {name}")
            lines += [f"- {e}" for e in rep["errors"][:30]]
            lines.append("")
    (DATA / "run_report.md").write_text("\n".join(lines))
    print("\n".join(lines))

    # αποτυχία μόνο αν δεν δούλεψε ΚΑΜΙΑ πηγή
    return 0 if any(r["ok"] for r in report.values()) else 1


if __name__ == "__main__":
    sys.exit(main())
