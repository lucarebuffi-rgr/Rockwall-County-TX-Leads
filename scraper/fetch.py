#!/usr/bin/env python3
"""
Rockwall County TX – Motivated Seller Lead Scraper
Clerk : rockwalltx-web.tylerhost.net (Tyler Technologies)
CAD   : Local DBF committed to repo at scraper/rockwall_ownership.zip
        (Rockwall CAD does not publish a public bulk URL)

Output schema matches Kaufman/Hill exactly so the dashboard renders identically.
"""

import asyncio
import csv
import io
import json
import logging
import os
import re
import struct
import traceback
import zipfile
from datetime import datetime, timedelta
from difflib import SequenceMatcher
from pathlib import Path
from typing import Optional

import httpx
from bs4 import BeautifulSoup

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    datefmt="%Y-%m-%d %H:%M:%S",
)
log = logging.getLogger(__name__)

BASE_URL      = "https://rockwalltx-web.tylerhost.net/web/search/DOCSEARCH542S1"
BASE_HOST     = "https://rockwalltx-web.tylerhost.net"
SEARCH_ID     = "DOCSEARCH542S1"
# CAD file is committed to the repo. Path is relative to repo root (where the workflow runs).
CAD_ZIP_PATH  = "scraper/rockwall_ownership.zip"
CAD_DBF_NAME  = "rockwall_ownership.dbf"
LOOKBACK_DAYS = int(os.getenv("LOOKBACK_DAYS", "14"))

DOC_TYPES = {
    "LIS PENDENS"         : ("pre_foreclosure", "Lis Pendens",          "LISPENDENS"),
    "FEDERAL TAX LIEN"    : ("lien",            "Federal Tax Lien",     "FTL"),
    "STATE TAX LIEN"      : ("lien",            "State Tax Lien",       "STL"),
    "JUDGMENT"            : ("judgment",        "Judgment",             "JUDGMENT"),
    "MECHANICS LIEN"      : ("lien",            "Mechanics Lien",       "MLIEN"),
    "LIEN"                : ("lien",            "Lien",                 "LIEN"),
    "CHILD SUPPORT LIEN"  : ("lien",            "Child Support Lien",   "CHILDSUPPORTLIEN"),
    "HEIRSHIP AFFIDAVIT"  : ("probate",         "Heirship Affidavit",   "HF"),
    "PROBATE"             : ("probate",         "Probate",              "PROBATE"),
    "DIVORCE DECREE"      : ("other",           "Divorce Decree",       "DD"),
}

# For these doc types, the GRANTEE is the property owner / motivated seller.
# DIVORCE DECREE is special - we match against either side (handled in enrich_with_parcel).
GRANTEE_IS_OWNER = {
    "FEDERAL TAX LIEN", "STATE TAX LIEN",
    "JUDGMENT", "MECHANICS LIEN", "LIEN",
    "CHILD SUPPORT LIEN",
}

# Doc types where we should match against either grantor or grantee
EITHER_SIDE_OWNER = {"DIVORCE DECREE"}

NAME_SUFFIXES = {"JR", "SR", "II", "III", "IV", "V", "ESQ", "TRUSTEE", "TR",
                 "ETAL", "ET", "AL", "ET AL", "ETUX", "ET UX", "ESTATE",
                 "DECEASED", "DECD"}

ENTITY_FILTERS = (
    "LLC", "INC", "CORP", "LTD", "LP ", "L.P.", "TRUST", "ASSOC", "HOMEOWNERS",
    "STATE OF", "CITY OF", "COUNTY OF", "DISTRICT", "MUNICIPALITY", "DEPT ",
    "ISD", "UTILITY", "AUTHORITY", "COMMISSION", "FEDERAL", "NATIONAL BANK",
    "MORTGAGE", "FINANCIAL", "INVESTMENT", "PROPERTIES", "REALTY", "HOLDINGS",
    "PARTNERS", "SERVICES", "MANAGEMENT", "SOLUTIONS", "ENTERPRISES",
    "N/A", "UNKNOWN", "PUBLIC", "ATTY GEN", "ATTY/GEN", "ROCKWALL COUNTY",
    "CITY OF ROCKWALL", "CITY OF HEATH", "CITY OF FATE", "CITY OF ROYSE",
    "CREDIT UNION", "LENDING", "LOAN SERVICING",
    "ANNUITY", "INSURANCE CO", "PENSION",
    "PNC BANK", "WELLS FARGO", "BANK OF AMERICA", "CHASE BANK",
    "IDAHO HOUSING", "US BANK", "NATIONSTAR", "LAKEVIEW LOAN",
    "UNITED WHOLESALE", "PENNYMAC", "FREEDOM MORTGAGE",
    "CHURCH", "MINISTRY", "FOUNDATION",
    "RESIDENTIAL LEASING", "AMERICAN HOMES",
)

DECEASED_TOKENS = re.compile(
    r"\b(DECEASED|DECD|DEC'D|ESTATE\s+OF|EST\s+OF|AKA|A\.K\.A\.)\b\.?",
    re.IGNORECASE,
)


def strip_deceased(name: str) -> str:
    """Remove deceased/AKA markers so heirship records match CAD owner names."""
    if not name:
        return name
    cleaned = DECEASED_TOKENS.sub("", name).strip()
    cleaned = re.sub(r"\s+", " ", cleaned)
    return cleaned


# ---------------------------------------------------------------------------
# Name handling (mirrors Kaufman/Hill)
# ---------------------------------------------------------------------------

def parse_date(raw: str) -> Optional[str]:
    for fmt in ("%m/%d/%Y", "%Y-%m-%d", "%m-%d-%Y", "%Y%m%d",
                "%m/%d/%Y %I:%M %p", "%m/%d/%Y %H:%M:%S"):
        try:
            return datetime.strptime(raw.strip(), fmt).strftime("%Y-%m-%d")
        except ValueError:
            continue
    return None


def strip_suffixes(tokens: list) -> list:
    return [t for t in tokens if t not in NAME_SUFFIXES]


def name_variants(full: str) -> list:
    full = re.sub(r"[^\w\s]", "", full.strip().upper())
    tokens = strip_suffixes(full.split())
    if not tokens:
        return [full]
    variants = set()
    variants.add(" ".join(tokens))
    if len(tokens) < 2:
        return list(variants)
    last  = tokens[0]
    first = tokens[1] if len(tokens) > 1 else ""
    mid   = tokens[2] if len(tokens) > 2 else ""
    variants.add(f"{last} {first} {mid}".strip())
    variants.add(f"{last}, {first} {mid}".strip())
    variants.add(f"{last} {first}")
    variants.add(f"{last}, {first}")
    variants.add(f"{first} {last}")
    if mid:
        variants.add(f"{first} {mid} {last}")
        variants.add(f"{first} {last}")
        if len(mid) == 1:
            variants.add(f"{last} {first}")
    return [v for v in variants if v]


def normalize_for_fuzzy(name: str) -> tuple:
    name = re.sub(r"[^\w\s]", "", name.strip().upper())
    tokens = strip_suffixes(name.split())
    filtered = [t for t in tokens if len(t) > 1]
    if len(filtered) >= 2:
        tokens = filtered
    if not tokens:
        return ("", set())
    return tokens[0], set(tokens[1:])


def is_entity(name: str) -> bool:
    n = name.strip().upper()
    if not n or n in ("N/A", "NA", "UNKNOWN", "PUBLIC", ""):
        return True
    tokens = [t for t in re.sub(r"[^\w\s]", "", n).split() if len(t) > 1]
    if len(tokens) < 2:
        return True
    return any(x in n for x in ENTITY_FILTERS)


# ---------------------------------------------------------------------------
# DBF reader (stdlib only)
# ---------------------------------------------------------------------------

def read_dbf_bytes(data: bytes):
    """Yield record dicts from DBF file bytes. dBase III layout, UTF-8 encoded."""
    header = data[:32]
    num_records = struct.unpack("<I", header[4:8])[0]
    header_len  = struct.unpack("<H", header[8:10])[0]
    record_len  = struct.unpack("<H", header[10:12])[0]

    fields = []
    pos = 32
    while True:
        descriptor = data[pos:pos+32]
        if descriptor[0:1] == b"\x0D":
            break
        name = descriptor[0:11].rstrip(b"\x00").decode("ascii", errors="replace")
        flen = descriptor[16]
        fields.append((name, flen))
        pos += 32

    pos = header_len
    for _ in range(num_records):
        rec = data[pos:pos+record_len]
        pos += record_len
        if not rec or rec[0:1] == b"\x1A":
            break
        if rec[0:1] == b"\x2A":
            continue
        offset = 1
        row = {}
        for (n, l) in fields:
            row[n] = rec[offset:offset+l].decode("utf-8", errors="replace").strip()
            offset += l
        yield row


def parse_num(val: str) -> float:
    try:
        return float(val) if val else 0.0
    except ValueError:
        return 0.0


# ---------------------------------------------------------------------------
# Build CAD parcel lookup from the local Rockwall ownership ZIP
# ---------------------------------------------------------------------------

def build_parcel_lookup() -> dict:
    lookup = {}
    log.info(f"Loading Rockwall CAD data from {CAD_ZIP_PATH} ...")
    try:
        if not Path(CAD_ZIP_PATH).exists():
            log.error(f"CAD file not found at {CAD_ZIP_PATH}")
            return lookup
        with open(CAD_ZIP_PATH, "rb") as f:
            zip_bytes = f.read()
        log.info(f"  Loaded {len(zip_bytes)/1_048_576:.1f} MB zip")

        zf = zipfile.ZipFile(io.BytesIO(zip_bytes))
        candidates = [n for n in zf.namelist() if n.endswith(CAD_DBF_NAME)]
        if not candidates:
            log.error(f"Could not find {CAD_DBF_NAME}. Files: {zf.namelist()[:20]}")
            return lookup
        log.info(f"  Parsing {candidates[0]} ...")
        dbf_bytes = zf.read(candidates[0])

        total = 0
        for row in read_dbf_bytes(dbf_bytes):
            # Filter: must have a structure (urban county - imprv_val > 0 only)
            if parse_num(row.get("ownerimpro", "0")) <= 0:
                continue

            owner_name = row.get("fileasname", "").strip().upper()
            owner_name = strip_deceased(owner_name)
            if not owner_name or is_entity(owner_name):
                continue

            # Property (situs) address - Rockwall uses streetnum/streetpre/streetnam/streetsuf
            s_num = row.get("streetnum", "").strip()
            s_pre = row.get("streetpre", "").strip()
            s_nam = row.get("streetnam", "").strip()
            s_suf = row.get("streetsuf", "").strip()
            prop_street = " ".join(p for p in (s_num, s_pre, s_nam, s_suf) if p)
            prop_city   = row.get("streetcity", "").strip()
            prop_state  = row.get("streetstat", "").strip() or "TX"
            prop_zip    = row.get("streetzip", "").strip()[:5]

            # Mailing address - Rockwall uses owneraddr/ownersuite/ownercity/etc.
            mail_addr  = row.get("owneraddr", "").strip()
            mail_suite = row.get("ownersuite", "").strip()
            if mail_suite:
                mail_addr = f"{mail_addr}, {mail_suite}".strip(", ")
            mail_city  = row.get("ownercity", "").strip()
            mail_state = row.get("ownerstate", "").strip() or "TX"
            mail_zip   = row.get("ownerzip", "").strip()[:5]

            if not prop_street and not mail_addr:
                continue

            parcel = {
                "prop_address": prop_street,
                "prop_city":    prop_city or "Rockwall",
                "prop_state":   prop_state,
                "prop_zip":     prop_zip,
                "mail_address": mail_addr,
                "mail_city":    mail_city,
                "mail_state":   mail_state,
                "mail_zip":     mail_zip,
            }

            # Co-owner splitting: Rockwall uses ' AND ' or '&' as separators.
            # 'SHUTTLEWORTH GARY AND MARTHA' -> ['SHUTTLEWORTH GARY', 'MARTHA']
            # 'SMITH JOHN & MARY' -> ['SMITH JOHN', 'MARY']
            parts = re.split(r'\s+AND\s+|\s*&\s*', owner_name)
            parts = [p.strip() for p in parts if p.strip()]
            if not parts:
                continue
            primary_surname = parts[0].split()[0] if parts[0].split() else ""
            full_parts = [parts[0]]
            for p in parts[1:]:
                tokens = p.split()
                if primary_surname and primary_surname not in tokens:
                    full_parts.append(f"{primary_surname} {p}")
                else:
                    full_parts.append(p)

            for part in full_parts:
                if part and not is_entity(part):
                    for variant in name_variants(part):
                        lookup[variant] = parcel

            # Also index secondname (sometimes a real co-owner, sometimes 'ATTN: TAX DEPT')
            sec = row.get("secondname", "").strip().upper()
            if sec and not is_entity(sec) and not sec.startswith("ATTN") and not sec.startswith("C/O"):
                sec = strip_deceased(sec)
                # Inherit primary surname if missing
                if primary_surname and primary_surname not in sec.split():
                    sec_full = f"{primary_surname} {sec}"
                else:
                    sec_full = sec
                for variant in name_variants(sec_full):
                    lookup[variant] = parcel

            total += 1
            if total % 10000 == 0:
                log.info(f"  Processed {total:,} parcels ...")

        log.info(f"Rockwall CAD lookup: {len(lookup):,} name variants from {total:,} parcels")
    except Exception:
        log.error(f"CAD lookup error:\n{traceback.format_exc()}")
    return lookup


# ---------------------------------------------------------------------------
# Tyler Tech clerk scraper
# ---------------------------------------------------------------------------

def parse_results_html(html: str, doc_type: str, cat: str, cat_label: str,
                       debug: bool = False) -> list:
    records = []
    try:
        soup = BeautifulSoup(html, "html.parser")
        result_list = soup.find("ul", class_="selfServiceSearchResultList")
        if not result_list:
            log.warning(f"  {doc_type}: no selfServiceSearchResultList found")
            return records

        items = result_list.find_all("li", recursive=False)
        log.info(f"  {doc_type}: {len(items)} result li items found")

        seen = set()
        for item in items:
            full_text = item.get_text(" ", strip=True)

            instrument = ""
            filed = ""
            grantor = ""
            grantee = ""
            legal   = ""

            columns = item.find_all("div", class_="searchResultFourColumn")
            for col in columns:
                ul = col.find("ul", class_="selfServiceSearchResultColumn")
                if not ul:
                    continue
                lis = ul.find_all("li")
                if not lis:
                    continue
                label = lis[0].get_text(strip=True).lower()
                val = ""
                if len(lis) > 1:
                    b = lis[1].find("b")
                    val = b.get_text(strip=True) if b else lis[1].get_text(strip=True)

                if "grantor" in label:
                    grantor = val
                elif "grantee" in label:
                    grantee = val
                elif "legal" in label:
                    legal = val
                elif ("document" in label and ("number" in label or "#" in label)) \
                     or label.strip() in ("doc #", "doc number", "instrument"):
                    instrument = val
                elif ("recording" in label or "rec date" in label or
                      "filed" in label or "file date" in label or "date" in label):
                    if not filed:
                        filed = val

            if not instrument:
                for pattern in (r"(\d{4}-\d+)",
                                r"\b(\d{8,})\b",
                                r"\b([A-Z]{1,3}\d{6,})\b"):
                    m = re.search(pattern, full_text)
                    if m:
                        instrument = m.group(1)
                        break

            if not filed:
                m2 = re.search(r"(\d{2}/\d{2}/\d{4})", full_text)
                if m2:
                    filed = m2.group(1)

            if not instrument and not (grantor or grantee):
                continue
            if not instrument:
                instrument = f"NOID-{abs(hash(full_text)) % 10**8}"

            if instrument in seen:
                continue
            seen.add(instrument)

            if debug:
                log.info(f"  PARSED: {instrument} | filed={filed} | grantor={grantor} | grantee={grantee}")

            records.append({
                "doc_num"  : instrument,
                "doc_type" : doc_type,
                "cat"      : cat,
                "cat_label": cat_label,
                "filed"    : parse_date(filed) or filed,
                "grantor"  : grantor,
                "grantee"  : grantee,
                "legal"    : legal,
                "amount"   : None,
                "clerk_url": BASE_URL,
                "_demo"    : False,
            })
    except Exception:
        log.error(f"  Parse error:\n{traceback.format_exc()}")
    return records


async def scrape_all(date_from: str, date_to: str) -> list:
    all_records = []

    def fmt_date(d):
        dt = datetime.strptime(d, "%m/%d/%Y")
        return f"{dt.month}/{dt.day}/{dt.year}"

    df = fmt_date(date_from)
    dt = fmt_date(date_to)

    ajax_headers = {
        "X-Requested-With": "XMLHttpRequest",
        "Ajaxrequest":       "true",
        "Accept":            "application/json, text/javascript, */*; q=0.01",
        "Referer":           BASE_URL,
    }

    async with httpx.AsyncClient(
        follow_redirects=True,
        headers={
            "User-Agent": "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
                          "AppleWebKit/537.36 (KHTML, like Gecko) "
                          "Chrome/120.0.0.0 Safari/537.36",
            "Referer": BASE_URL,
        },
        timeout=60
    ) as client:
        await client.get(BASE_URL)
        await client.post(
            BASE_HOST + "/web/user/disclaimer",
            data={"disclaimer": "accept", "submit": "Accept"}
        )
        r = await client.get(BASE_URL)
        log.info(f"  Search page loaded: {r.status_code} len={len(r.text)}")
        log.info(f"  Cookies: {list(client.cookies.keys())}")

        for doc_type, (cat, cat_label, holder_input) in DOC_TYPES.items():
            try:
                form_data = {
                    "field_BothNamesID-containsInput":               "Contains Any",
                    "field_BothNamesID":                             "",
                    "field_GrantorID-containsInput":                 "Contains Any",
                    "field_GrantorID":                               "",
                    "field_GranteeID-containsInput":                 "Contains Any",
                    "field_GranteeID":                               "",
                    # Rockwall uses 'RecordingDateID' (not 'RecDateID' like Kaufman/Hill)
                    "field_RecordingDateID_DOT_StartDate":           df,
                    "field_RecordingDateID_DOT_EndDate":             dt,
                    # Rockwall uses 'DocumentNumberID' (not 'DocNumID')
                    "field_DocumentNumberID":                        "",
                    # Rockwall uses 'BookPageID' (not 'BookVolPageID')
                    "field_BookPageID_DOT_Book-containsInput":       "Contains Any",
                    "field_BookPageID_DOT_Book":                     "",
                    "field_BookPageID_DOT_Volume":                   "",
                    "field_BookPageID_DOT_Page":                     "",
                    "field_selfservice_documentTypes-holderInput":   holder_input,
                    "field_selfservice_documentTypes-holderValue":   doc_type,
                    "field_selfservice_documentTypes-containsInput": "Contains Any",
                    "field_selfservice_documentTypes":               "",
                }

                post_resp = await client.post(
                    BASE_HOST + f"/web/searchPost/{SEARCH_ID}",
                    data=form_data,
                    headers={
                        **ajax_headers,
                        "Content-Type": "application/x-www-form-urlencoded; charset=UTF-8",
                    }
                )
                log.info(f"  {doc_type} POST: {post_resp.status_code}")

                try:
                    post_json   = post_resp.json()
                    total_pages = post_json.get("totalPages", 0)
                    log.info(f"  {doc_type} totalPages={total_pages}")
                except Exception:
                    log.warning(f"  {doc_type} POST not JSON")
                    total_pages = 0

                if total_pages == 0:
                    continue

                for pg in range(1, total_pages + 1):
                    ts = int(datetime.now().timestamp() * 1000)
                    get_resp = await client.get(
                        BASE_HOST + f"/web/searchResults/{SEARCH_ID}",
                        params={"page": str(pg), "_": str(ts)},
                        headers=ajax_headers
                    )
                    log.info(f"  {doc_type} GET p{pg}: {get_resp.status_code} len={len(get_resp.text)}")

                    debug = (doc_type == "LIS PENDENS" and pg == 1)
                    if get_resp.status_code == 200 and len(get_resp.text) > 500:
                        recs = parse_results_html(
                            get_resp.text, doc_type, cat, cat_label, debug=debug
                        )
                        log.info(f"  {doc_type} p{pg}: {len(recs)} records parsed")
                        all_records.extend(recs)

            except Exception as e:
                log.warning(f"  {doc_type} failed: {e}\n{traceback.format_exc()}")

    log.info(f"  Total scraped: {len(all_records)}")
    return all_records


# ---------------------------------------------------------------------------
# Demo data fallback
# ---------------------------------------------------------------------------

def generate_demo_records(date_from: str, date_to: str) -> list:
    samples = [
        ("LIS PENDENS",        "pre_foreclosure", "Lis Pendens",
         "SMITH ROBERT",   "ROCKET MORTGAGE",    0),
        ("FEDERAL TAX LIEN",   "lien",            "Federal Tax Lien",
         "WILLIAMS DAVID", "IRS",            45200),
        ("STATE TAX LIEN",     "lien",            "State Tax Lien",
         "HENDERSON BOB",  "STATE OF TX",     9800),
        ("JUDGMENT",           "judgment",        "Judgment",
         "JOHNSON PAT",    "CITIBANK",       18700),
        ("MECHANICS LIEN",     "lien",            "Mechanics Lien",
         "BROWN MICHAEL",  "ACME CONTR",     22000),
        ("LIEN",               "lien",            "Lien",
         "TAYLOR JAMES",   "GENERIC LIEN",    7500),
        ("CHILD SUPPORT LIEN", "lien",            "Child Support Lien",
         "MARTINEZ LUIS",  "TX OAG",          5500),
        ("HEIRSHIP AFFIDAVIT", "probate",         "Heirship Affidavit",
         "GARCIA CARLOS",  "GARCIA MARIA",       0),
        ("PROBATE",            "probate",         "Probate",
         "DAVIS JAMES",    "ROCKWALL PROB",      0),
        ("DIVORCE DECREE",     "other",           "Divorce Decree",
         "JONES MARK",     "JONES SUSAN",        0),
    ]
    base = datetime.strptime(date_from, "%m/%d/%Y")
    recs = []
    for i, (code, cat, cat_label, grantor, grantee, amt) in enumerate(samples):
        filed_dt = base + timedelta(days=i % LOOKBACK_DAYS)
        recs.append({
            "doc_num":   f"2026-DEMO-{i+1:04d}",
            "doc_type":  code,
            "cat":       cat,
            "cat_label": cat_label,
            "filed":     filed_dt.strftime("%Y-%m-%d"),
            "grantor":   grantor,
            "grantee":   grantee,
            "legal":     "DEMO RECORD",
            "amount":    float(amt) if amt else None,
            "clerk_url": BASE_URL,
            "_demo":     True,
        })
    return recs


# ---------------------------------------------------------------------------
# Match clerk records to CAD parcels
# ---------------------------------------------------------------------------

def _try_match(name: str, lookup: dict, fuzzy_index: list) -> Optional[dict]:
    """Try exact variant lookup, then fall back to fuzzy match."""
    if not name:
        return None
    # Strip deceased/AKA tokens BEFORE the entity check, so 'ESTATE OF SMITH' isn't
    # rejected as an entity by the 'STATE OF' substring filter.
    cleaned = strip_deceased(name)
    if is_entity(cleaned):
        return None
    for variant in name_variants(cleaned):
        if variant in lookup:
            return lookup[variant]
    # Fuzzy fallback
    o_last, o_firsts = normalize_for_fuzzy(cleaned)
    if not o_last or not o_firsts:
        return None
    for c_last, c_firsts, candidate in fuzzy_index:
        if c_last != o_last or not c_firsts:
            continue
        if o_firsts & c_firsts:
            return candidate
        o_str = " ".join(sorted(o_firsts))
        c_str = " ".join(sorted(c_firsts))
        if o_str and c_str and SequenceMatcher(None, o_str, c_str).ratio() >= 0.85:
            return candidate
    return None


def enrich_with_parcel(records: list, lookup: dict) -> list:
    fuzzy_index = []
    seen = set()
    for variant, parcel in lookup.items():
        last, firsts = normalize_for_fuzzy(variant)
        key = (last, frozenset(firsts))
        if last and key not in seen:
            seen.add(key)
            fuzzy_index.append((last, firsts, parcel))

    matched = 0
    for rec in records:
        dtype = rec.get("doc_type", "")

        # For divorce decrees, try BOTH grantor and grantee
        if dtype in EITHER_SIDE_OWNER:
            candidates = [
                rec.get("grantor", "").upper().strip(),
                rec.get("grantee", "").upper().strip(),
            ]
        elif dtype in GRANTEE_IS_OWNER:
            candidates = [rec.get("grantee", "").upper().strip()]
        else:
            candidates = [rec.get("grantor", "").upper().strip()]

        parcel = None
        matched_name = None
        for cand in candidates:
            if not cand:
                continue
            parcel = _try_match(cand, lookup, fuzzy_index)
            if parcel:
                matched_name = cand
                break

        if parcel:
            rec.update(parcel)
            # For divorce records, store which side matched
            if dtype in EITHER_SIDE_OWNER and matched_name:
                rec["matched_owner"] = matched_name
            matched += 1
        else:
            owners_for_log = " | ".join(c for c in candidates if c)
            if owners_for_log:
                log.info(f"  NO MATCH: {owners_for_log}")
            rec.setdefault("prop_address", "")
            rec.setdefault("prop_city",    "")
            rec.setdefault("prop_state",   "TX")
            rec.setdefault("prop_zip",     "")
            rec.setdefault("mail_address", "")
            rec.setdefault("mail_city",    "")
            rec.setdefault("mail_state",   "TX")
            rec.setdefault("mail_zip",     "")
    log.info(f"Parcel enrichment: {matched}/{len(records)} records matched")
    return records


# ---------------------------------------------------------------------------
# Score and flag each record
# ---------------------------------------------------------------------------

def score_record(rec: dict) -> tuple:
    score = 30
    flags = []
    dtype  = rec.get("doc_type", "")
    amount = rec.get("amount") or 0
    if dtype == "LIS PENDENS":                              flags.append("Lis pendens")
    if dtype in ("FEDERAL TAX LIEN", "STATE TAX LIEN"):     flags.append("Tax lien")
    if dtype == "JUDGMENT":                                 flags.append("Judgment lien")
    if dtype == "MECHANICS LIEN":                           flags.append("Mechanic lien")
    if dtype == "LIEN":                                     flags.append("Lien")
    if dtype == "CHILD SUPPORT LIEN":                       flags.append("Child support lien")
    if dtype == "HEIRSHIP AFFIDAVIT":                       flags.append("Probate / estate")
    if dtype == "PROBATE":                                  flags.append("Probate / estate")
    if dtype == "DIVORCE DECREE":                           flags.append("Divorce")
    try:
        filed = datetime.strptime(rec.get("filed", ""), "%Y-%m-%d")
        if (datetime.today() - filed).days <= 14:
            flags.append("New this week")
    except Exception:
        pass
    has_addr = bool(rec.get("prop_address") or rec.get("mail_address"))
    score += 10 * len(flags)
    if "Lis pendens" in flags:      score += 20
    if "Probate / estate" in flags: score += 10
    if "Tax lien" in flags:         score += 10
    if "Divorce" in flags:          score += 5
    if amount and amount > 100_000: score += 15
    elif amount and amount > 50_000: score += 10
    if "New this week" in flags:    score += 5
    if has_addr:                    score += 5
    return min(score, 100), flags


# ---------------------------------------------------------------------------
# Output assembly
# ---------------------------------------------------------------------------

def build_output(raw_records: list, date_from: str, date_to: str) -> dict:
    seen_docs   = set()
    out_records = []
    for raw in raw_records:
        try:
            doc_num = raw.get("doc_num", "")
            if doc_num and doc_num in seen_docs:
                continue
            if doc_num:
                seen_docs.add(doc_num)
            dtype = raw.get("doc_type", "")

            # Pick which side is the owner for output display
            if dtype in EITHER_SIDE_OWNER:
                # Use whichever side actually matched the CAD; fall back to grantor
                owner = raw.get("matched_owner") or raw.get("grantor", "")
                grantee = raw.get("grantee", "") if owner == raw.get("grantor", "") else raw.get("grantor", "")
            elif dtype in GRANTEE_IS_OWNER:
                owner   = raw.get("grantee", "")
                grantee = raw.get("grantor", "")
            else:
                owner   = raw.get("grantor", "")
                grantee = raw.get("grantee", "")
            owner = strip_deceased(owner)
            if not owner:
                owner = f"UNKNOWN ({doc_num})"
            score, flags = score_record({**raw, "owner": owner})
            out_records.append({
                "doc_num":      doc_num,
                "doc_type":     dtype,
                "filed":        raw.get("filed", ""),
                "cat":          raw.get("cat", "other"),
                "cat_label":    raw.get("cat_label", ""),
                "owner":        owner,
                "grantee":      grantee,
                "amount":       raw.get("amount"),
                "legal":        raw.get("legal", ""),
                "prop_address": raw.get("prop_address", ""),
                "prop_city":    raw.get("prop_city", ""),
                "prop_state":   raw.get("prop_state", "TX"),
                "prop_zip":     raw.get("prop_zip", ""),
                "mail_address": raw.get("mail_address", ""),
                "mail_city":    raw.get("mail_city", ""),
                "mail_state":   raw.get("mail_state", "TX"),
                "mail_zip":     raw.get("mail_zip", ""),
                "clerk_url":    raw.get("clerk_url", ""),
                "flags":        flags,
                "score":        score,
                "_demo":        raw.get("_demo", False),
            })
        except Exception:
            log.warning(f"Skipping: {traceback.format_exc()}")
    out_records = [r for r in out_records if not is_entity(r.get("owner", ""))]
    out_records = [r for r in out_records if not any(
        x in (r.get("owner", "")).upper() for x in ENTITY_FILTERS
    )]
    out_records = [r for r in out_records if r.get("prop_address") or r.get("mail_address") or r.get("_demo")]
    out_records.sort(key=lambda r: (-r["score"], r.get("filed", "") or ""))
    with_address = sum(1 for r in out_records if r["prop_address"] or r["mail_address"])
    return {
        "fetched_at":   datetime.utcnow().isoformat() + "Z",
        "source":       "Rockwall County TX – Tyler Technologies",
        "date_range":   {"from": date_from, "to": date_to},
        "total":        len(out_records),
        "with_address": with_address,
        "records":      out_records,
    }


def save_output(data: dict):
    for path in ["dashboard/records.json", "data/records.json"]:
        p = Path(path)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps(data, indent=2))
        log.info(f"Saved {data['total']} records → {path}")


def export_ghl_csv(data: dict):
    fieldnames = [
        "First Name", "Last Name", "Mailing Address", "Mailing City",
        "Mailing State", "Mailing Zip", "Property Address", "Property City",
        "Property State", "Property Zip", "Lead Type", "Document Type",
        "Date Filed", "Document Number", "Amount/Debt Owed", "Seller Score",
        "Motivated Seller Flags", "Source", "Public Records URL",
    ]
    buf = io.StringIO()
    writer = csv.DictWriter(buf, fieldnames=fieldnames)
    writer.writeheader()
    for r in data["records"]:
        parts = (r.get("owner", "")).split()
        writer.writerow({
            "First Name":             parts[0] if parts else "",
            "Last Name":              " ".join(parts[1:]) if len(parts) > 1 else "",
            "Mailing Address":        r.get("mail_address", ""),
            "Mailing City":           r.get("mail_city", ""),
            "Mailing State":          r.get("mail_state", "TX"),
            "Mailing Zip":            r.get("mail_zip", ""),
            "Property Address":       r.get("prop_address", ""),
            "Property City":          r.get("prop_city", ""),
            "Property State":         r.get("prop_state", "TX"),
            "Property Zip":           r.get("prop_zip", ""),
            "Lead Type":              r.get("cat_label", ""),
            "Document Type":          r.get("doc_type", ""),
            "Date Filed":             r.get("filed", ""),
            "Document Number":        r.get("doc_num", ""),
            "Amount/Debt Owed":       str(r.get("amount", "") or ""),
            "Seller Score":           str(r.get("score", "")),
            "Motivated Seller Flags": "|".join(r.get("flags", [])),
            "Source":                 "Rockwall County TX",
            "Public Records URL":     r.get("clerk_url", ""),
        })
    Path("data/ghl_export.csv").write_text(buf.getvalue())
    log.info("GHL CSV saved")


async def main():
    today     = datetime.today()
    start     = today - timedelta(days=LOOKBACK_DAYS)
    date_from = start.strftime("%m/%d/%Y")
    date_to   = today.strftime("%m/%d/%Y")

    log.info("=== Rockwall County TX Lead Scraper ===")
    log.info(f"Date range: {date_from} → {date_to}")

    log.info("Building parcel lookup ...")
    parcel_lookup = build_parcel_lookup()
    log.info(f"  {len(parcel_lookup):,} name variants indexed")

    log.info("Scraping clerk records ...")
    raw_records = await scrape_all(date_from, date_to)
    log.info(f"Total raw records: {len(raw_records)}")

    if not raw_records:
        log.warning("No live records – using demo data")
        raw_records = generate_demo_records(date_from, date_to)

    raw_records = enrich_with_parcel(raw_records, parcel_lookup)
    data = build_output(raw_records, date_from, date_to)
    save_output(data)
    export_ghl_csv(data)
    log.info(f"Done. {data['total']} leads | {data['with_address']} with address")


if __name__ == "__main__":
    asyncio.run(main())
