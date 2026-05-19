#!/usr/bin/env python3
"""Standalone TNM query debugger for TrailPrint3D."""
import argparse, json, logging, os, sys, time
from typing import Any, Dict
from urllib.parse import urlencode
from urllib.request import Request, urlopen
from urllib.error import HTTPError, URLError

DEFAULT_BASE_URL = "https://epqs.nationalmap.gov/v1/json"
DEFAULT_LAT = 39.7392
DEFAULT_LON = -104.9903
DEFAULT_UNITS = "Meters"
DEFAULT_WKID = 4326
DEFAULT_TIMEOUT_SECONDS = 12.0

def configure_logging(verbose: bool) -> logging.Logger:
    logger = logging.getLogger("tnm_query_debug")
    logger.setLevel(logging.DEBUG if verbose else logging.INFO)
    h = logging.StreamHandler(sys.stdout)
    h.setFormatter(logging.Formatter("%(asctime)s | %(levelname)s | %(message)s"))
    h.setLevel(logging.DEBUG if verbose else logging.INFO)
    logger.handlers.clear(); logger.addHandler(h)
    return logger

def get_usgs_auth_headers(logger: logging.Logger) -> Dict[str, str]:
    token = os.environ.get("USGS_API_TOKEN", "").strip()
    if token:
        logger.debug("USGS_API_TOKEN detected; Authorization header will be sent")
        return {"Authorization": f"Bearer {token}"}
    logger.debug("USGS_API_TOKEN not set; no Authorization header")
    return {}

def build_url(base_url: str, lon: float, lat: float, units: str, wkid: int, logger: logging.Logger) -> str:
    q = {"x": lon, "y": lat, "units": units, "wkid": wkid}
    url = f"{base_url}?{urlencode(q)}"
    logger.debug("Query params: %s", q)
    logger.debug("Full URL: %s", url)
    return url

def extract_elevation(payload: Dict[str, Any], logger: logging.Logger) -> Any:
    logger.debug("Trying payload['value']")
    v = payload.get("value")
    if v is not None: return v
    logger.debug("Trying nested fallback payload['USGS_Elevation_Point_Query_Service']['Elevation_Query']['Elevation']")
    v = payload.get("USGS_Elevation_Point_Query_Service",{}).get("Elevation_Query",{}).get("Elevation")
    return v

def run_once(args: argparse.Namespace, logger: logging.Logger) -> int:
    headers = get_usgs_auth_headers(logger)
    url = build_url(args.base_url, args.lon, args.lat, args.units, args.wkid, logger)
    logger.info("Request | GET %s | timeout=%.2fs", url, args.timeout)
    logger.debug("Headers: %s", headers if headers else "{}")
    req = Request(url, method="GET")
    for k,v in headers.items(): req.add_header(k,v)
    start=time.perf_counter()
    try:
        with urlopen(req, timeout=args.timeout) as resp:
            elapsed=time.perf_counter()-start
            status=getattr(resp,'status',None)
            body=resp.read().decode('utf-8','replace')
            logger.info("Response | status=%s | elapsed=%.3fs", status, elapsed)
            logger.debug("Response headers: %s", dict(resp.headers.items()))
            logger.debug("Response body (first 1000 chars): %s", body[:1000])
    except HTTPError as e:
        body=e.read().decode('utf-8','replace')
        logger.error("HTTPError | code=%s | reason=%s", e.code, e.reason)
        logger.debug("HTTPError body: %s", body[:1000])
        return 1
    except URLError as e:
        logger.error("URLError | reason=%s", e.reason)
        return 1
    except Exception as e:
        logger.error("Unexpected error: %s", e)
        return 1
    try:
        payload=json.loads(body)
        logger.debug("Parsed JSON: %s", json.dumps(payload, indent=2, ensure_ascii=False))
    except Exception as e:
        logger.error("JSON parse failed: %s", e)
        return 2
    value=extract_elevation(payload, logger)
    if value is None:
        logger.error("No elevation value found in payload")
        return 3
    logger.info("SUCCESS | elevation=%s", value)
    return 0

def build_parser():
    p=argparse.ArgumentParser(description='Debug USGS TNM elevation point query')
    p.add_argument('--base-url',default=DEFAULT_BASE_URL)
    p.add_argument('--lat',type=float,default=DEFAULT_LAT)
    p.add_argument('--lon',type=float,default=DEFAULT_LON)
    p.add_argument('--units',default=DEFAULT_UNITS)
    p.add_argument('--wkid',type=int,default=DEFAULT_WKID)
    p.add_argument('--timeout',type=float,default=DEFAULT_TIMEOUT_SECONDS)
    p.add_argument('--quiet',action='store_true')
    return p

if __name__=='__main__':
    args=build_parser().parse_args()
    logger=configure_logging(verbose=not args.quiet)
    raise SystemExit(run_once(args, logger))
