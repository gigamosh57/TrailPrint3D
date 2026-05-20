#!/usr/bin/env python3
"""Standalone USGS elevation query debugger for TrailPrint3D.

Supports:
- EPQS point query (legacy script behavior)
- 3DEP ImageServer exportImage metadata requests for bbox coverage testing
"""
import argparse
import hashlib
import json
import logging
import os
import sys
import time
from typing import Any, Dict
from urllib.error import HTTPError, URLError
from urllib.parse import urlencode
from urllib.request import Request, urlopen

DEFAULT_EPQS_BASE_URL = "https://epqs.nationalmap.gov/v1/json"
DEFAULT_3DEP_EXPORT_URL = "https://elevation.nationalmap.gov/arcgis/rest/services/3DEPElevation/ImageServer/exportImage"
DEFAULT_LAT = 39.7392
DEFAULT_LON = -104.9903
DEFAULT_UNITS = "Meters"
DEFAULT_WKID = 4326
DEFAULT_TIMEOUT_SECONDS = 12.0

# Small bbox around downtown Denver for default 3DEP coverage test.
DEFAULT_MIN_LON = -105.01
DEFAULT_MIN_LAT = 39.72
DEFAULT_MAX_LON = -104.97
DEFAULT_MAX_LAT = 39.76
DEFAULT_WIDTH = 512
DEFAULT_HEIGHT = 512


def build_3dep_cache_paths(args: argparse.Namespace) -> Dict[str, str]:
    cache_key = hashlib.sha1(
        f"{args.min_lon},{args.min_lat},{args.max_lon},{args.max_lat}|{args.width}x{args.height}|{args.wkid}|{args.image_format}|{args.pixel_type}".encode("utf-8")
    ).hexdigest()
    root = os.path.abspath(os.path.expanduser(args.cache_dir))
    os.makedirs(root, exist_ok=True)
    return {
        "metadata": os.path.join(root, f"{cache_key}.json"),
        "raster": os.path.join(root, f"{cache_key}.tif"),
    }


def write_3dep_cache(args: argparse.Namespace, metadata: Dict[str, Any], raster_body: bytes, logger: logging.Logger) -> None:
    paths = build_3dep_cache_paths(args)
    with open(paths["metadata"], "w", encoding="utf-8") as f_meta:
        json.dump(metadata, f_meta, indent=2)
    with open(paths["raster"], "wb") as f_raster:
        f_raster.write(raster_body)
    logger.info("3DEP cache saved | metadata=%s | raster=%s", paths["metadata"], paths["raster"])


def configure_logging(verbose: bool) -> logging.Logger:
    logger = logging.getLogger("tnm_query_debug")
    logger.setLevel(logging.DEBUG if verbose else logging.INFO)
    handler = logging.StreamHandler(sys.stdout)
    handler.setFormatter(logging.Formatter("%(asctime)s | %(levelname)s | %(message)s"))
    handler.setLevel(logging.DEBUG if verbose else logging.INFO)
    logger.handlers.clear()
    logger.addHandler(handler)
    return logger


def get_usgs_auth_headers(logger: logging.Logger) -> Dict[str, str]:
    token = os.environ.get("USGS_API_TOKEN", "").strip()
    if token:
        logger.debug("USGS_API_TOKEN detected; Authorization header will be sent")
        return {"Authorization": f"Bearer {token}"}
    logger.debug("USGS_API_TOKEN not set; no Authorization header")
    return {}


def build_epqs_url(base_url: str, lon: float, lat: float, units: str, wkid: int, logger: logging.Logger) -> str:
    query = {"x": lon, "y": lat, "units": units, "wkid": wkid}
    url = f"{base_url}?{urlencode(query)}"
    logger.debug("EPQS query params: %s", query)
    logger.debug("EPQS full URL: %s", url)
    return url


def build_3dep_export_url(base_url: str, args: argparse.Namespace, logger: logging.Logger) -> str:
    bbox = f"{args.min_lon},{args.min_lat},{args.max_lon},{args.max_lat}"
    query = {
        "bbox": bbox,
        "bboxSR": args.wkid,
        "imageSR": args.wkid,
        "size": f"{args.width},{args.height}",
        "format": args.image_format,
        "pixelType": args.pixel_type,
        "f": args.response_format,
    }
    url = f"{base_url}?{urlencode(query)}"
    logger.debug("3DEP exportImage query params: %s", query)
    logger.debug("3DEP exportImage full URL: %s", url)
    return url


def extract_epqs_elevation(payload: Dict[str, Any], logger: logging.Logger) -> Any:
    logger.debug("Trying payload['value']")
    value = payload.get("value")
    if value is not None:
        return value

    logger.debug("Trying nested fallback payload['USGS_Elevation_Point_Query_Service']['Elevation_Query']['Elevation']")
    return payload.get("USGS_Elevation_Point_Query_Service", {}).get("Elevation_Query", {}).get("Elevation")


def run_request(url: str, timeout: float, headers: Dict[str, str], logger: logging.Logger, method: str = "GET") -> Dict[str, Any]:
    logger.info("Request | %s %s | timeout=%.2fs", method, url, timeout)
    logger.debug("Headers: %s", headers if headers else "{}")

    req = Request(url, method=method)
    for key, value in headers.items():
        req.add_header(key, value)

    start = time.perf_counter()
    try:
        with urlopen(req, timeout=timeout) as response:
            elapsed = time.perf_counter() - start
            status = getattr(response, "status", None)
            body = response.read()
            response_headers = dict(response.headers.items())
            logger.info("Response | status=%s | elapsed=%.3fs", status, elapsed)
            logger.debug("Response headers: %s", response_headers)
            logger.debug("Response body bytes=%s", len(body))
            if method == "GET" and "json" in response_headers.get("Content-Type", "").lower():
                logger.debug("Response body (first 2000 chars): %s", body.decode("utf-8", "replace")[:2000])
            return {
                "status": status,
                "elapsed": elapsed,
                "headers": response_headers,
                "body": body,
            }
    except HTTPError as exc:
        body = exc.read().decode("utf-8", "replace")
        logger.error("HTTPError | code=%s | reason=%s", exc.code, exc.reason)
        logger.debug("HTTPError body: %s", body[:2000])
        raise
    except URLError as exc:
        logger.error("URLError | reason=%s", exc.reason)
        raise


def run_epqs(args: argparse.Namespace, logger: logging.Logger) -> int:
    headers = get_usgs_auth_headers(logger)
    url = build_epqs_url(args.base_url, args.lon, args.lat, args.units, args.wkid, logger)
    try:
        result = run_request(url, args.timeout, headers, logger)
    except Exception:
        return 1

    try:
        payload = json.loads(result["body"].decode("utf-8", "replace"))
        logger.debug("Parsed JSON: %s", json.dumps(payload, indent=2, ensure_ascii=False))
    except Exception as exc:
        logger.error("JSON parse failed: %s", exc)
        return 2

    value = extract_epqs_elevation(payload, logger)
    if value is None:
        logger.error("No elevation value found in payload")
        return 3

    try:
        value = float(value)
    except Exception:
        logger.warning("Elevation was non-numeric; leaving as raw value: %s", value)

    logger.info("SUCCESS | provider=epqs | elevation=%s", value)
    return 0


def run_3dep(args: argparse.Namespace, logger: logging.Logger) -> int:
    headers = get_usgs_auth_headers(logger)
    url = build_3dep_export_url(args.base_url, args, logger)
    logger.info(
        "3DEP request context | bbox=(%s,%s,%s,%s) | size=%sx%s | format=%s | pixelType=%s | f=%s",
        args.min_lon,
        args.min_lat,
        args.max_lon,
        args.max_lat,
        args.width,
        args.height,
        args.image_format,
        args.pixel_type,
        args.response_format,
    )

    try:
        result = run_request(url, args.timeout, headers, logger)
    except Exception:
        return 1

    content_type = result["headers"].get("Content-Type", "")
    logger.info("3DEP content-type detected: %s", content_type)

    # For f=json, parse details and print the downloadable URL.
    if args.response_format.lower() == "json":
        try:
            payload = json.loads(result["body"].decode("utf-8", "replace"))
            logger.debug("Parsed JSON: %s", json.dumps(payload, indent=2, ensure_ascii=False))
        except Exception as exc:
            logger.error("JSON parse failed: %s", exc)
            return 2

        href = payload.get("href")
        if href:
            logger.info("SUCCESS | provider=3dep | export href=%s", href)
            raster_result = None
            try:
                raster_result = run_request(href, args.timeout, headers, logger)
            except Exception as exc:
                logger.warning(
                    "3DEP raster fetch from export href failed; attempting direct image fallback | href=%s | error=%s",
                    href,
                    exc,
                )
                image_args = argparse.Namespace(**vars(args))
                image_args.response_format = "image"
                fallback_image_url = build_3dep_export_url(args.base_url, image_args, logger)
                try:
                    raster_result = run_request(fallback_image_url, args.timeout, headers, logger)
                except Exception as fallback_exc:
                    logger.error(
                        "3DEP raster fetch failed after metadata success | href=%s | fallback_url=%s | error=%s",
                        href,
                        fallback_image_url,
                        fallback_exc,
                    )
                    return 4

            raster_content_type = raster_result["headers"].get("Content-Type", "").lower()
            if raster_result["status"] != 200:
                logger.error(
                    "3DEP raster fetch failed after metadata success | expected status=200 | got=%s",
                    raster_result["status"],
                )
                return 4
            if not any(token in raster_content_type for token in ("image/tiff", "image/tif", "application/octet-stream")):
                logger.error(
                    "3DEP raster fetch failed after metadata success | unexpected content-type=%s",
                    raster_result["headers"].get("Content-Type", ""),
                )
                return 4
            logger.info(
                "SUCCESS | provider=3dep | metadata ok + raster fetch ok | href=%s | content-type=%s | bytes=%s",
                href,
                raster_result["headers"].get("Content-Type", ""),
                len(raster_result["body"]),
            )
            write_3dep_cache(args, payload, raster_result["body"], logger)
        else:
            logger.warning("3DEP JSON response did not include href; payload keys=%s", sorted(payload.keys()))
            logger.info("SUCCESS | provider=3dep | json response received")
        return 0

    # For f=image requests, body is binary and not JSON; reaching status=200 is a valid connectivity success.
    logger.info("SUCCESS | provider=3dep | image response received | bytes=%s", len(result["body"]))
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Debug USGS EPQS/3DEP elevation queries")
    parser.add_argument("--provider", choices=["epqs", "3dep"], default="3dep")

    # Shared
    parser.add_argument("--timeout", type=float, default=DEFAULT_TIMEOUT_SECONDS)
    parser.add_argument("--wkid", type=int, default=DEFAULT_WKID)
    parser.add_argument("--quiet", action="store_true")
    parser.add_argument("--cache-dir", default=".cache/tnm_3dep")

    # EPQS point params
    parser.add_argument("--lat", type=float, default=DEFAULT_LAT)
    parser.add_argument("--lon", type=float, default=DEFAULT_LON)
    parser.add_argument("--units", default=DEFAULT_UNITS)

    # 3DEP bbox params
    parser.add_argument("--min-lon", type=float, default=DEFAULT_MIN_LON)
    parser.add_argument("--min-lat", type=float, default=DEFAULT_MIN_LAT)
    parser.add_argument("--max-lon", type=float, default=DEFAULT_MAX_LON)
    parser.add_argument("--max-lat", type=float, default=DEFAULT_MAX_LAT)
    parser.add_argument("--width", type=int, default=DEFAULT_WIDTH)
    parser.add_argument("--height", type=int, default=DEFAULT_HEIGHT)
    parser.add_argument("--image-format", default="tiff")
    parser.add_argument("--pixel-type", default="F32")
    parser.add_argument("--response-format", choices=["json", "image"], default="json")

    # Optional base-url override, provider dependent
    parser.add_argument("--base-url", default=None)

    return parser


if __name__ == "__main__":
    arguments = build_parser().parse_args()
    log = configure_logging(verbose=not arguments.quiet)

    if arguments.provider == "epqs":
        arguments.base_url = arguments.base_url or DEFAULT_EPQS_BASE_URL
        raise SystemExit(run_epqs(arguments, log))

    arguments.base_url = arguments.base_url or DEFAULT_3DEP_EXPORT_URL
    raise SystemExit(run_3dep(arguments, log))
