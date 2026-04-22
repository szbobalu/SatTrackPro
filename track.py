#!/usr/bin/env python3
"""
track.py - Weather Satellite Pass Predictor

//dev by szbobalu/0xdev
========================================================
Tracks NOAA APT and METEOR LRPT weather-imaging satellites.
All orbital data is fetched from Celestrak (free, no API key required).

Location is detected automatically if --lat/--lon are not provided:
  1. gpsd          (requires: pip install gps; gpsd running)
  2. NMEA serial   (direct GPS receiver on /dev/ttyUSB0 etc.; pip install pyserial)
  3. termux-location (Android/Termux with Termux:API installed)
  4. IP geolocation  (ip-api.com → ipwho.is → ipinfo.io; city-level, ~1–50 km)

Satellite transmission modes:
  APT  = Automatic Picture Transmission   ~137 MHz analog
         Decode with: WXtoImg, apt-decoder, SatDump
  LRPT = Low Rate Picture Transmission    ~137 MHz digital QPSK
         Decode with: SatDump, METEOR Demodulator plugin for SDR#

Install dependencies:
  pip install requests ephem
  pip install gps          # optional: gpsd client
  pip install pyserial     # optional: direct NMEA serial GPS

Usage:
  python wx_pass_tracker.py                        # full auto-detect
  python wx_pass_tracker.py --gps                  # force GPS, skip IP fallback
  python wx_pass_tracker.py --lat 47.5 --lon 19.0  # manual override
  python wx_pass_tracker.py --min-elev 20 --hours 48
  python wx_pass_tracker.py --local-time --no-color
"""

import argparse
import dataclasses
import json
import math
import os
import subprocess
import sys
import time
from datetime import datetime, timezone
from itertools import groupby
from typing import Optional

import ephem
import requests

# ─── Satellite Registry ───────────────────────────────────────────────────────
# Only satellites with active weather-imaging transmitters receivable with a
# basic SDR dongle + dipole/V-dipole antenna around 137 MHz.
#
# Sources for status verification (all free):
#   https://www.ospo.noaa.gov/Operations/POES/status.html  (NOAA ops status)
#   https://www.sigidwiki.com/wiki/Automatic_Picture_Transmission_(APT)
#   https://lrpt.su  (METEOR-M community tracker)

ACTIVE_WX_SATS = {
    "NOAA 15": {
        "norad":  25338,
        "freq":   "137.620 MHz",
        "mode":   "APT",
        "status": "Operational · mild attitude wobble, still decodable",
    },
    "NOAA 18": {
        "norad":  28654,
        "freq":   "137.9125 MHz",
        "mode":   "APT",
        "status": "Operational",
    },
    "NOAA 19": {
        "norad":  33591,
        "freq":   "137.1000 MHz",
        "mode":   "APT",
        "status": "Operational · strongest APT signal",
    },
    "METEOR-M 2-3": {
        "norad":  57166,
        "freq":   "137.900 MHz",
        "mode":   "LRPT",
        "status": "Operational · requires LRPT/QPSK decoder",
    },
}

# Celestrak TLE sources — the "weather" group covers NOAA POES + METEOR
TLE_URLS = [
    "https://celestrak.org/NORAD/elements/gp.php?GROUP=weather&FORMAT=tle",
    # Fallback: individual name lookups
    "https://celestrak.org/NORAD/elements/gp.php?CATNR=25338&FORMAT=tle",
    "https://celestrak.org/NORAD/elements/gp.php?CATNR=28654&FORMAT=tle",
    "https://celestrak.org/NORAD/elements/gp.php?CATNR=33591&FORMAT=tle",
    "https://celestrak.org/NORAD/elements/gp.php?CATNR=57166&FORMAT=tle",
]

# ─── ANSI Colours ─────────────────────────────────────────────────────────────
RESET = "\033[0m"
BOLD  = "\033[1m"
DIM   = "\033[2m"
CYAN  = "\033[96m"
BLUE  = "\033[94m"
GREEN_BRIGHT = "\033[92m"
GREEN        = "\033[32m"
YELLOW       = "\033[33m"
GREY         = "\033[90m"
WHITE        = "\033[97m"

QUALITY_MAP = [
    (60, "EXCELLENT", GREEN_BRIGHT),
    (30, "GOOD",      GREEN),
    (15, "FAIR",      YELLOW),
    ( 0, "LOW",       GREY),
]

# ─── Location Detection ───────────────────────────────────────────────────────

@dataclasses.dataclass
class LocationResult:
    lat:      float
    lon:      float
    alt:      float  = 0.0
    city:     str    = ""
    region:   str    = ""
    country:  str    = ""
    source:   str    = ""
    accuracy: str    = ""

    @property
    def display_name(self) -> str:
        parts = [p for p in [self.city, self.region, self.country] if p]
        return ", ".join(parts) if parts else f"{self.lat:+.4f}°, {self.lon:+.4f}°"


# ── GPS via gpsd ─────────────────────────────────────────────────────────────

def _try_gpsd(timeout: float = 6.0) -> Optional[LocationResult]:
    """Connect to a running gpsd daemon via the gps Python module."""
    try:
        import gps  # pip install gps
        session = gps.gps(mode=gps.WATCH_ENABLE | gps.WATCH_NEWSTYLE)
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            report = session.next()
            if report.get("class") == "TPV":
                lat = report.get("lat")
                lon = report.get("lon")
                if lat is not None and lon is not None:
                    alt = float(report.get("alt") or 0.0)
                    epx = report.get("epx")
                    acc = f"±{epx:.0f} m" if epx else "GPS fix"
                    return LocationResult(
                        lat=lat, lon=lon, alt=alt,
                        source="GPS (gpsd)", accuracy=acc,
                    )
    except ImportError:
        pass
    except (ConnectionRefusedError, OSError, StopIteration):
        pass
    except Exception:
        pass
    return None


# ── GPS via NMEA serial ───────────────────────────────────────────────────────

_NMEA_PORTS = [
    "/dev/ttyUSB0", "/dev/ttyUSB1", "/dev/ttyUSB2",
    "/dev/ttyACM0", "/dev/ttyACM1",
    "/dev/ttyS0",   "/dev/ttyS1",
    "/dev/serial0",                  # Raspberry Pi GPIO UART
]
_NMEA_BAUDS = [9600, 4800, 38400, 115200]


def _nmea_to_decimal(raw: str, direction: str) -> float:
    dot = raw.index(".")
    deg = int(raw[: dot - 2])
    mins = float(raw[dot - 2 :])
    val = deg + mins / 60.0
    return -val if direction in ("S", "W") else val


def _parse_gga(line: str) -> Optional[tuple]:
    """Return (lat, lon, alt) from a $GxGGA sentence, or None."""
    parts = line.split(",")
    if len(parts) < 10:
        return None
    fix = parts[6]
    if fix in ("", "0"):          # no fix
        return None
    try:
        lat = _nmea_to_decimal(parts[2], parts[3])
        lon = _nmea_to_decimal(parts[4], parts[5])
        alt = float(parts[9]) if parts[9] else 0.0
        return lat, lon, alt
    except (ValueError, IndexError):
        return None


def _try_nmea_serial(timeout: float = 8.0) -> Optional[LocationResult]:
    """Read NMEA sentences directly from a serial GPS receiver."""
    try:
        import serial  # pip install pyserial
    except ImportError:
        return None

    for port in _NMEA_PORTS:
        if not os.path.exists(port):
            continue
        for baud in _NMEA_BAUDS:
            try:
                with serial.Serial(port, baud, timeout=1.5) as ser:
                    deadline = time.monotonic() + timeout
                    while time.monotonic() < deadline:
                        raw = ser.readline()
                        line = raw.decode("ascii", errors="ignore").strip()
                        if line[3:6] == "GGA":   # $GPGGA, $GNGGA, $GLGGA …
                            result = _parse_gga(line)
                            if result:
                                lat, lon, alt = result
                                return LocationResult(
                                    lat=lat, lon=lon, alt=alt,
                                    source=f"GPS (serial {port}@{baud})",
                                    accuracy="GPS fix",
                                )
            except Exception:
                continue
    return None


# ── GPS via Termux:API (Android) ─────────────────────────────────────────────

def _try_termux_location(timeout: float = 12.0) -> Optional[LocationResult]:
    """Use termux-location (requires Termux:API app + pkg install termux-api)."""
    try:
        result = subprocess.run(
            ["termux-location", "-p", "gps", "-r", "once"],
            capture_output=True, text=True, timeout=timeout,
        )
        if result.returncode != 0 or not result.stdout.strip():
            return None
        data = json.loads(result.stdout)
        acc = data.get("accuracy")
        return LocationResult(
            lat=float(data["latitude"]),
            lon=float(data["longitude"]),
            alt=float(data.get("altitude", 0.0)),
            source="GPS (termux-location)",
            accuracy=f"±{acc:.0f} m" if acc else "GPS fix",
        )
    except (FileNotFoundError, subprocess.TimeoutExpired):
        pass
    except (json.JSONDecodeError, KeyError, ValueError, OSError):
        pass
    return None


# ── IP Geolocation ────────────────────────────────────────────────────────────
# Three independent free APIs, no key required.  Tried in order until one
# succeeds.  Accuracy is city-level (~1–50 km depending on ISP).

def _parse_ip_api(data: dict) -> Optional[LocationResult]:
    if data.get("status") != "success":
        return None
    return LocationResult(
        lat=float(data["lat"]),
        lon=float(data["lon"]),
        city=data.get("city", ""),
        region=data.get("regionName", ""),
        country=data.get("country", ""),
        source="IP geolocation (ip-api.com)",
        accuracy="city-level  (~1–50 km)",
    )

def _parse_ipwho(data: dict) -> Optional[LocationResult]:
    if not data.get("success"):
        return None
    return LocationResult(
        lat=float(data["latitude"]),
        lon=float(data["longitude"]),
        city=data.get("city", ""),
        region=data.get("region", ""),
        country=data.get("country", ""),
        source="IP geolocation (ipwho.is)",
        accuracy="city-level  (~1–50 km)",
    )

def _parse_ipinfo(data: dict) -> Optional[LocationResult]:
    loc = data.get("loc", "")
    if "," not in loc:
        return None
    lat_s, lon_s = loc.split(",", 1)
    return LocationResult(
        lat=float(lat_s),
        lon=float(lon_s),
        city=data.get("city", ""),
        region=data.get("region", ""),
        country=data.get("country", ""),
        source="IP geolocation (ipinfo.io)",
        accuracy="city-level  (~1–50 km)",
    )

_IP_GEO_APIS = [
    ("http://ip-api.com/json",  _parse_ip_api),
    ("https://ipwho.is/",       _parse_ipwho),
    ("https://ipinfo.io/json",  _parse_ipinfo),
]


def _try_ip_geolocation() -> Optional[LocationResult]:
    session = requests.Session()
    session.headers.update({"User-Agent": "wx_pass_tracker/1.0"})
    for url, parser in _IP_GEO_APIS:
        try:
            r = session.get(url, timeout=8)
            r.raise_for_status()
            result = parser(r.json())
            if result:
                return result
        except Exception:
            continue
    return None


# ── Orchestrator ─────────────────────────────────────────────────────────────

def auto_detect_location(
    gps_only: bool = False,
    verbose: bool = False,
) -> Optional[LocationResult]:
    """
    Try location sources in priority order:
      GPS (gpsd) → GPS (NMEA serial) → GPS (Termux) → IP geolocation

    Set gps_only=True to skip the IP fallback entirely.
    """
    methods: list[tuple[str, callable]] = [
        ("gpsd",              _try_gpsd),
        ("NMEA serial GPS",   _try_nmea_serial),
        ("termux-location",   _try_termux_location),
    ]
    if not gps_only:
        methods.append(("IP geolocation", _try_ip_geolocation))

    for name, fn in methods:
        if verbose:
            print(f"  Trying {name} ...", end=" ", flush=True)
        loc = fn()
        if loc is not None:
            if verbose:
                print(f"OK  ({loc.display_name})")
            return loc
        if verbose:
            print("not available")

    return None


# ─── TLE Fetching ─────────────────────────────────────────────────────────────

def parse_tle_block(text: str) -> dict[int, tuple[str, str, str]]:
    """Parse a raw TLE text block into {norad_id: (name, line1, line2)}."""
    result: dict[int, tuple[str, str, str]] = {}
    lines = [l.strip() for l in text.strip().splitlines() if l.strip()]
    i = 0
    while i + 2 < len(lines):
        name = lines[i]
        l1   = lines[i + 1]
        l2   = lines[i + 2]
        if l1.startswith("1 ") and l2.startswith("2 "):
            try:
                norad = int(l2[2:7])
                result[norad] = (name, l1, l2)
                i += 3
                continue
            except ValueError:
                pass
        i += 1
    return result


def fetch_tles(verbose: bool = False) -> dict[int, tuple[str, str, str]]:
    """
    Fetch TLEs from Celestrak.
    First tries the weather group (all at once), then falls back to per-CATNR.
    Returns {norad_id: (name, line1, line2)}.
    """
    wanted = {info["norad"] for info in ACTIVE_WX_SATS.values()}
    collected: dict[int, tuple[str, str, str]] = {}

    session = requests.Session()
    session.headers.update({"User-Agent": "wx_pass_tracker/1.0"})

    for url in TLE_URLS:
        if wanted.issubset(collected.keys()):
            break  # already have everything
        try:
            r = session.get(url, timeout=15)
            r.raise_for_status()
            parsed = parse_tle_block(r.text)
            for norad, tle in parsed.items():
                if norad in wanted and norad not in collected:
                    collected[norad] = tle
                    if verbose:
                        print(f"  + {tle[0]} (NORAD {norad})")
        except requests.RequestException as exc:
            if verbose:
                print(f"  [WARN] {url}: {exc}", file=sys.stderr)

    return collected


# ─── Pass Prediction ──────────────────────────────────────────────────────────

def ephem_to_utc(ed: ephem.Date) -> datetime:
    return ed.datetime().replace(tzinfo=timezone.utc)


def predict_passes(
    sat_name: str,
    sat_info: dict,
    tle: tuple[str, str, str],
    lat: float,
    lon: float,
    alt_m: float,
    min_elev_deg: float,
    hours: int,
) -> list[dict]:
    """
    Calculate all passes for one satellite within the given time window.
    AOS / LOS are computed at the min_elev_deg horizon so the reported
    times correspond to when the satellite is actually receivable.
    """
    _, l1, l2 = tle
    sat = ephem.readtle(sat_name, l1, l2)

    obs          = ephem.Observer()
    obs.lat      = str(lat)
    obs.lon      = str(lon)
    obs.elev     = alt_m
    obs.pressure = 0       # no atmospheric refraction
    obs.horizon  = str(min_elev_deg)   # AOS/LOS at this elevation

    now_utc  = datetime.now(timezone.utc)
    obs.date = ephem.Date(now_utc.strftime("%Y/%m/%d %H:%M:%S"))
    end_date = obs.date + hours / 24.0

    passes: list[dict] = []

    while True:
        try:
            aos_t, aos_az, tca_t, tca_alt, los_t, los_az = obs.next_pass(sat)
        except (ephem.NeverUpError, ephem.AlwaysUpError):
            break
        except Exception:
            break

        if aos_t > end_date:
            break
        if aos_t == los_t:
            # Grazing pass — skip
            obs.date = aos_t + 1 * ephem.minute
            continue

        max_elev_deg = math.degrees(tca_alt)

        passes.append({
            "sat":       sat_name,
            "mode":      sat_info["mode"],
            "freq":      sat_info["freq"],
            "status":    sat_info["status"],
            "aos":       ephem_to_utc(aos_t),
            "tca":       ephem_to_utc(tca_t),
            "los":       ephem_to_utc(los_t),
            "max_elev":  round(max_elev_deg, 1),
            "aos_az":    round(math.degrees(aos_az), 1),
            "los_az":    round(math.degrees(los_az), 1),
            "duration":  max(0, int((los_t - aos_t) * 86400)),
        })

        # Advance past this pass
        obs.date = los_t + 1 * ephem.minute

    return passes


# ─── Formatting Helpers ───────────────────────────────────────────────────────

def quality_for(elev: float) -> tuple[str, str]:
    for threshold, label, colour in QUALITY_MAP:
        if elev >= threshold:
            return label, colour
    return "LOW", GREY


COMPASS = ["N","NNE","NE","ENE","E","ESE","SE","SSE",
           "S","SSW","SW","WSW","W","WNW","NW","NNW"]

def az_compass(deg: float) -> str:
    return COMPASS[round(deg / 22.5) % 16]


def fmt_duration(seconds: int) -> str:
    m, s = divmod(abs(seconds), 60)
    return f"{m}m {s:02d}s"


def fmt_time(dt: datetime, local: bool) -> str:
    if local:
        return dt.astimezone().strftime("%H:%M:%S %Z")
    return dt.strftime("%H:%M:%S UTC")


def fmt_date(dt: datetime, local: bool) -> str:
    d = dt.astimezone() if local else dt
    return d.strftime("%A, %B %-d %Y")


# ─── Output ───────────────────────────────────────────────────────────────────

def print_header(loc: LocationResult, min_elev: float, hours: int, use_color: bool) -> None:
    def c(s): return s if use_color else ""

    print()
    print(f"{c(BOLD)}{c(WHITE)}  Weather Satellite Pass Tracker{c(RESET)}")
    print(f"{c(DIM)}  {'─' * 52}{c(RESET)}")

    if loc.display_name != f"{loc.lat:+.4f}°, {loc.lon:+.4f}°":
        print(f"  Location  {c(BOLD)}{loc.display_name}{c(RESET)}")
    print(f"  Position  {loc.lat:+.4f}°,  {loc.lon:+.4f}°"
          + (f"   alt {loc.alt:.0f} m" if loc.alt else ""))
    src_colour = CYAN if "GPS" in loc.source else YELLOW
    print(f"  Source    {c(src_colour)}{loc.source}{c(RESET)}"
          + (f"  {c(DIM)}{loc.accuracy}{c(RESET)}" if loc.accuracy else ""))
    print(f"  Window    next {hours} h")
    print(f"  Min elev  {min_elev}°  (AOS/LOS reported at this angle)")
    print(f"  Sats      NOAA 15 / 18 / 19 (APT 137 MHz)  ·  METEOR-M 2-3 (LRPT)")
    print()


def print_passes(passes: list[dict], local: bool, use_color: bool) -> None:
    def c(s): return s if use_color else ""

    if not passes:
        print("  No passes found matching your criteria.\n")
        return

    passes = sorted(passes, key=lambda p: p["aos"])

    for date_str, group_iter in groupby(passes, key=lambda p: fmt_date(p["aos"], local)):
        print(f"{c(BOLD)}{c(CYAN)}  {date_str}{c(RESET)}")
        print(f"{c(DIM)}  {'─' * 66}{c(RESET)}")

        for p in group_iter:
            qlabel, qcolour = quality_for(p["max_elev"])

            aos_s = fmt_time(p["aos"], local)
            los_s = fmt_time(p["los"], local)
            dur_s = fmt_duration(p["duration"])

            # Satellite name + mode line
            mode_colour = BLUE if p["mode"] == "APT" else CYAN
            print(
                f"\n  {c(BOLD)}{c(WHITE)}{p['sat']:<14}{c(RESET)}"
                f"  {c(mode_colour)}{c(BOLD)}{p['mode']}{c(RESET)}"
                f"  {p['freq']}"
            )

            # AOS / LOS / Duration
            print(
                f"  AOS {c(BOLD)}{aos_s}{c(RESET)}"
                f"   LOS {los_s}"
                f"   {c(BOLD)}{dur_s}{c(RESET)}"
            )

            # Elevation + azimuth
            bar_width = 24
            bar_fill  = round((p["max_elev"] / 90) * bar_width)
            bar       = "█" * bar_fill + "░" * (bar_width - bar_fill)
            print(
                f"  Max elev {c(qcolour)}{c(BOLD)}{p['max_elev']:>5.1f}°  {bar}  {qlabel}{c(RESET)}"
            )
            print(
                f"  AOS az {p['aos_az']:>6.1f}° ({az_compass(p['aos_az']):<3})"
                f"   LOS az {p['los_az']:>6.1f}° ({az_compass(p['los_az'])})"
            )
            print(f"  {c(DIM)}{p['status']}{c(RESET)}")

        print()


def print_legend(use_color: bool) -> None:
    def c(s): return s if use_color else ""
    parts = []
    for _, label, colour in QUALITY_MAP:
        parts.append(f"{c(colour)}{c(BOLD)}{label}{c(RESET)}")
    thresholds = ["≥60°", "≥30°", "≥15°", "<15°"]
    legend_items = "  ·  ".join(f"{p} {t}" for p, t in zip(parts, thresholds))
    print(f"  Pass quality: {legend_items}\n")


# ─── Main ─────────────────────────────────────────────────────────────────────

def main() -> None:
    parser = argparse.ArgumentParser(
        prog="wx_pass_tracker",
        description="Predict upcoming weather satellite passes (NOAA APT / METEOR LRPT).",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
location detection (used when --lat/--lon are omitted):
  1. gpsd            needs: pip install gps  +  gpsd running
  2. NMEA serial     needs: pip install pyserial  +  USB/GPIO GPS receiver
  3. termux-location needs: Termux:API app + pkg install termux-api  (Android)
  4. IP geolocation  ip-api.com → ipwho.is → ipinfo.io  (city-level, no key)

examples:
  python wx_pass_tracker.py                          # auto-detect location
  python wx_pass_tracker.py --gps                    # GPS only, no IP fallback
  python wx_pass_tracker.py --lat 47.5 --lon 19.0   # manual override
  python wx_pass_tracker.py --min-elev 20 --hours 48
  python wx_pass_tracker.py --local-time --no-color > passes.txt

data source: Celestrak (https://celestrak.org) — free, no API key required
        """,
    )

    loc_group = parser.add_argument_group("location (all optional — auto-detected if omitted)")
    loc_group.add_argument(
        "--lat", type=float, default=None, metavar="DEG",
        help="Observer latitude in decimal degrees (North = positive)",
    )
    loc_group.add_argument(
        "--lon", type=float, default=None, metavar="DEG",
        help="Observer longitude in decimal degrees (East = positive)",
    )
    loc_group.add_argument(
        "--alt", type=float, default=None, metavar="METRES",
        help="Observer altitude in metres (default: from GPS or 0)",
    )
    loc_group.add_argument(
        "--gps", action="store_true",
        help="Force GPS-only location detection (skip IP geolocation fallback)",
    )
    loc_group.add_argument(
        "--no-auto", action="store_true",
        help="Disable all auto-detection; --lat and --lon become required",
    )

    parser.add_argument(
        "--min-elev", type=float, default=10.0, metavar="DEG",
        help="Minimum peak elevation for a pass to appear, degrees (default: 10)",
    )
    parser.add_argument(
        "--hours", type=int, default=24, metavar="N",
        help="Prediction window in hours (default: 24)",
    )
    parser.add_argument(
        "--local-time", action="store_true",
        help="Display pass times in your local timezone instead of UTC",
    )
    parser.add_argument(
        "--no-color", action="store_true",
        help="Disable ANSI colour output (useful for piping to a file)",
    )
    parser.add_argument(
        "--verbose", action="store_true",
        help="Print TLE fetch and location-detection details",
    )

    args = parser.parse_args()

    use_color = not args.no_color and sys.stdout.isatty()
    def c(s): return s if use_color else ""

    # ── Resolve observer location ────────────────────────────────────────────
    loc: Optional[LocationResult] = None

    manual_lat = args.lat is not None
    manual_lon = args.lon is not None

    if manual_lat and manual_lon:
        # Fully manual — wrap in a LocationResult so the rest of the code is uniform
        loc = LocationResult(
            lat=args.lat,
            lon=args.lon,
            alt=args.alt or 0.0,
            source="manual (--lat/--lon)",
        )

    elif manual_lat or manual_lon:
        parser.error("Provide both --lat and --lon, or neither (for auto-detection).")

    elif args.no_auto:
        parser.error("--no-auto requires --lat and --lon to be specified.")

    else:
        # Auto-detect
        print()
        print(f"{c(BOLD)}{c(WHITE)}  Weather Satellite Pass Tracker{c(RESET)}")
        print(f"{c(DIM)}  {'─' * 52}{c(RESET)}")
        print(f"  Detecting location...", flush=True)
        if args.verbose:
            print()

        loc = auto_detect_location(gps_only=args.gps, verbose=args.verbose)

        if loc is None:
            print(
                f"\n  {c(YELLOW)}Could not determine location automatically.{c(RESET)}\n"
                f"  Specify it manually with:  --lat <deg> --lon <deg>\n"
            )
            sys.exit(1)

        # User can still override altitude independently
        if args.alt is not None:
            loc.alt = args.alt

        # Clear the partial header — print_header will reprint cleanly
        print(f"\033[A\033[A\033[A\033[2K\033[A\033[2K\033[A\033[2K", end="")

    print_header(loc, args.min_elev, args.hours, use_color)

    # ── Fetch TLEs ───────────────────────────────────────────────────────────
    print(f"  Fetching TLEs from Celestrak...", end="", flush=True)
    tles = fetch_tles(verbose=args.verbose)

    found   = [n for n, i in ACTIVE_WX_SATS.items() if i["norad"] in tles]
    missing = [n for n, i in ACTIVE_WX_SATS.items() if i["norad"] not in tles]

    print(f"  {c(GREEN)}{len(found)}/{len(ACTIVE_WX_SATS)} satellites loaded{c(RESET)}")

    if missing:
        for name in missing:
            print(
                f"  {c(YELLOW)}[WARN] TLE not found for {name} "
                f"(NORAD {ACTIVE_WX_SATS[name]['norad']}){c(RESET)}",
                file=sys.stderr,
            )

    if not found:
        print(
            f"\n  {c(YELLOW)}No TLEs could be fetched. "
            f"Check your internet connection or try again later.{c(RESET)}\n"
        )
        sys.exit(1)

    # ── Predict Passes ───────────────────────────────────────────────────────
    all_passes: list[dict] = []
    for sat_name, sat_info in ACTIVE_WX_SATS.items():
        if sat_info["norad"] not in tles:
            continue
        passes = predict_passes(
            sat_name, sat_info, tles[sat_info["norad"]],
            loc.lat, loc.lon, loc.alt,
            args.min_elev, args.hours,
        )
        all_passes.extend(passes)

    total = len(all_passes)
    tz_note = "local time" if args.local_time else "UTC"
    print(
        f"  {c(BOLD)}{total} pass{'es' if total != 1 else ''}{c(RESET)} "
        f"found in the next {args.hours} h  ({tz_note})\n"
    )

    print_passes(all_passes, local=args.local_time, use_color=use_color)
    print_legend(use_color)


if __name__ == "__main__":
    main()
