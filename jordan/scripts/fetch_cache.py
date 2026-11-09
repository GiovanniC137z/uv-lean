#!/usr/bin/env python3
"""Fetch only the pinned mathlib closure needed by this companion."""
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
MATHLIB = ROOT / ".lake" / "packages" / "mathlib"
SCHOENFLIES = ROOT / ".lake" / "packages" / "schoenflies-lean" / "Schoenflies"

if not MATHLIB.is_dir() or not SCHOENFLIES.is_dir():
    raise SystemExit("Fetch the pinned dependencies with `lake update` first")

files = list((ROOT / "UV").glob("*.lean")) + list(SCHOENFLIES.rglob("*.lean"))
modules = set()
for path in files:
    for line in path.read_text().splitlines():
        if line.startswith("import "):
            modules.update(re.findall(r"\bMathlib(?:\.[A-Za-z0-9_]+)+", line.split("--")[0]))
missing = [m for m in modules if not MATHLIB.joinpath(*m.split(".")).with_suffix(".lean").exists()]
if missing:
    raise SystemExit("Unknown pinned mathlib imports: " + ", ".join(sorted(missing)))
print(f"Fetching cache closure of {len(modules)} mathlib roots", flush=True)
subprocess.run(["lake", "exe", "cache", "get", *sorted(modules)], cwd=ROOT, check=True)
