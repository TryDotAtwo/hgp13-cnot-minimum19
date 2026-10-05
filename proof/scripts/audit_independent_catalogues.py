"""Audit the separate exhaustive catalogue run against the pinned export."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "scripts/independent_catalogue_check.cpp"
COUNTS = ROOT / "evidence/independent_catalogue_counts.txt"
KEYS = ROOT / "evidence/independent_catalogue_keys.txt"
PINNED = ROOT / "scale_pilot/catalogue_keys.txt"
expected = {(0, 3): (298, 524), (0, 4): (21687, 40022),
            (1, 3): (298, 524), (1, 4): (21823, 40208)}

lines = COUNTS.read_text(encoding="utf-8").splitlines()
if len(lines) != 2:
    raise ValueError("expected two orientation count lines")
for orientation, line in enumerate(lines):
    tag, o, n3, n4, k3, k4 = line.split()
    if tag != "COUNTS" or int(o) != orientation:
        raise ValueError("bad count record")
    if (int(n3), int(k3)) != expected[(orientation, 3)]:
        raise ValueError("triple count mismatch")
    if (int(n4), int(k4)) != expected[(orientation, 4)]:
        raise ValueError("quadruple count mismatch")

parsed = {(o, k): [] for o, k in expected}
for line in KEYS.read_text(encoding="utf-8").splitlines():
    o, k, x = map(int, line.split())
    if (o, k) not in parsed:
        raise ValueError("unexpected orientation/capacity")
    parsed[o, k].append(x)
for group, keys in parsed.items():
    if len(keys) != expected[group][1] or keys != sorted(set(keys)):
        raise ValueError(f"bad key count, order or uniqueness: {group}")
if KEYS.read_bytes() != PINNED.read_bytes():
    raise ValueError("independent keys differ from pinned-source export")

sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
report = {
    "status": "PASS: independent exhaustive catalogue keys equal pinned-source export",
    "source_sha256": sha(SOURCE),
    "independent_keys_sha256": sha(KEYS),
    "pinned_export_sha256": sha(PINNED),
    "counts_sha256": sha(COUNTS),
    "records": {f"orientation_{o}_capacity_{k}": {"catalogues": n, "keys": m}
                for (o, k), (n, m) in expected.items()},
    "scope": "external enumeration; Lean's literal trees are checked separately; no formal C++ semantics or binary provenance attestation",
}
(ROOT / "evidence/independent_catalogue_audit.json").write_text(
    json.dumps(report, indent=2) + "\n", encoding="utf-8"
)
print(report["status"])
