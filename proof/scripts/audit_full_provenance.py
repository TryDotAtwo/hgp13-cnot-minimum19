"""Audit a fresh source/binary-bound full run against the preserved result."""
import hashlib
import json
from pathlib import Path
from audit_full_run import parse_run

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "evidence/full_provenance_2026-09-27"
PINNED_SOURCE = "2174f445df534455c30e9ae7b54b8dfff4fdbdce3ff4eaf6b7d7e557fa3f8e4c"
EXPECTED_IMAGE = "sha256:9ab7f14196d7bc671cd825564fbe5da9410e2ab1b88b7ad1017bbe65df760684"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def case_map(path):
    cases = {}
    lines = path.read_text(encoding="utf-8").splitlines()
    for line in lines:
        if line.startswith("CASE "):
            record = json.loads(line[5:])
            i = record["id"]
            if i in cases:
                raise ValueError(f"duplicate case {i}")
            cases[i] = record
    if set(cases) != set(range(363)):
        raise ValueError("missing or extra sector IDs")
    return cases, lines


source = ROOT / "hgp13_verify.cpp"
binary = OUT / "verifier.bin"
run = OUT / "run.txt"
record = OUT / "provenance.txt"
image = (OUT / "image_id.txt").read_text(encoding="utf-8").strip()
if image != EXPECTED_IMAGE:
    raise ValueError("container image identity differs")
if digest(source) != PINNED_SOURCE:
    raise ValueError("source digest differs")

fields = {}
for line in record.read_text(encoding="utf-8").splitlines():
    name, value = line.split(" ", 1)
    if name in fields:
        raise ValueError(f"duplicate provenance field: {name}")
    fields[name] = value
if set(fields) != {"source_sha256", "compiler", "compile_command",
                   "binary_sha256", "start_utc", "exit_code",
                   "end_utc", "run_sha256"}:
    raise ValueError("incomplete provenance fields")
if fields["source_sha256"].split()[0] != PINNED_SOURCE:
    raise ValueError("recorded source digest differs")
if fields["binary_sha256"].split()[0] != digest(binary):
    raise ValueError("recorded binary digest differs")
if fields["run_sha256"].split()[0] != digest(run):
    raise ValueError("recorded run digest differs")
if fields["exit_code"] != "0":
    raise ValueError("full verifier did not exit successfully")
if "g++ (Ubuntu 11.4.0" not in fields["compiler"]:
    raise ValueError("unexpected compiler version")
if fields["compile_command"] != (
    "g++ -O3 -std=c++17 -pthread hgp13_verify.cpp -o "
    "evidence/full_provenance_2026-09-27/verifier.bin"
):
    raise ValueError("unexpected compile command")

new, newlines = case_map(run)
old, oldlines = case_map(ROOT / "verification_run.txt")
structured_cases, _ = parse_run(run)
if structured_cases != new:
    raise ValueError("structural transcript audit differs")
if new != old:
    bad = [i for i in range(363) if new[i] != old[i]]
    raise ValueError(f"different case records: {bad[:10]}")
for tag in ("CATALOGUES ", "FOUNDATIONS_OK", "FAMILY 0 ",
            "FAMILY 1 ", "FAMILY 2 ", "FAMILY 3 ",
            "COMPLETED 363 ", "VERIFIED_FIXED_MATRIX_MINIMUM_19"):
    a = [line for line in newlines if line.startswith(tag)]
    b = [line for line in oldlines if line.startswith(tag)]
    if len(a) != 1 or a != b:
        raise ValueError(f"missing or different completion record: {tag}")
if newlines[-1] != "VERIFIED_FIXED_MATRIX_MINIMUM_19":
    raise ValueError("full verification marker is not final")

report = {
    "status": "PASS: fresh source/binary-bound full run agrees on all 363 cases",
    "source_sha256": PINNED_SOURCE,
    "binary_sha256": digest(binary),
    "run_sha256": digest(run),
    "preserved_run_sha256": digest(ROOT / "verification_run.txt"),
    "image_id": image,
    "compiler": fields["compiler"],
    "compile_command": fields["compile_command"],
    "start_utc": fields["start_utc"],
    "end_utc": fields["end_utc"],
    "exit_code": 0,
    "cases": len(new),
    "total_labels": sum(c["total"] for c in new.values()),
    "terminals": sum(c["terminals"] for c in new.values()),
    "all_best_gt_18": all(c["best"] > 18 for c in new.values()),
    "scope": "repeat execution of the same C++ implementation; not an independent solver or formal C++ refinement",
}
(OUT / "audit.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
print(report["status"])
