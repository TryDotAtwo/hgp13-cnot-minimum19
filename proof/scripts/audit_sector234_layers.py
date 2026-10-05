"""Compare every checked-sector state layer from two C++ exports as sets."""
import hashlib
import json
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ORIGINAL = ROOT / "hgp13_verify.cpp"
PINNED = "2174f445df534455c30e9ae7b54b8dfff4fdbdce3ff4eaf6b7d7e557fa3f8e4c"
if hashlib.sha256(ORIGINAL.read_bytes()).hexdigest() != PINNED:
    raise ValueError("pinned source changed")


if len(sys.argv) > 2:
    raise SystemExit("usage: python audit_sector234_layers.py [234|359]")
case_id = int(sys.argv[1]) if len(sys.argv) == 2 else 234
if case_id not in (234, 359):
    raise ValueError("only checked sectors 234 and 359 are supported")


def load(path):
    layers = defaultdict(set)
    case = None
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.startswith("STATE "):
            fields = tuple(map(int, line.split()[1:]))
            if len(fields) != 18:
                raise ValueError(f"bad state: {line}")
            depth, state = fields[0], fields[1:]
            if state in layers[depth]:
                raise ValueError(f"duplicate state at depth {depth}")
            layers[depth].add(state)
        elif line.startswith("CASE "):
            if case is not None:
                raise ValueError("multiple case records")
            case = json.loads(line[5:])
    if case is None or case["id"] != case_id:
        raise ValueError(f"missing sector-{case_id} case record")
    if sorted(layers) != [d for d, count in enumerate(case["layers"]) if count]:
        raise ValueError("missing or extra layer")
    if [len(layers[d]) for d in range(len(case["layers"]))] != case["layers"]:
        raise ValueError("state counts disagree with case record")
    return layers, case


diagnostic = ROOT / f"evidence/cpp_sector{case_id}_layers.txt"
candidate = (ROOT / "sector234/pilot234_graph.txt" if case_id == 234
             else ROOT / "pilot359/graph359.txt")
a, a_case = load(diagnostic)
b, b_case = load(candidate)
if a_case != b_case:
    raise ValueError("case records differ")
for depth in sorted(a):
    if a[depth] != b[depth]:
        raise ValueError(
            f"layer {depth} mismatch: only-pinned={len(a[depth]-b[depth])}, "
            f"only-candidate={len(b[depth]-a[depth])}"
        )
report = {
    "status": f"PASS: all sector-{case_id} state layers equal as sets",
    "pinned_source_sha256": PINNED,
    "diagnostic_sha256": hashlib.sha256(diagnostic.read_bytes()).hexdigest(),
    "candidate_sha256": hashlib.sha256(candidate.read_bytes()).hexdigest(),
    "layers": a_case["layers"],
    "states": sum(a_case["layers"]),
    "terminals": a_case["terminals"],
    "best": a_case["best"],
    "scope": "one sector; two C++ exports; candidate graph separately checked by Lean",
}
(ROOT / f"evidence/sector{case_id}_layers_audit.json").write_text(
    json.dumps(report, indent=2) + "\n", encoding="utf-8"
)
print(report["status"], report["states"])
