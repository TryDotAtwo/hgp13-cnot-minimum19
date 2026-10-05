"""Pin the bounded xor_cost/BFS differential test's source and result."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
source = ROOT / "hgp13_verify.cpp"
harness = ROOT / "scripts/xor_cost_differential.cpp"
output = ROOT / "evidence/xor_cost_differential.txt"
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
if sha(source) != "2174f445df534455c30e9ae7b54b8dfff4fdbdce3ff4eaf6b7d7e557fa3f8e4c":
    raise ValueError("pinned verifier changed")
expected = "PASS XOR_COST_DIFFERENTIAL trials=1518 cells=453376 seed=decafbad637a59e1\n"
if output.read_text(encoding="utf-8") != expected:
    raise ValueError("bounded differential test did not pass exactly")
report = {
    "status": "PASS: xor_cost equals BFS oracle on 1518 deterministic histories",
    "pinned_source_sha256": sha(source),
    "harness_sha256": sha(harness),
    "output_sha256": sha(output),
    "compiler": "g++ 11.4.0 -O2 -std=c++17 -pthread",
    "dimensions": [7, 8, 9],
    "histories": 1518,
    "checked_cells": 453376,
    "scope": "bounded differential test; not a formal proof of the C++ loop",
}
(ROOT / "evidence/xor_cost_differential_audit.json").write_text(
    json.dumps(report, indent=2) + "\n", encoding="utf-8"
)
print(report["status"])
