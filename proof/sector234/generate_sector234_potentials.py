"""Generate candidate 8-bit terminal potentials; Lean checks every certificate."""
import json
from collections import deque
from pathlib import Path

here = Path(__file__).resolve().parent
report = json.loads((here / "pilot234_replay_report.json").read_text())
targets = [21, 62, 104, 50, 96]
out = [
    "import Sector234Encoding",
    "namespace HGP13.Sector234Potentials",
    "open Sector234Encoding FullPackedPotential SectorCoordinates",
    "def targets : List Row := [" + ",".join(f"liftMask ({v} : BitVec 8)" for v in targets) + "]",
]
for i, terminal in enumerate(report["terminal_costs"]):
    history = terminal["history"]
    forms = [v for v in range(256) if history >> v & 1]
    distances = [999] * 256
    distances[0] = 0
    queue = deque([0])
    while queue:
        x = queue.popleft()
        for v in forms:
            y = x ^ v
            if distances[y] > distances[x] + 1:
                distances[y] = distances[x] + 1
                queue.append(y)
    assert max(distances) < 999
    weights = [min(d, 3) for d in distances]
    lower = terminal["depth"] + sum(weights[v] for v in targets)
    assert lower > 18
    assert all(weights[x ^ v] <= weights[x] + 1 for x in range(256) for v in forms)
    table = sum(v << (2 * j) for j, v in enumerate(weights))
    out.extend([
        f"def history{i} : List Row := [" + ",".join(f"liftMask ({v} : BitVec 8)" for v in forms) + "]",
        f"def table{i} : Nat := {table}",
        "set_option maxRecDepth 20000 in",
        "set_option maxHeartbeats 2000000 in",
        f"theorem checked{i} : check (embed sector) history{i} table{i} = true := by decide +kernel",
        f"theorem bound{i} : 18 < {terminal['depth']} + (targets.map "
        f"(fun z => tableWeight table{i} (PackedRows.pack (embed sector) z))).sum := by decide +kernel",
        f"theorem excludes{i} (costs : Row → Nat)",
        f"    (hc : ∀ z ∈ targets, PassiveCost.cost history{i} z = some (costs z)) :",
        f"    18 < {terminal['depth']} + (targets.map costs).sum :=",
        f"  excludes_completion (embed sector) history{i} targets table{i} {terminal['depth']} costs checked{i} hc bound{i}",
    ])
out.append("end HGP13.Sector234Potentials")
path = here / "Sector234Potentials.lean"
path.write_text("\n".join(out) + "\n", encoding="utf-8")
print(f"Generated {len(report['terminal_costs'])} candidate terminal certificates in {path}")
