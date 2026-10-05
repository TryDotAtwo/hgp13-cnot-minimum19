"""Generate scratch full-row terminal potentials for q=2 and p=1 samples.

Python proposes tables; Lean checks every edge of each table against every
historical full row.  This is a performance pilot, not a sector certificate.
"""
from pathlib import Path
from collections import deque
import hashlib
import json

root = Path(__file__).resolve().parent
cases = {0: ([0, 1], [0, 1]), 315: ([0], [0])}
goals = [73, 82, 3, 6, 27, 54, 100]
private_outputs = [6, 7, 9, 10, 11, 12]
report = {}


def lift(value, wires):
    return sum(1 << w for i, w in enumerate(wires) if (value >> i) & 1)


for case_id, (sources, relays) in cases.items():
    lines = (root / f"sector_scale_{case_id}.log").read_text(encoding="utf-8").splitlines()
    fields = next(line.split() for line in lines if line.startswith("TERMINAL "))
    depth, total, ns, ny = map(int, fields[1:5])
    assert ns == len(sources) and ny == len(relays)
    nc = ns + ny + 1
    values = list(map(int, fields[5:]))
    history = sum(values[nc + i] << (64 * i) for i in range(8))
    width = 7 + ny
    wires = list(range(6)) + [8] + [private_outputs[j] for j in relays]
    forms = [v for v in range(1, 1 << width) if (history >> v) & 1]
    dist = [10**9] * (1 << width)
    dist[0] = 0
    queue = deque([0])
    while queue:
        x = queue.popleft()
        for v in forms:
            y = x ^ v
            if dist[y] > dist[x] + 1:
                dist[y] = dist[x] + 1
                queue.append(y)
    weights = [min(3, x) for x in dist]
    assert all(x < 10**9 for x in dist)
    table = sum(w << (2 * i) for i, w in enumerate(weights))
    targets = [goals[j] for j in range(6) if j not in relays]
    target_weights = [weights[v] for v in targets]
    assert depth + sum(target_weights) > 18
    assert depth + sum(dist[v] for v in targets) == total
    full_forms = [lift(v, wires) for v in forms]
    full_targets = [lift(v, wires) for v in targets]
    sector = f"⟨false,{sources},{[private_outputs[j] for j in relays]}⟩"
    code = f"""import FullPackedPotential
import SectorCoordinates
namespace HGP13.SectorScalePotential{case_id}
set_option maxRecDepth 20000
set_option maxHeartbeats 100000000
def sector : SectorCover.Sector := {sector}
def history : List Row := {full_forms}
def targets : List Row := {full_targets}
def table : Nat := {table}
theorem checked : FullPackedPotential.check (SectorCoordinates.embed sector) history table = true := by decide
theorem bound : 18 < {depth} +
  (targets.map (fun r => FullPackedPotential.tableWeight table
    (PackedRows.pack (SectorCoordinates.embed sector) r))).sum := by decide
end HGP13.SectorScalePotential{case_id}
"""
    path = root / f"SectorScalePotential{case_id}.lean"
    path.write_text(code, encoding="utf-8")
    report[str(case_id)] = {
        "source_sha256": hashlib.sha256(code.encode()).hexdigest(),
        "source_bytes": len(code.encode()),
        "width": width,
        "history_forms": len(forms),
        "weight_table_bits": table.bit_length(),
        "target_weights": target_weights,
        "verified_lower_bound_candidate": depth + sum(target_weights),
        "actual_cost_from_python": total,
    }

(root / "sector_scale_potentials.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
print(report)
