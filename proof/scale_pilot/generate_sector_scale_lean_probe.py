"""Turn bounded C++ successor samples into scratch Lean equality probes.

These equality checks benchmark kernel work on real large-sector labels. They
do not prove coverage of any layer or of the sector as a whole.
"""
from pathlib import Path
import hashlib
import json
from collections import deque

root = Path(__file__).resolve().parent
package_source = root.parent / "hgp13_verify.cpp"
source = package_source if package_source.exists() else root.parent / "outputs/hgp13-arxiv/hgp13_verify.cpp"
cases = {0: ([0, 1], [0, 1]), 315: ([0], [0])}


def parse_state(nums, nc):
    assert len(nums) == nc + 8 + 4
    rows = nums[:nc]
    hist = sum(x << (64 * i) for i, x in enumerate(nums[nc:nc + 8]))
    counters = nums[nc + 8:]
    return rows, hist, counters


def literal(state):
    rows, hist, counters = state
    return "⟨[" + ",".join(map(str, rows)) + "], " + str(hist) + ", " + ", ".join(map(str, counters)) + "⟩"


report = {
    "pinned_cpp_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
    "instrumented_cpp_sha256": hashlib.sha256((root / "sector_scale_samples.cpp").read_bytes()).hexdigest(),
    "original_prefixes_sha256": hashlib.sha256((root / "OriginalPrefixes.lean").read_bytes()).hexdigest(),
    "cases": {},
    "scope": "local successor equality benchmark only; not sector coverage or prefix completeness",
}

out = [
    "import OriginalPrefixes",
    "namespace HGP13.SectorScaleProbe",
    "open HGP13.SharedSearch",
    "set_option maxRecDepth 20000",
    "set_option maxHeartbeats 100000000",
]
header = list(out)
for case_id, (sources, relays) in cases.items():
    case_out = []
    path = root / f"sector_scale_{case_id}.log"
    lines = path.read_text(encoding="utf-8").splitlines()
    samples = {}
    edges = {}
    terminal = None
    nc = len(sources) + len(relays) + 1
    for line in lines:
        parts = line.split()
        if parts[0] == "SAMPLE":
            depth, pop, ns, ny = map(int, parts[1:5])
            assert ns == len(sources) and ny == len(relays)
            samples[depth] = (pop, parse_state(list(map(int, parts[5:])), nc))
        elif parts[0] == "EDGE":
            depth, t, j = map(int, parts[1:4])
            edges.setdefault(depth, []).append((t, j, parse_state(list(map(int, parts[4:])), nc)))
        elif parts[0] == "TERMINAL":
            depth, total, ns, ny = map(int, parts[1:5])
            assert ns == len(sources) and ny == len(relays)
            terminal = (depth, total, parse_state(list(map(int, parts[5:])), nc))
    case_out += [
        f"def config{case_id} : Config := ⟨{sources}, {relays}, [73,82,3,6,27,54,100], HGP13.OriginalPrefixes.lookup⟩"
    ]
    report["cases"][str(case_id)] = {"sample_depths": {}, "log_sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
    for depth, (pop, state) in sorted(samples.items()):
        name = f"s{case_id}_{depth}"
        children = [literal(edge[2]) for edge in edges.get(depth, [])]
        case_out += [
            f"def {name} : State := {literal(state)}",
            f"theorem {name}_next : next config{case_id} {depth} {name} = [{','.join(children)}] := by decide",
        ]
        report["cases"][str(case_id)]["sample_depths"][str(depth)] = {
            "history_popcount": pop, "successors": len(children), "history_bits": state[1].bit_length()
        }
    assert len(samples) == 3
    assert terminal is not None
    depth, total, terminal_state = terminal
    dim = 7 + len(relays)
    history = terminal_state[1]
    forms = [v for v in range(1, 1 << dim) if (history >> v) & 1]
    distance = [10**9] * (1 << dim)
    distance[0] = 0
    queue = deque([0])
    while queue:
        x = queue.popleft()
        for v in forms:
            y = x ^ v
            if distance[y] > distance[x] + 1:
                distance[y] = distance[x] + 1
                queue.append(y)
    goals = [73, 82, 3, 6, 27, 54, 100]
    targets = [goals[j] for j in range(6) if j not in relays]
    target_costs = [distance[v] for v in targets]
    assert depth + sum(target_costs) == total
    assert all(x < 10**9 for x in target_costs)
    report["cases"][str(case_id)]["best_terminal"] = {
        "depth": depth,
        "total": total,
        "history_popcount": len(forms),
        "history_bits": history.bit_length(),
        "targets": targets,
        "target_costs": target_costs,
        "cap3_total": depth + sum(min(3, x) for x in target_costs),
    }
    case_out += [
        f"def terminal{case_id} : State := {literal(terminal_state)}",
        f"theorem terminal{case_id}_check : terminal config{case_id} terminal{case_id} = true := by decide",
    ]
    out.extend(case_out)
    (root / f"SectorScaleProbe{case_id}.lean").write_text(
        "\n".join(header + case_out + ["end HGP13.SectorScaleProbe"]) + "\n", encoding="utf-8"
    )

out.append("end HGP13.SectorScaleProbe")
output = "\n".join(out) + "\n"
(root / "SectorScaleProbe.lean").write_text(output, encoding="utf-8")
report["lean_probe_sha256"] = hashlib.sha256(output.encode()).hexdigest()
(root / "sector_scale_samples.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
(root / "SectorScaleImportOnly.lean").write_text(
    "\n".join(header + ["end HGP13.SectorScaleProbe"]) + "\n", encoding="utf-8"
)
print(root / "SectorScaleProbe.lean", len(output), "bytes")
