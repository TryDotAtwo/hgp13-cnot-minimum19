"""Untrusted packed fourth-layer probe; Lean verifies the selected parent."""
from pathlib import Path
import sys

GOALS = {
    "original": [73, 82, 3, 6, 27, 54, 100],
    "transpose": [21, 62, 104, 17, 50, 96, 67],
}
orientation = sys.argv[1] if len(sys.argv) > 1 else "transpose"
final_node_only = "--final-node" in sys.argv
parent_index = int(sys.argv[2]) if len(sys.argv) > 2 and not sys.argv[2].startswith("--") else 5000
goals = GOALS[orientation]
base_set = {1, 2, 4, 8, 16, 32, 64}


def closure(extras):
    known = base_set | set(extras)
    while True:
        ready = {a ^ b for a in known for b in known} & set(goals) - known
        if not ready:
            return known
        known |= ready


def successors(extras):
    known = closure(extras)
    return [z for z in range(1, 128)
            if z not in known and any((z ^ a) in known for a in known)]


layers = [[()]]
for _ in range(4):
    layers.append(sorted({tuple(sorted(xs + (z,)))
                          for xs in layers[-1] for z in successors(xs)}))

expected = {
    "original": [1, 28, 583, 10945, 200390],
    "transpose": [1, 39, 970, 20125, 386819],
}[orientation]
assert [len(x) for x in layers] == expected
assert 0 <= parent_index < len(layers[3])


def key(xs):
    n = 0
    for z in xs:
        n = n * 128 + z
    return n


def state(xs):
    return "[" + ",".join(f"({z} : Value)" for z in xs) + "]"


masks = {}
for a, b, c, d in layers[4]:
    triple = (a, b, c)
    masks[triple] = masks.get(triple, 0) | (1 << d)
items = sorted(masks.items(), key=lambda item: key(item[0]))

if final_node_only:
    first_feasible = next(xs for xs in layers[4]
                          if set(goals) <= closure(xs))
    triple = first_feasible[:3]
    mask = masks[triple]
    goal_name = "TransposeFree.goals" if orientation == "transpose" else "FreeXor.maskGoals"
    table_name = "SectorGraph359.prefix4" if orientation == "transpose" else "OriginalPrefixes.prefix4"
    lines = [
        "import PrefixPackedFourth",
        "import SectorGraph359" if orientation == "transpose" else "import OriginalPrefixes",
        "namespace HGP13.PackedFourthFinalNode",
        "open HGP13.PrefixPackedFourth HGP13.Catalogues",
        "set_option maxRecDepth 20000",
        "set_option maxHeartbeats 100000000",
        f"def mask : BitVec 128 := BitVec.ofNat 128 {mask}",
        f"theorem final_hit : finalNodeOK {goal_name} "
        f"(SectorGraph359.lookup {table_name}) {state(triple)} mask = true := by decide +kernel",
        f"theorem deleted_zero_rejected : finalNodeOK {goal_name} "
        f"(fun k => (k != 0) && SectorGraph359.lookup {table_name} k) "
        f"{state(triple)} mask = false := by decide +kernel",
        "end HGP13.PackedFourthFinalNode",
    ]
    out = Path(__file__).with_name(f"PackedFourthFinalNode_{orientation}.lean")
    out.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(out, "triple", triple, "mask_bits", mask.bit_count(), "bytes", out.stat().st_size)
    sys.exit(0)


def literal_tree(items):
    if not items:
        return ".nil"
    mid = len(items) // 2
    triple, mask = items[mid]
    return (f"(.node {literal_tree(items[:mid])} {state(triple)} "
            f"(BitVec.ofNat 128 {mask}) {literal_tree(items[mid+1:])})")


def emit_tree(label, items, lines, max_literal_nodes=48):
    if len(items) <= max_literal_nodes:
        lines.append(f"def {label} : Tree4 := {literal_tree(items)}")
        return
    mid = len(items) // 2
    emit_tree(label + "_l", items[:mid], lines, max_literal_nodes)
    emit_tree(label + "_r", items[mid+1:], lines, max_literal_nodes)
    triple, mask = items[mid]
    lines.append(f"def {label} : Tree4 := .node {label}_l {state(triple)} "
                 f"(BitVec.ofNat 128 {mask}) {label}_r")


parent = layers[3][parent_index]
goal_name = "TransposeFree.goals" if orientation == "transpose" else "FreeXor.maskGoals"
lines = [
    "import PrefixPackedFourth",
    "namespace HGP13.PackedFourthProbe",
    "open HGP13.PrefixPackedFourth HGP13.Catalogues",
    "set_option maxRecDepth 20000",
    "set_option maxHeartbeats 100000000",
]
emit_tree("layer4", items, lines)
lines += [
    f"theorem parent{parent_index} : nodeStepOK FreeXor.maskBasis {goal_name} "
    f"{state(parent)} layer4 = true := by decide +kernel",
    "end HGP13.PackedFourthProbe",
]
out = Path(__file__).with_name(f"PackedFourth_{orientation}_parent{parent_index}.lean")
out.write_text("\n".join(lines) + "\n", encoding="utf-8")
print(out, "layers", expected, "prefixes", len(items), "bytes", out.stat().st_size)
