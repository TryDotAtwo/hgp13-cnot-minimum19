"""Untrusted depth-two tree-certificate probe; Lean checks all emitted edges."""
from pathlib import Path
import sys

GOALS = {
    "original": [73, 82, 3, 6, 27, 54, 100],
    "transpose": [21, 62, 104, 17, 50, 96, 67],
}
orientation = sys.argv[1] if len(sys.argv) > 1 else "transpose"
max_depth = 4 if "--depth4" in sys.argv else (3 if "--depth3" in sys.argv else 2)
parent_only = int(sys.argv[3]) if len(sys.argv) > 3 and sys.argv[2] == "--parent" else None
all_parents = "--all-parents" in sys.argv
omit_child = "--omit-child" in sys.argv
goals = GOALS[orientation]
base = [1, 2, 4, 8, 16, 32, 64]
base_set = set(base)


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
for depth in range(max_depth):
    next_layer = {tuple(sorted(xs + (z,)))
                  for xs in layers[-1] for z in successors(xs)}
    layers.append(sorted(next_layer))


def key(xs):
    result = 0
    for z in xs:
        result = result * 128 + z
    return result


def as_lean_state(xs):
    return "[" + ",".join(f"({z} : Value)" for z in xs) + "]"


def tree(xs):
    if not xs:
        return ".nil"
    mid = len(xs) // 2
    return f"(.node {tree(xs[:mid])} {as_lean_state(xs[mid])} {tree(xs[mid+1:])})"


def emit_tree(label, xs, source, max_literal_nodes=64):
    if len(xs) <= max_literal_nodes:
        source.append(f"def {label} : Tree := {tree(xs)}")
        return
    mid = len(xs) // 2
    emit_tree(label + "_l", xs[:mid], source, max_literal_nodes)
    emit_tree(label + "_r", xs[mid+1:], source, max_literal_nodes)
    source.append(
        f"def {label} : Tree := .node {label}_l "
        f"{as_lean_state(xs[mid])} {label}_r"
    )


expected = {
    "original": [1, 28, 583, 10945, 200390],
    "transpose": [1, 39, 970, 20125, 386819],
}[orientation]
assert [len(x) for x in layers] == expected[:max_depth+1]
for layer in layers:
    assert len({key(xs) for xs in layer}) == len(layer)

suffix = f"_parent{parent_only}" if parent_only is not None else ""
if all_parents:
    assert max_depth == 2 and parent_only is None and not omit_child
    suffix = "_all"
if omit_child:
    assert parent_only is not None
    suffix += "_omitted"
out = Path(__file__).with_name(f"PrefixTreeDepth{max_depth}_{orientation}{suffix}.lean")
source = [
    "import PrefixTreeCertificate",
    "namespace HGP13.PrefixTreeDepth2Omitted" if omit_child else
        "namespace HGP13.PrefixTreeDepth2",
    "open HGP13.PrefixTreeCertificate HGP13.Catalogues",
    "set_option maxRecDepth 20000",
    "set_option maxHeartbeats 100000000",
]
for depth, layer in enumerate(layers):
    emitted = layer
    if depth == max_depth and omit_child:
        parent = layers[max_depth-1][parent_only]
        child = tuple(sorted(parent + (successors(parent)[0],)))
        assert child in layer
        emitted = [xs for xs in layer if xs != child]
    emit_tree(f"layer{depth}", sorted(emitted,key=key), source)
goal_name = "TransposeFree.goals" if orientation == "transpose" else "FreeXor.maskGoals"
if all_parents:
    source.append(
        f"theorem step01 : stepOK FreeXor.maskBasis {goal_name} layer0 layer1 = true := by decide +kernel"
    )
    for idx, parent in enumerate(layers[1]):
        source.append(
            f"theorem parent{idx} : nodeStepOK FreeXor.maskBasis {goal_name} "
            f"{as_lean_state(parent)} layer2 = true := by decide +kernel"
        )
    literal = "[" + ",".join(as_lean_state(xs) for xs in layers[1]) + "]"
    source.append(f"theorem layer1_entries : entries layer1 = {literal} := by decide +kernel")
    source += [
        f"theorem step12 : stepOK FreeXor.maskBasis {goal_name} layer1 layer2 = true := by",
        "  apply stepOK_of_nodes",
        "  intro xs hxs",
        "  rw [layer1_entries] at hxs",
        "  simp only [List.mem_cons,List.not_mem_nil,or_false] at hxs",
        "  rcases hxs with " + " | ".join(f"h{i}" for i in range(len(layers[1]))),
    ]
    for idx in range(len(layers[1])):
        source += [f"  · rcases h{idx} with rfl",f"    exact parent{idx}"]
elif parent_only is None:
    source += [
        f"theorem step01 : stepOK FreeXor.maskBasis {goal_name} layer0 layer1 = true := by decide +kernel",
        f"theorem step12 : stepOK FreeXor.maskBasis {goal_name} layer1 layer2 = true := by decide +kernel",
    ]
else:
    parent = layers[max_depth-1][parent_only]
    expected = "false" if omit_child else "true"
    source.append(
        f"theorem parent{parent_only} : nodeStepOK FreeXor.maskBasis {goal_name} "
        f"{as_lean_state(parent)} layer{max_depth} = {expected} := by decide +kernel"
    )
source.append("end HGP13.PrefixTreeDepth2Omitted" if omit_child else
              "end HGP13.PrefixTreeDepth2")
out.write_text("\n".join(source) + "\n", encoding="utf-8")
print(out, "layers", [len(x) for x in layers], "bytes", out.stat().st_size)
