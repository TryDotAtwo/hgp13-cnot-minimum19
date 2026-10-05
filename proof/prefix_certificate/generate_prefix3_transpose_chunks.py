"""Emit bounded Lean obligations for all depth-2 to depth-3 prefix edges."""
from pathlib import Path

here = Path(__file__).resolve().parent
goals = {21, 62, 104, 17, 50, 96, 67}
base = {1, 2, 4, 8, 16, 32, 64}

def closure(extras):
    known = base | set(extras)
    while True:
        ready = {a ^ b for a in known for b in known} & goals - known
        if not ready:
            return known
        known |= ready

def successors(extras):
    known = closure(extras)
    return [z for z in range(1, 128)
            if z not in known and any((z ^ a) in known for a in known)]

layers = [[()]]
for _ in range(2):
    layers.append(sorted({tuple(sorted(xs + (z,)))
                          for xs in layers[-1] for z in successors(xs)}))
parents = layers[2]
assert len(parents) == 970

def lit(xs):
    return "[" + ",".join(f"({v} : Value)" for v in xs) + "]"

chunk_size = 25
chunks = [parents[i:i + chunk_size] for i in range(0, len(parents), chunk_size)]
for c, chunk in enumerate(chunks):
    first = c * chunk_size
    module = f"PrefixTreeDepth3TransposeChunk{c:02d}"
    out = [
        "import PrefixTreeDepth3TransposeBase",
        "namespace HGP13.PrefixTreeDepth3Transpose",
        "open HGP13.PrefixTreeCertificate HGP13.Catalogues",
        "set_option maxRecDepth 20000",
        "set_option maxHeartbeats 100000000",
    ]
    for j, parent in enumerate(chunk):
        i = first + j
        out.append(f"theorem parent{i} : nodeStepOK FreeXor.maskBasis TransposeFree.goals {lit(parent)} layer3 = true := by decide +kernel")
    out.append(f"def group{c:02d} : List (List Value) := [" + ",".join(lit(p) for p in chunk) + "]")
    out += [
        f"theorem group{c:02d}_all : (group{c:02d}.all fun xs => nodeStepOK FreeXor.maskBasis TransposeFree.goals xs layer3) = true := by",
        f"  simp only [group{c:02d}, List.all_cons, List.all_nil, Bool.and_true, " +
        ", ".join(f"parent{first+j}" for j in range(len(chunk))) + "]",
        "end HGP13.PrefixTreeDepth3Transpose",
    ]
    (here / f"{module}.lean").write_text("\n".join(out) + "\n", encoding="utf-8")
print("Generated", len(chunks), "chunks of at most", chunk_size, "parents")
