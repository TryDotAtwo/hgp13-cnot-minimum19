"""Untrusted witness-path exporter for 25 third-layer prefix obligations."""
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
for _ in range(3):
    layers.append(sorted({tuple(sorted(xs + (z,)))
                          for xs in layers[-1] for z in successors(xs)}))
assert list(map(len,layers)) == [1,39,970,20125]
layer3 = layers[3]

def path(xs, vals):
    m = len(vals)//2
    if xs == vals[m]:
        return ".here"
    if xs < vals[m]:
        return f"(.left {path(xs, vals[:m])})"
    return f"(.right {path(xs, vals[m+1:])})"

def lit(xs):
    return "[" + ",".join(f"({v} : Value)" for v in xs) + "]"

out = [
    "import PrefixPathWitness",
    "import PrefixTreeDepth3TransposeBase",
    "namespace HGP13.PrefixPathProbe",
    "open HGP13.PrefixPathWitness HGP13.PrefixTreeDepth3Transpose HGP13.Catalogues",
    "set_option maxRecDepth 20000",
    "set_option maxHeartbeats 100000000",
]
for i, parent in enumerate(layers[2][:25]):
    children = [tuple(sorted(parent + (z,))) for z in successors(parent)]
    paths = [path(child, layer3) for child in children]
    out.append(f"def paths{i} : List Path := [" + ",".join(paths) + "]")
    out.append(f"theorem checked{i} : checkNode FreeXor.maskBasis TransposeFree.goals {lit(parent)} layer3 paths{i} = true := by decide +kernel")
out.append("end HGP13.PrefixPathProbe")
target = here / "PrefixPathProbe.lean"
target.write_text("\n".join(out)+"\n",encoding="utf-8")
print(target, target.stat().st_size, "bytes")
