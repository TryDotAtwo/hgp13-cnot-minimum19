"""Scratch prefix tree that imports only SharedSearch, not a sector graph."""
from pathlib import Path
import hashlib

root = Path(__file__).resolve().parent
lines = (root / "catalogue_keys.txt").read_text(encoding="utf-8").splitlines()
keys = {3: [], 4: []}
for line in lines:
    orientation, size, value = map(int, line.split())
    if orientation == 0:
        keys[size].append(value)
assert len(keys[3]) == 524 and len(keys[4]) == 40022
assert all(values == sorted(set(values)) for values in keys.values())


def tree(values):
    if not values:
        return ".nil"
    mid = len(values) // 2
    return f"(.node {tree(values[:mid])} {values[mid]} {tree(values[mid + 1:])})"


def definitions(name, values):
    if len(values) <= 512:
        return f"def {name} : Tree := {tree(values)}\n"
    mid = len(values) // 2
    return (
        definitions(name + "_l", values[:mid])
        + definitions(name + "_r", values[mid + 1:])
        + f"def {name} : Tree := .node {name}_l {values[mid]} {name}_r\n"
    )


code = (
    "import PrefixKeyTree\n"
    "namespace HGP13.OriginalPrefixesLite\n"
    "open HGP13.PrefixKeyTree (Tree)\n"
    + definitions("prefix3", keys[3])
    + definitions("prefix4", keys[4])
    + "def lookup (k x : Nat) : Bool :=\n"
    "  HGP13.PrefixKeyTree.lookup (if k ≤ 3 then prefix3 else prefix4) x\n"
    "end HGP13.OriginalPrefixesLite\n"
)
(root / "OriginalPrefixesLite.lean").write_text(code, encoding="utf-8")
for name in ("SectorScaleProbe0", "SectorScaleProbe315", "SectorScaleImportOnly"):
    text = (root / f"{name}.lean").read_text(encoding="utf-8")
    text = text.replace("OriginalPrefixes", "OriginalPrefixesLite")
    (root / f"{name}Lite.lean").write_text(text, encoding="utf-8")
print("OriginalPrefixesLite", len(code), "bytes", hashlib.sha256(code.encode()).hexdigest())
