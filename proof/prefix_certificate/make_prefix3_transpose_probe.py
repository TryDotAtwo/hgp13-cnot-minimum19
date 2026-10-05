"""Create a kernel-checkable full depth-3 transition probe from candidate tree data."""
from pathlib import Path

here = Path(__file__).resolve().parent
source = (here / "PrefixTreeDepth3_transpose_parent500.lean").read_text(encoding="utf-8")
tree_lines = [line for line in source.splitlines() if line.startswith("def layer3")]
assert tree_lines and tree_lines[-1].startswith("def layer3 :")
base = [
    "import PrefixTreeDepth2Transpose",
    "namespace HGP13.PrefixTreeDepth3Transpose",
    "open HGP13.PrefixTreeCertificate HGP13.Catalogues",
    "set_option maxRecDepth 20000",
    "set_option maxHeartbeats 100000000",
] + tree_lines + ["end HGP13.PrefixTreeDepth3Transpose"]
(here / "PrefixTreeDepth3TransposeBase.lean").write_text("\n".join(base) + "\n", encoding="utf-8")
probe = [
    "import PrefixTreeDepth3TransposeBase",
    "namespace HGP13.PrefixTreeDepth3Transpose",
    "open HGP13.PrefixTreeCertificate HGP13.Catalogues",
    "set_option maxRecDepth 20000",
    "set_option maxHeartbeats 100000000",
    "theorem step23 : stepOK FreeXor.maskBasis TransposeFree.goals",
    "    PrefixTreeDepth2.layer2 layer3 = true := by decide +kernel",
    "end HGP13.PrefixTreeDepth3Transpose",
]
(here / "PrefixTreeDepth3TransposeProbe.lean").write_text("\n".join(probe) + "\n", encoding="utf-8")
print("Depth-3 tree defs:", len(tree_lines))
