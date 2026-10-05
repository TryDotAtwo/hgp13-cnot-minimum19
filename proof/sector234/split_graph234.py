"""Split the generated Lean graph certificate by depth to bound elaboration RAM."""
import re
from pathlib import Path

here = Path(__file__).resolve().parent
source = (here / "Graph234.lean").read_text(encoding="utf-8")
marks = [(int(m.group(1)), m.start()) for m in re.finditer(r"(?m)^def s(\d+)_0 : State", source)]
assert [d for d, _ in marks] == list(range(11, -1, -1))
base = source[:marks[0][1]] + "end HGP13.SectorGraph234\n"
(here / "Graph234Base.lean").write_text(base, encoding="utf-8")
for i, (depth, start) in enumerate(marks):
    end = marks[i + 1][1] if i + 1 < len(marks) else len(source)
    body = source[start:end].removesuffix("end HGP13.SectorGraph234\n")
    prev = "Graph234Base" if depth == 11 else f"Graph234Layer{depth + 1}"
    module = (f"import {prev}\nnamespace HGP13.SectorGraph234\n"
              "open SharedSearch\nset_option maxRecDepth 20000\n"
              "set_option maxHeartbeats 2000000\n" + body +
              "end HGP13.SectorGraph234\n")
    (here / f"Graph234Layer{depth}.lean").write_text(module, encoding="utf-8")
print("Split", len(marks), "layers; largest", max((here / f"Graph234Layer{d}.lean").stat().st_size for d, _ in marks), "bytes")
