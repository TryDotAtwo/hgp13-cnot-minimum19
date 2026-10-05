"""Glue exact 8-bit terminal histories to the checked potential bounds."""
import json
from pathlib import Path

here = Path(__file__).resolve().parent
records = json.loads((here / "pilot234_replay_report.json").read_text())["terminal_costs"]
out = ["""import Graph234Layer0
import Sector234Potentials
namespace HGP13.SectorCost234
open SharedSearch SectorGraph234
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
def decode (h : Nat) : List Row :=
  ((List.range 256).filter (fun v => PackedRows.has h v)).map
    (fun v => Sector234Encoding.liftMask (BitVec.ofNat 8 v))
"""]
for i, item in enumerate(records):
    out.append(f"theorem decode{i} : decode {item['history']} = Sector234Potentials.history{i} := by decide\n")
out += ["""theorem key_cost (depth history : Nat) (costs : Row → Nat)
    (hk : (depth,history) ∈ SectorGraph234.keys)
    (hc : ∀ z ∈ Sector234Potentials.targets,
      PassiveCost.cost (decode history) z = some (costs z)) :
    18 < depth + (Sector234Potentials.targets.map costs).sum := by
  simp only [SectorGraph234.keys,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with """ + " | ".join("hk" for _ in records) + "\n"]
for i in range(len(records)):
    out += ["""  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
""" + f"    exact Sector234Potentials.excludes{i} costs (by simpa only [decode{i}] using hc)\n"]
out += ["""theorem no_cheap_terminal {k : Nat} {z : State}
    (reach : SectorGraph234.Reach 0 (initial SectorGraph234.config) k z)
    (length : k ≤ 13)
    (terminal : SharedSearch.terminal SectorGraph234.config z = true)
    (costs : Row → Nat)
    (hc : ∀ r ∈ Sector234Potentials.targets,
      PassiveCost.cost (decode z.history) r = some (costs r)) :
    18 < k + (Sector234Potentials.targets.map costs).sum :=
  key_cost k z.history costs (reachable_terminal_key reach length terminal) hc
end HGP13.SectorCost234
"""]
path = here / "SectorCost234.lean"
path.write_text("".join(out), encoding="utf-8")
print(path, path.stat().st_size)
