import json
from pathlib import Path

p=Path(__file__).parent
ts=json.loads((p/'potential359.json').read_text())['terminals']
out=['''import SectorGraph359
import SectorTerminal359
namespace HGP13.SectorCost359
open SharedSearch SectorGraph359
set_option maxRecDepth 20000
def decode (h : Nat) : List Row :=
  ((List.range 128).filter (fun v => PackedRows.has h v)).map
    (fun v => BitVec.ofNat 13 ((v &&& 63) ||| ((v &&& 64) <<< 2)))
''']
for i,t in enumerate(ts):
    out.append(f'theorem decode{i} : decode {t["history"]} = SectorTerminal359.history{i} := by decide\n')
out.append('''theorem key_cost (depth history : Nat) (costs : Row → Nat)
    (hk : (depth,history) ∈ SectorGraph359.keys)
    (hc : ∀ z ∈ SectorTerminal359.targets, PassiveCost.cost (decode history) z = some (costs z)) :
    18 < depth + (SectorTerminal359.targets.map costs).sum := by
  simp only [SectorGraph359.keys,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with '''+' | '.join('hk' for _ in ts)+'\n')
for i,t in enumerate(ts):
    out.append(f'''  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes{i} costs (by simpa only [decode{i}] using hc)
''')
out.append('''theorem no_cheap_terminal {k : Nat} {z : State}
    (reach : SectorGraph359.Reach 0 (initial SectorGraph359.config) k z)
    (length : k ≤ 12) (terminal : SharedSearch.terminal SectorGraph359.config z = true)
    (costs : Row → Nat)
    (hc : ∀ r ∈ SectorTerminal359.targets, PassiveCost.cost (decode z.history) r = some (costs r)) :
    18 < k + (SectorTerminal359.targets.map costs).sum :=
  key_cost k z.history costs (reachable_terminal_key reach length terminal) hc
end HGP13.SectorCost359
''')
(p/'SectorCost359.lean').write_text(''.join(out),encoding='utf-8')
print('Generated terminal-history decoding and reachable cost exclusion bridge.')
