"""Generate untrusted closed-set witnesses; Lean checks every witness and case.

No search result is imported as an axiom. The proof covers arbitrary program
lengths using TransposeFree.potential_required and cut_preserved.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
P = {0, 1, 2, 4, 8, 16, 32, 64}
F = [21, 62, 104, 17, 50, 96, 67]
B = P | set(F)

def potential(x, y):
    return all(any(a not in (0,z) and a ^ z in (x,y) for a in B)
               or x ^ y == z for z in [50,62,67])

def closure(x, y):
    seen = set(P)
    allowed = B | {x,y}
    while True:
        nxt = seen | {a ^ b for a in seen for b in seen if a ^ b in allowed}
        if nxt == seen:
            return sorted(seen), next(z for z in F if z not in seen)
        seen = nxt

lines = ['import TransposeFree', '', 'namespace HGP13.TransposeCertificate',
         'open HGP13.TransposeFree', 'set_option maxRecDepth 20000',
         'set_option maxHeartbeats 2000000', '']
count = 0
for x in range(128):
    name = f'row{x:03}'
    lines.append(f'def {name} (y : BitVec 7) : Cut := match y.toNat with')
    for y in range(128):
        if not potential(x,y):
            continue
        values,missing = closure(x,y)
        count += 1
        lines.append(f'  | {y} => ⟨[' + ','.join(map(str,values)) + f'],{missing}⟩')
    lines.append('  | _ => default')
    lines.append(f'theorem checked{x:03} : ∀ y : BitVec 7, fastPotential {x} y = true →')
    lines.append(f'    check {x} y ({name} y) = true := by decide')
    lines.append('')
lines += ['def certificate (x y : BitVec 7) : Cut := match x.toNat with']
for x in range(128):
    lines.append(f'  | {x} => row{x:03} y')
lines += ['  | _ => default', '', 'theorem word_cases : ∀ x : BitVec 7,']
lines.append('    x ∈ [' + ','.join(map(str,range(128))) + '] := by decide')
lines += ['', 'theorem all_checked (x y : BitVec 7) (h : fastPotential x y = true) :',
          '    check x y (certificate x y) = true := by',
          '  have hx := word_cases x',
          '  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx',
          '  rcases hx with ' + ' | '.join('rfl' for _ in range(128))]
for x in range(128):
    lines.append(f'  · exact checked{x:03} y h')
lines += ['', 'theorem two_extras_impossible (p : List (BitVec 7)) (x y : BitVec 7)',
          '    (hv : FreeXor.validMasks initial p = true) (bounded : p ⊆ allowed x y)',
          '    (reaches : goals ⊆ initial ++ p) : False := by',
          '  have hp := potential_required p x y hv bounded reaches',
          '  rw [fastPotential_correct] at hp',
          '  exact checked_cut_excludes x y (certificate x y) (all_checked x y hp)',
          '    p hv bounded reaches', '', 'end HGP13.TransposeCertificate', '']
(ROOT/'lean/TransposeCertificate.lean').write_text('\n'.join(lines),encoding='utf-8')
print(f'Generated {count} checked cuts ({count//2} unordered pairs).')
