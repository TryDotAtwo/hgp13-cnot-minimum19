"""Generate explicit terminal-cost certificates, not a graph-coverage proof."""
import json
from pathlib import Path

p = Path(__file__).parent
data = json.loads((p / 'potential359.json').read_text())
lift = lambda v: (v & 63) | ((v & 64) << 2)
out = [(p / 'PackedTerminalPotential.lean').read_text(),
       'namespace HGP13.SectorTerminal359',
       'set_option maxRecDepth 20000',
       'open PackedTerminalPotential',
       '/- Only the listed terminal histories are certified. Search coverage remains OPEN. -/',
       'def targets : List Row := [' + ','.join(str(lift(v)) for v in [21,62,104,17,50,96]) + ']']
for i, t in enumerate(data['terminals']):
    out += [
        f'def history{i} : List Row := [' + ','.join(str(lift(v)) for v in t['available']) + ']',
        f'def table{i} : Nat := ' + str(sum(min(3,x) << (2*j) for j,x in enumerate(t['potential']))),
        'set_option maxHeartbeats 2000000 in',
        f'theorem checked{i} : check history{i} table{i} = true := by decide',
        f'theorem bound{i} : 18 < {t["depth"]} + (targets.map (fun z => tableWeight table{i} (Projection.project z))).sum := by decide',
        f'theorem excludes{i} (costs : Row → Nat)',
        f'    (hc : ∀ z ∈ targets, PassiveCost.cost history{i} z = some (costs z)) :',
        f'    18 < {t["depth"]} + (targets.map costs).sum :=',
        f'  excludes_completion history{i} targets table{i} {t["depth"]} costs checked{i} hc bound{i}'
    ]
out += ['end HGP13.SectorTerminal359']
(p / 'PackedTerminal359.lean').write_text('\n'.join(out) + '\n', encoding='utf-8')
print('Generated 36 terminal histories and 108 proof obligations.')
