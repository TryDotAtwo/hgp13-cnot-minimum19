"""Candidate optimization: prove projected auxiliary list once per state.

Still uses kernel reduction for every transition. Leaves the accepted pilot
source unchanged. Do not promote this candidate until its full check passes.
"""
import re
from pathlib import Path
p=Path(__file__).parent
s=(p/'Pilot284.lean').read_text(encoding='utf-8')
s=s.replace('namespace HGP13.SectorPilot284','namespace HGP13.SectorPilot284Cached')
s=s.replace('end HGP13.SectorPilot284','end HGP13.SectorPilot284Cached')
aux='(List.range 128).filter (fun a => a != 0 && has old a && !base.contains a && !goals.contains a)'
assert s.count('let aux := '+aux)==1
s=s.replace('def move (depth : Nat)', 'def auxiliary (s : State) : List Nat :=\n  let old := projected s.hist\n  '+aux+'\ndef moveWith (aux : List Nat) (depth : Nat)')
s=s.replace('  let aux := '+aux+'\n','')
s=s.replace('def next (d : Nat) (s : State) : List State :=\n  (List.range 4).flatMap fun t => (List.range 8).filterMap fun j => move d s t j',
'''def nextWith (d : Nat) (s : State) (aux : List Nat) : List State :=
  (List.range 4).flatMap fun t => (List.range 8).filterMap fun j => moveWith aux d s t j
def next (d : Nat) (s : State) : List State := nextWith d s (auxiliary s)''')
base=[0,1,2,4,8,16,32,64];goals=[21,62,104,17,50,96,67]
def proof(m):
    declaration,name,values,edge=m.groups()
    hist=int(values.split(',')[4].strip())
    old=(hist|(hist>>128))&((1<<128)-1)
    a=[v for v in range(128) if v and (old>>v)&1 and v not in base+goals]
    return declaration+f'theorem {name}_aux : auxiliary {name} = {a} := by decide\n'+edge.replace(':= by decide',f':= by\n  unfold next\n  rw [{name}_aux]\n  decide')+'\n'
s=re.sub(r'(def (s\d+_\d+) : State := ⟨([^\n]+)⟩\n)(theorem [^\n]+_edges[^\n]+:= by decide)\n',proof,s)
(p/'Cached.lean').write_text(s,encoding='utf-8')
print('Candidate written:',(p/'Cached.lean').stat().st_size,'bytes')
