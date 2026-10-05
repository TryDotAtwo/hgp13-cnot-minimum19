import json
from pathlib import Path

p = Path(__file__).parent
lines = (p/'graph359.txt').read_text().splitlines()
prefix = {k:sorted(int(s.split()[1]) for s in lines if s.startswith(f'PREFIX{k} ')) for k in [3,4]}
sets = {k:set(v) for k,v in prefix.items()}
layers = {}
for line in lines:
    if not line.startswith('STATE '): continue
    v=list(map(int,line.split()[1:]))
    assert v[3:6] == [0,0,0] and v[16] == 0
    hist=sum(v[6+i]<<(64*i) for i in range(8))
    assert hist >> 128 == 0
    state=tuple(v[1:3])+ (hist,v[14],v[15],v[16],v[17])
    layers.setdefault(v[0],[]).append(state)
for d in layers: layers[d].sort()
goals=[21,62,104,17,50,96,67]
fixed=[1,2,8,16,32]
want=[4,67]
base=[0,1,2,4,8,16,32,64]

def encode(xs):
    n=0
    for x in sorted(xs):n=n*128+x
    return n

def move(d,s,t,j):
    if t==j:return None
    rows=list(s[:2]);hist,changed,returned,copied,extra=s[2:]
    value=rows[t]^(rows[j] if j<2 else fixed[j-2])
    if value==0:return None
    ret=t==0 and value==4 and changed&1 and not returned&1
    if t==0:changed|=1
    if ret:returned|=1
    seen=value in base or (hist>>value)&1
    if seen and not ret:extra+=1
    if extra>1:return None
    aux=[x for x in range(1,128) if (hist>>x)&1 and x not in base+goals]
    if not seen and value not in goals:aux.append(value)
    capacity=4-extra
    if len(aux)>capacity or encode(aux) not in sets[capacity]:return None
    rows[t]=value;hist|=1<<value
    delta=[rows[i]^want[i] for i in range(2) if rows[i]!=want[i]]
    missing=set(x for x in delta if x not in rows+want+fixed)
    bound=max(len(delta)+2*(not changed&1),len(delta)+(len(missing)+1)//2)
    if d+1+bound>12:return None
    return tuple(rows)+(hist,changed,returned,copied,extra)

edges={};terminal_keys=set()
for d,states in layers.items():
    seen=set()
    for s in states:
        children=[z for t in range(2) for j in range(7) if (z:=move(d,s,t,j)) is not None]
        edges[d,s]=children;seen.update(children)
        if list(s[:2])==want and s[3]==1:terminal_keys.add((d,s[2]))
    assert seen==set(layers.get(d+1,[])),d
terminal_data=json.loads((p/'potential359.json').read_text())['terminals']
keys=[(t['depth'],t['history']) for t in terminal_data]
assert terminal_keys==set(keys) and len(keys)==36

def tree(xs):
    if not xs:return '.nil'
    m=len(xs)//2
    return f'(.node {tree(xs[:m])} {xs[m]} {tree(xs[m+1:])})'

head='''import SharedSearch
namespace HGP13.SectorGraph359
open SharedSearch
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
/- A graph certificate for the shared transition specification.
   Completeness for arbitrary full CNOT words remains OPEN. -/
inductive Tree where
  | nil
  | node : Tree → Nat → Tree → Tree
def lookup : Tree → Nat → Bool
  | .nil, _ => false
  | .node l a r, x => if x == a then true else if x < a then lookup l x else lookup r x
'''
def tree_defs(name,xs):
    if len(xs) <= 512:return f'def {name} : Tree := {tree(xs)}\n'
    m=len(xs)//2
    return (tree_defs(name+'_l',xs[:m])+tree_defs(name+'_r',xs[m+1:])+
            f'def {name} : Tree := .node {name}_l {xs[m]} {name}_r\n')
for k in [3,4]:head+=tree_defs(f'prefix{k}',prefix[k])
head+='''def config : Config := ⟨[2], [], [21,62,104,17,50,96,67],
  fun k x => lookup (if k ≤ 3 then prefix3 else prefix4) x⟩
'''
head+='def keys : List (Nat × Nat) := ['+', '.join(f'({d},{h})' for d,h in keys)+']\n'
head+='''def Covered (d : Nat) (s : State) : Prop :=
  terminal config s = true → (d,s.history) ∈ keys
instance (d : Nat) (s : State) : Decidable (Covered d s) := by
  unfold Covered
  infer_instance
def Safe : Nat → Nat → State → Prop
  | 0, d, s => Covered d s
  | k+1, d, s => Covered d s ∧ ∀ z ∈ next config d s, Safe k (d+1) z
theorem safe_succ (k d : Nat) (s : State) (zs : List State)
    (ht : Covered d s) (he : next config d s = zs)
    (hs : ∀ z ∈ zs, Safe k (d+1) z) : Safe (k+1) d s := by
  exact ⟨ht, fun z hz => hs z (he ▸ hz)⟩
inductive Reach : Nat → State → Nat → State → Prop where
  | refl (d s) : Reach d s 0 s
  | step {d s t k z} : t ∈ next config d s → Reach (d+1) t k z → Reach d s (k+1) z
theorem safe_reach {d s k z} (h : Reach d s k z) :
    ∀ fuel, k ≤ fuel → Safe fuel d s → Covered (d+k) z := by
  induction h with
  | refl d s =>
    intro fuel _ hs
    cases fuel with
    | zero => exact hs
    | succ n => exact hs.1
  | @step d s t k z ht hr ih =>
    intro fuel hk hs
    cases fuel with
    | zero => omega
    | succ n =>
      have h := ih n (by omega) (hs.2 _ ht)
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
'''
ids={(d,s):f's{d}_{i}' for d in layers for i,s in enumerate(layers[d])}
out=[head]
for d in sorted(layers,reverse=True):
    for s in layers[d]:
        name=ids[d,s];children=[ids[d+1,z] for z in edges[d,s]]
        childlist='['+', '.join(children)+']'
        literal='⟨['+','.join(map(str,s[:2]))+'], '+', '.join(map(str,s[2:]))+'⟩'
        out += [f'def {name} : State := {literal}\n',
                f'theorem {name}_edges : next config {d} {name} = {childlist} := by decide\n',
                f'theorem {name}_safe : Safe {12-d} {d} {name} := by\n',
                f'  apply safe_succ {11-d} {d} {name} {childlist} (by decide) {name}_edges\n']
        if not children:out.append('  simp\n')
        else:
            out += ['  intro z hz\n  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz\n',
                    '  rcases hz with '+' | '.join('h' for _ in children)+'\n']
            out += [f'  · subst z; exact {child}_safe\n' for child in children]
out += ['theorem initial_eq : initial config = s0_0 := by decide\n',
        'theorem initial_safe : Safe 12 0 (initial config) := by rw [initial_eq]; exact s0_0_safe\n',
        '''theorem reachable_terminal_key {k z} (h : Reach 0 (initial config) k z) (hk : k ≤ 12)
    (ht : terminal config z = true) : (k,z.history) ∈ keys := by
  have hc := safe_reach h 12 hk initial_safe
  simpa using hc ht
#print axioms reachable_terminal_key
end HGP13.SectorGraph359
''']
(p/'Graph359.lean').write_text(''.join(out),encoding='utf-8')
report=dict(states=sum(map(len,layers.values())),edges=sum(map(len,edges.values())),
            prefixes={k:len(v) for k,v in prefix.items()},terminals=len(keys),
            full_word_correspondence_proved=False)
(p/'graph359_report.json').write_text(json.dumps(report,indent=2))
print(report)
