import json, hashlib
from pathlib import Path
P=Path(__file__).parent
lines=(P/'exported.txt').read_text().splitlines()
prefix=sorted(int(s.split()[1]) for s in lines if s.startswith('PREFIX '))
layers={}
for line in lines:
    if not line.startswith('STATE '): continue
    v=list(map(int,line.split()[1:])); d=v[0]
    hist=sum(v[6+i]<<(64*i) for i in range(8))
    st=tuple(v[1:5])+ (hist,) +tuple(v[14:18])
    assert v[5]==0 and st[-1]==0
    layers.setdefault(d,[]).append(st)
for d in layers: layers[d].sort()
goals=[21,62,104,17,50,96,67]
want=[4,8,67,224]; fixed=[1,2,16,32]; passive=goals[:5]
def has(h,v): return (h>>v)&1
base=[0,1,2,4,8,16,32,64]
def encode(a):
    x=0
    for v in a:x=x*128+v
    return x
def step(d,s,t,j):
    if j==t:return None
    rows=list(s[:4]); hist,changed,returned,copied,extra=s[4:]
    v=rows[t]^(rows[j] if j<4 else fixed[j-4]); p=v&127
    if not v:return None
    mand=False
    if t<2:
        changed|=1<<t
        if v==[4,8][t] and has(s[5],t) and not has(returned,t):
            returned|=1<<t; mand=True
    if t==3 and rows[t]&127==0 and p!=0 and not copied:
        copied=1;mand=True
    old=(hist|(hist>>128))&((1<<128)-1)
    seen=p in base or has(old,p)
    if seen and not mand:return None
    aux=[a for a in range(1,128) if has(old,a) and a not in base+goals]
    if not seen and p not in goals:aux.append(p)
    if len(aux)>3 or encode(sorted(aux)) not in prefix:return None
    rows[t]=v; hist|=1<<v
    known=(hist|(hist>>128))&((1<<128)-1)
    for i in [2,3]:
        f=want[i]&127
        if not has(known,f) or rows[i]==want[i]:continue
        if i==2 or rows[i]&127!=0 or f not in rows:return None
    if any(has(known,f) and not has(hist,f) for f in passive):return None
    dif=[rows[i]^want[i] for i in range(4) if rows[i]!=want[i]]
    missing=set(x for x in dif if x not in rows+want+fixed)
    untouched=2-sum(has(changed,i) for i in range(2))
    bound=max(len(dif)+2*untouched,len(dif)+(len(missing)+1)//2)
    if d+1+bound>13:return None
    return tuple(rows)+(hist,changed,returned,copied,0)
edges={}
for d,states in layers.items():
    reachable=set()
    for s in states:
        out=[z for t in range(4) for j in range(8) if (z:=step(d,s,t,j)) is not None]
        edges[d,s]=out; reachable.update(out)
        assert list(s[:4])!=want or s[5]!=3
    assert reachable==set(layers.get(d+1,[])),d
print('Independent transition reproduction:',[len(layers[d]) for d in layers],flush=True)
def tree(a):
    if not a:return '.nil'
    m=len(a)//2
    return f'(.node {tree(a[:m])} {a[m]} {tree(a[m+1:])})'
def lit(s):return '⟨'+', '.join(map(str,s[:-1]))+'⟩'
head='''import Std
namespace HGP13.SectorPilot284
/- Experimental finite graph. Its correspondence to all short full words is OPEN.
   Transpose orientation, active sources [2,3], relay [5], depth cap 13.
   Catalogue prefix completeness and pruning soundness are NOT assumed proved. -/
structure State where
  a : Nat
  b : Nat
  c : Nat
  r : Nat
  hist : Nat
  changed : Nat
  returned : Nat
  copied : Nat
  deriving DecidableEq, Repr
inductive Tree where
  | nil
  | node (left : Tree) (key : Nat) (right : Tree)
def lookup : Tree → Nat → Bool
  | .nil, _ => false
  | .node l k r, x => if x < k then lookup l x else if x = k then true else lookup r x
def has (h v : Nat) : Bool := ((h >>> v) &&& 1) == 1
def set (h v : Nat) : Nat := h ||| (1 <<< v)
def rows (s : State) := [s.a,s.b,s.c,s.r]
def projected (h : Nat) := (h ||| (h >>> 128)) &&& ((1 <<< 128)-1)
def base := [0,1,2,4,8,16,32,64]
def goals := [21,62,104,17,50,96,67]
def want := [4,8,67,224]
def fixed := [1,2,16,32]
def passive := [21,62,104,17,50]
def ins (x : Nat) : List Nat → List Nat
  | [] => [x]
  | a :: r => if x ≤ a then x :: a :: r else a :: ins x r
def sort : List Nat → List Nat
  | [] => []
  | a :: r => ins a (sort r)
def encode (l : List Nat) := l.foldl (fun a b => a*128+b) 0
'''
head+='def prefixes : Tree := '+tree(prefix)+'\n'
head+='''def move (depth : Nat) (s : State) (t j : Nat) : Option State := Id.run do
  if j == t then return none
  let rs := rows s
  let control := if j < 4 then rs[j]! else fixed[j-4]!
  let v := rs[t]! ^^^ control
  let p := v &&& 127
  if v == 0 then return none
  let changed := if t < 2 then set s.changed t else s.changed
  let ret := t < 2 && v == [4,8][t]! && has s.changed t && !has s.returned t
  let copy := t == 3 && rs[t]! &&& 127 == 0 && p != 0 && s.copied == 0
  let returned := if ret then set s.returned t else s.returned
  let copied := if copy then 1 else s.copied
  let old := projected s.hist
  let seen := base.contains p || has old p
  if seen && !(ret || copy) then return none
  let aux := (List.range 128).filter (fun a => a != 0 && has old a && !base.contains a && !goals.contains a)
  let enlarged := if !seen && !goals.contains p then p :: aux else aux
  if enlarged.length > 3 || !lookup prefixes (encode (sort enlarged)) then return none
  let rs := rs.set t v
  let hist := set s.hist v
  let known := projected hist
  if ([2,3].any fun i =>
      let f := want[i]! &&& 127
      has known f && rs[i]! != want[i]! &&
        (i == 2 || rs[i]! &&& 127 != 0 || !rs.contains f)) then return none
  if passive.any (fun f => has known f && !has hist f) then return none
  let delta := ((List.range 4).filter (fun i => rs[i]! != want[i]!)).map (fun i => rs[i]! ^^^ want[i]!)
  let missing := (delta.filter (fun v => !(rs ++ want ++ fixed).contains v)).eraseDups
  let untouched := ((List.range 2).filter (fun i => !has changed i)).length
  let bound := max (delta.length+2*untouched) (delta.length+(missing.length+1)/2)
  if depth+1+bound > 13 then return none
  return some ⟨rs[0]!,rs[1]!,rs[2]!,rs[3]!,hist,changed,returned,copied⟩
def next (d : Nat) (s : State) : List State :=
  (List.range 4).flatMap fun t => (List.range 8).filterMap fun j => move d s t j
def terminal (s : State) : Bool := s.changed == 3 && rows s == want
def Safe : Nat → Nat → State → Prop
  | 0, _, s => terminal s = false
  | k+1, d, s => terminal s = false ∧ ∀ z ∈ next d s, Safe k (d+1) z

theorem safe_succ (k d : Nat) (s : State) (zs : List State)
    (ht : terminal s = false) (he : next d s = zs)
    (hs : ∀ z ∈ zs, Safe k (d+1) z) : Safe (k+1) d s := by
  exact ⟨ht, fun z hz => hs z (he ▸ hz)⟩

inductive Reach : Nat → State → Nat → State → Prop where
  | refl (d s) : Reach d s 0 s
  | step {d s t k z} : t ∈ next d s → Reach (d+1) t k z → Reach d s (k+1) z

theorem safe_reach {d s k z} (h : Reach d s k z) :
    ∀ fuel, k ≤ fuel → Safe fuel d s → terminal z = false := by
  induction h with
  | refl d s =>
    intro fuel _ hs
    cases fuel with
    | zero => exact hs
    | succ n => exact hs.1
  | step ht hr ih =>
    intro fuel hk hs
    cases fuel with
    | zero => omega
    | succ n => exact ih n (by omega) (hs.2 _ ht)

'''
# Explicit per-state proof blocks use shared child constants. No hash or external oracle is trusted.
ids={(d,s):f's{d}_{i}' for d in layers for i,s in enumerate(layers[d])}
parts=[head]
for d in sorted(layers,reverse=True):
    for s in layers[d]:
        name=ids[d,s]; out=edges[d,s]
        children=[ids[d+1,z] for z in out]
        childlist='['+', '.join(children)+']'
        parts.append(f'def {name} : State := {lit(s)}\n')
        parts.append(f'theorem {name}_edges : next {d} {name} = {childlist} := by decide\n')
        parts.append(f'theorem {name}_safe : Safe {13-d} {d} {name} := by\n')
        parts.append(f'  apply safe_succ {12-d} {d} {name} {childlist} (by decide) {name}_edges\n')
        if not children:parts.append('  simp\n')
        else:
            parts.append('  intro z hz\n  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz\n')
            # List membership reduces to equality, cases then substitute.
            parts.append('  rcases hz with '+ ' | '.join('h' for _ in children)+'\n')
            for child in children:parts.append(f'  · subst z; exact {child}_safe\n')
parts.append('theorem initial_safe : Safe 13 0 s0_0 := s0_0_safe\n')
parts.append('theorem no_terminal {k z} (h : Reach 0 s0_0 k z) (hk : k ≤ 13) : terminal z = false := safe_reach h 13 hk initial_safe\n')
parts.append('#print axioms no_terminal\nend HGP13.SectorPilot284\n')
(P/'Pilot284.lean').write_text(''.join(parts),encoding='utf-8')
(P/'generator_report.json').write_text(json.dumps(dict(sector=284,layers=[len(layers[d]) for d in layers],states=sum(map(len,layers.values())),edges=sum(map(len,edges.values())),prefixes=len(prefix),source_bytes=(P/'Pilot284.lean').stat().st_size,full_word_correspondence_proved=False),indent=2))
print((P/'generator_report.json').read_text())
