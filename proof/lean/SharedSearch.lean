import ProjectedHistory

/- Candidate shared transition specification. Not an accepted completeness theorem.
   The fixed pilot remains unchanged until a specialization theorem is proved. -/
namespace HGP13.SharedSearch
open PackedRows

structure Config where
  sources : List Nat
  relays : List Nat
  goals : List Nat
  prefixAccept : Nat → Nat → Bool

structure State where
  rows : List Nat
  history : Nat
  changed : Nat
  returned : Nat
  copied : Nat
  extra : Nat
  deriving DecidableEq, Repr

def fixed (c : Config) := (List.range 6).filter (fun i => !c.sources.contains i) |>.map (fun i => 2^i)
def want (c : Config) := c.sources.map (fun i => 2^i) ++ [c.goals[6]!] ++
  c.relays.zipIdx.map (fun (j,k) => 2^(7+k) ^^^ c.goals[j]!)
def passive (c : Config) := ((List.range 6).filter (fun j => !c.relays.contains j)).map (fun j => c.goals[j]!)
def count (c : Config) := c.sources.length+1+c.relays.length
def maxDepth (c : Config) := 12+c.relays.length
def base := [0,1,2,4,8,16,32,64]
def projected (h : Nat) :=
  (h ||| (h >>> 128) ||| (h >>> 256) ||| (h >>> 384)) &&& (2^128-1)
def insert (x : Nat) : List Nat → List Nat
  | [] => [x]
  | a :: r => if x ≤ a then x :: a :: r else a :: insert x r
def sort : List Nat → List Nat
  | [] => []
  | a :: r => insert a (sort r)
def encode (xs : List Nat) := (sort xs).foldl (fun a b => a*128+b) 0

def initial (c : Config) : State :=
  ⟨c.sources.map (fun i => 2^i) ++ [64] ++
      (List.range c.relays.length).map (fun i => 2^(7+i)),
    encodeHistory ((List.range (7+c.relays.length)).map (fun i => 2^i)),0,0,0,0⟩

def move (c : Config) (depth : Nat) (s : State) (t j : Nat) : Option State := Id.run do
  if t ≥ count c || j ≥ count c + (fixed c).length || j == t then return none
  let control := if j < count c then s.rows[j]! else (fixed c)[j-count c]!
  let value := s.rows[t]! ^^^ control
  let p := value &&& 127
  if value == 0 then return none
  let ns := c.sources.length
  let changed := if t < ns then remember s.changed t else s.changed
  let ret := t < ns && value == 2^(c.sources[t]!) && has s.changed t && !has s.returned t
  let copy := t > ns && s.rows[t]! &&& 127 == 0 && p != 0 && !has s.copied (t-ns-1)
  let returned := if ret then remember s.returned t else s.returned
  let copied := if copy then remember s.copied (t-ns-1) else s.copied
  let old := projected s.history
  let seen := base.contains p || has old p
  let extra := s.extra + if seen && !(ret || copy) then 1 else 0
  if extra > 2-ns then return none
  let aux := (List.range 128).filter (fun a => a != 0 && has old a && !base.contains a && !c.goals.contains a)
  let enlarged := if !seen && !c.goals.contains p then p :: aux else aux
  let capacity := 5-ns-extra
  if enlarged.length > capacity || !c.prefixAccept (if capacity ≤ 3 then 3 else 4) (encode enlarged) then return none
  let rows := s.rows.set t value
  let history := remember s.history value
  if ns == 2 then
    let known := projected history
    if ((List.range (count c)).any fun i =>
        i ≥ ns &&
        let f := (want c)[i]! &&& 127
        has known f && rows[i]! != (want c)[i]! &&
          (i == ns || rows[i]! &&& 127 != 0 || !rows.contains f)) then return none
    if (passive c).any (fun f => has known f && !has history f) then return none
  let delta := ((List.range (count c)).filter (fun i => rows[i]! != (want c)[i]!)).map
    (fun i => rows[i]! ^^^ (want c)[i]!)
  let missing := (delta.filter (fun d => !(rows ++ want c ++ fixed c).contains d)).eraseDups
  let untouched := ((List.range ns).filter (fun i => !has changed i)).length
  let bound := max (delta.length+2*untouched) (delta.length+(missing.length+1)/2)
  if depth+1+bound > maxDepth c then return none
  return some ⟨rows,history,changed,returned,copied,extra⟩

def next (c : Config) (depth : Nat) (s : State) :=
  (List.range (count c)).flatMap fun t =>
    (List.range (count c+(fixed c).length)).filterMap fun j => move c depth s t j

/-- Core endpoint only. Full acceptance additionally requires the passive completion cost. -/
def terminal (c : Config) (s : State) : Bool :=
  s.changed == 2^c.sources.length-1 && s.rows == want c

open SectorCover SectorCoordinates ProjectedHistory in
def ofSector (s : Sector) (lookup : Nat → Nat → Bool) : Config :=
  ⟨s.active.map Fin.val, s.carriers.map Budget.privateOutputs.idxOf,
    (projectedGoals s).map BitVec.toNat, lookup⟩

open SectorCover SectorCoordinates ProjectedHistory in
def InitialAgreement (s : Sector) : Prop :=
  (initial (ofSector s (fun _ _ => true))).rows = initialRowLiterals s ∧
  (initial (ofSector s (fun _ _ => true))).history = initialLiterals s ∧
  fixed (ofSector s (fun _ _ => true)) = fixedLiterals s ∧
  want (ofSector s (fun _ _ => true)) = targetRowLiterals s

instance (s : SectorCover.Sector) : Decidable (InitialAgreement s) := by
  unfold InitialAgreement
  infer_instance

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem initial_agreements_checked :
    SectorCover.sectors.all (fun s => decide (InitialAgreement s)) = true := by decide

theorem initial_agreement (s : SectorCover.Sector) (hs : s ∈ SectorCover.sectors) :
    InitialAgreement s :=
  of_decide_eq_true (List.all_eq_true.mp initial_agreements_checked s hs)

open SectorCover SectorCoordinates ProjectedHistory in
theorem initial_matches_full_matrix (s : Sector) (hs : s ∈ sectors)
    (lookup : Nat → Nat → Bool) :
    (initial (ofSector s lookup)).rows = rowCodes s identity ∧
    (initial (ofSector s lookup)).history = initialBits s ∧
    fixed (ofSector s lookup) = initialFixedCodes s ∧
    want (ofSector s lookup) = rowCodes s (goal s) := by
  obtain ⟨ha,hb,hc,hd⟩ := initial_agreement s hs
  obtain ⟨he,hf,hg,hh⟩ := sector_literals s hs
  exact ⟨ha.trans hf.symm,hb.trans he.symm,hc.trans hg.symm,hd.trans hh.symm⟩

theorem next_iff (c : Config) (depth : Nat) (s z : State) :
    z ∈ next c depth s ↔ ∃ t, t < count c ∧
      ∃ j, j < count c + (fixed c).length ∧ move c depth s t j = some z := by
  simp [next,List.mem_flatMap,List.mem_filterMap]

end HGP13.SharedSearch
