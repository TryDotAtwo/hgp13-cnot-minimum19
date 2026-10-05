import SharedSearch

namespace HGP13.TransitionChecks
open SharedSearch PackedRows

structure Proposal where
  state : State
  alphabetBad : Bool
  zeroBad : Bool
  extraBad : Bool
  catalogueBad : Bool
  coreBad : Bool
  passiveBad : Bool
  depthBad : Bool

def propose (c : Config) (depth : Nat) (s : State) (t j : Nat) : Proposal :=
  let control := if j < count c then s.rows[j]! else (fixed c)[j-count c]!
  let value := s.rows[t]! ^^^ control
  let p := value &&& 127
  let ns := c.sources.length
  let changed := if t < ns then remember s.changed t else s.changed
  let ret := t < ns && value == 2^(c.sources[t]!) && has s.changed t && !has s.returned t
  let copy := t > ns && s.rows[t]! &&& 127 == 0 && p != 0 && !has s.copied (t-ns-1)
  let returned := if ret then remember s.returned t else s.returned
  let copied := if copy then remember s.copied (t-ns-1) else s.copied
  let old := projected s.history
  let seen := base.contains p || has old p
  let extra := s.extra + if seen && !(ret || copy) then 1 else 0
  let aux := (List.range 128).filter (fun a => a != 0 && has old a && !base.contains a && !c.goals.contains a)
  let enlarged := if !seen && !c.goals.contains p then p :: aux else aux
  let capacity := 5-ns-extra
  let rows := s.rows.set t value
  let history := remember s.history value
  let known := projected history
  let badCore := ((List.range (count c)).any fun i =>
    i ≥ ns &&
    let f := (want c)[i]! &&& 127
    has known f && rows[i]! != (want c)[i]! &&
      (i == ns || rows[i]! &&& 127 != 0 || !rows.contains f))
  let badPassive := (passive c).any (fun f => has known f && !has history f)
  let delta := ((List.range (count c)).filter (fun i => rows[i]! != (want c)[i]!)).map
    (fun i => rows[i]! ^^^ (want c)[i]!)
  let missing := (delta.filter (fun d => !(rows ++ want c ++ fixed c).contains d)).eraseDups
  let untouched := ((List.range ns).filter (fun i => !has changed i)).length
  let bound := max (delta.length+2*untouched) (delta.length+(missing.length+1)/2)
  ⟨⟨rows,history,changed,returned,copied,extra⟩,
    t ≥ count c || j ≥ count c + (fixed c).length || j == t,
    value == 0, decide (extra > 2-ns),
    enlarged.length > capacity || !c.prefixAccept (if capacity ≤ 3 then 3 else 4) (encode enlarged),
    badCore,badPassive,decide (depth+1+bound > maxDepth c)⟩

def checked (two : Bool) (q : Proposal) : Option State :=
  if q.alphabetBad then none else
  if q.zeroBad then none else
  if q.extraBad then none else
  if q.catalogueBad then none else
  if two then
    if q.coreBad then none else
    if q.passiveBad then none else
    if q.depthBad then none else some q.state
  else
    if q.depthBad then none else some q.state

theorem move_eq_checked (c : Config) (depth : Nat) (s : State) (t j : Nat) :
    move c depth s t j = checked (c.sources.length == 2) (propose c depth s t j) := by
  simp only [move,checked,propose,decide_eq_true_eq,Id.run,pure]

def Admissible (two : Bool) (q : Proposal) : Prop :=
  q.alphabetBad = false ∧ q.zeroBad = false ∧ q.extraBad = false ∧
  q.catalogueBad = false ∧
  (two = true → q.coreBad = false ∧ q.passiveBad = false) ∧ q.depthBad = false

theorem checked_eq_some_iff (two : Bool) (q : Proposal) (z : State) :
    checked two q = some z ↔ Admissible two q ∧ z = q.state := by
  rcases q with ⟨state,a,b,c,d,e,f,g⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    cases e <;> cases f <;> cases g <;> cases two <;>
    simp [checked,Admissible,eq_comm]

theorem move_eq_some_iff (c : Config) (depth : Nat) (s z : State) (t j : Nat) :
    move c depth s t j = some z ↔
      Admissible (c.sources.length == 2) (propose c depth s t j) ∧
        z = (propose c depth s t j).state := by
  rw [move_eq_checked,checked_eq_some_iff]

theorem admissible_move (c : Config) (depth : Nat) (s : State) (t j : Nat)
    (h : Admissible (c.sources.length == 2) (propose c depth s t j)) :
    move c depth s t j = some (propose c depth s t j).state :=
  (move_eq_some_iff c depth s _ t j).mpr ⟨h,rfl⟩

theorem successful_move_rows (c : Config) (depth : Nat) (s z : State) (t j : Nat)
    (h : move c depth s t j = some z) :
    z.rows = s.rows.set t (s.rows[t]! ^^^
      if j < count c then s.rows[j]! else (fixed c)[j-count c]!) := by
  rw [((move_eq_some_iff c depth s z t j).mp h).2]
  rfl

theorem successful_move_history (c : Config) (depth : Nat) (s z : State) (t j : Nat)
    (h : move c depth s t j = some z) :
    z.history = remember s.history (s.rows[t]! ^^^
      if j < count c then s.rows[j]! else (fixed c)[j-count c]!) := by
  rw [((move_eq_some_iff c depth s z t j).mp h).2]
  rfl

theorem successful_move_changed (c : Config) (depth : Nat) (s z : State) (t j : Nat)
    (h : move c depth s t j = some z) :
    z.changed = if t < c.sources.length then remember s.changed t else s.changed := by
  rw [((move_eq_some_iff c depth s z t j).mp h).2]
  rfl

theorem admissible_indices (c : Config) (depth : Nat) (s : State) (t j : Nat)
    (h : Admissible (c.sources.length == 2) (propose c depth s t j)) :
    t < count c ∧ j < count c + (fixed c).length ∧ j ≠ t := by
  have hh := h.1
  simp [propose] at hh
  omega

/-- Labels use (target position, control position), matching move's argument order. -/
def advance (c : Config) (s : State) (g : Nat × Nat) : State :=
  (propose c 0 s g.1 g.2).state

theorem proposal_state_depth (c : Config) (depth : Nat) (s : State) (g : Nat × Nat) :
    (propose c depth s g.1 g.2).state = advance c s g := by rfl

def rawRun (c : Config) (s : State) : List (Nat × Nat) → State
  | [] => s
  | g :: p => rawRun c (advance c s g) p

def GuardsHold (c : Config) : Nat → State → List (Nat × Nat) → Prop
  | _, _, [] => True
  | depth, s, g :: p =>
      Admissible (c.sources.length == 2) (propose c depth s g.1 g.2) ∧
      GuardsHold c (depth+1) (advance c s g) p

inductive Path (c : Config) : Nat → State → List (Nat × Nat) → State → Prop where
  | nil (depth s) : Path c depth s [] s
  | cons {depth s g p t z} : move c depth s g.1 g.2 = some t →
      Path c (depth+1) t p z → Path c depth s (g :: p) z

theorem guards_path (c : Config) (depth : Nat) (s : State) (p : List (Nat × Nat))
    (h : GuardsHold c depth s p) : Path c depth s p (rawRun c s p) := by
  induction p generalizing depth s with
  | nil => exact Path.nil depth s
  | cons g p ih =>
    have hm := admissible_move c depth s g.1 g.2 h.1
    rw [proposal_state_depth] at hm
    exact Path.cons hm (ih (depth+1) (advance c s g) h.2)

theorem path_raw {c : Config} {depth : Nat} {s z : State} {p : List (Nat × Nat)}
    (h : Path c depth s p z) : z = rawRun c s p := by
  induction h with
  | nil => rfl
  | @cons depth s g p t z hm hp ih =>
    have ht := ((move_eq_some_iff c depth s t g.1 g.2).mp hm).2
    rw [proposal_state_depth] at ht
    simpa only [rawRun,ht] using ih

theorem raw_changed (c : Config) (s : State) (p : List (Nat × Nat)) (i : Nat) :
    has (rawRun c s p).changed i = true ↔
      has s.changed i = true ∨ ∃ g ∈ p, g.1 = i ∧ i < c.sources.length := by
  induction p generalizing s with
  | nil => simp [rawRun]
  | cons g p ih =>
    have hc : (advance c s g).changed =
        if g.1 < c.sources.length then remember s.changed g.1 else s.changed := rfl
    rw [rawRun,ih,hc]
    by_cases he : g.1 = i
    · subst i
      by_cases hlt : g.1 < c.sources.length <;>
        simp [hlt,has_remember,List.mem_cons]
    · by_cases hlt : g.1 < c.sources.length <;>
        simp [hlt,he,has_remember,List.mem_cons]

theorem first_event_bit (h v i : Nat) (event : Bool) :
    has (if event && !has h v then remember h v else h) i =
      (has h i || (event && decide (v = i))) := by
  by_cases he : v = i
  · subst i
    cases event <;> cases hb : has h v <;> simp [hb,has_remember]
  · cases event <;> cases hb : has h v <;> simp [hb,he,has_remember]

def value (c : Config) (s : State) (g : Nat × Nat) : Nat :=
  s.rows[g.1]! ^^^ if g.2 < count c then s.rows[g.2]! else (fixed c)[g.2-count c]!

def returnEvent (c : Config) (s : State) (g : Nat × Nat) : Bool :=
  g.1 < c.sources.length && value c s g == 2^(c.sources[g.1]!) && has s.changed g.1

def copyEvent (c : Config) (s : State) (g : Nat × Nat) : Bool :=
  g.1 > c.sources.length && s.rows[g.1]! &&& 127 == 0 && value c s g &&& 127 != 0

theorem advance_returned (c : Config) (s : State) (g : Nat × Nat) (i : Nat) :
    has (advance c s g).returned i =
      (has s.returned i || (returnEvent c s g && decide (g.1 = i))) :=
  first_event_bit s.returned g.1 i (returnEvent c s g)

theorem advance_copied (c : Config) (s : State) (g : Nat × Nat) (i : Nat) :
    has (advance c s g).copied i =
      (has s.copied i || (copyEvent c s g && decide (g.1-c.sources.length-1 = i))) :=
  first_event_bit s.copied (g.1-c.sources.length-1) i (copyEvent c s g)

def events (c : Config) (event : State → (Nat × Nat) → Bool)
    (index : (Nat × Nat) → Nat) (s : State) : List (Nat × Nat) → List Nat
  | [] => []
  | g :: p => if event s g then index g :: events c event index (advance c s g) p
      else events c event index (advance c s g) p

theorem raw_event_mask (c : Config) (event : State → (Nat × Nat) → Bool)
    (index : (Nat × Nat) → Nat) (mask : State → Nat)
    (step : ∀ s g i, has (mask (advance c s g)) i =
      (has (mask s) i || (event s g && decide (index g = i))))
    (s : State) (p : List (Nat × Nat)) (i : Nat) :
    has (mask (rawRun c s p)) i = true ↔
      has (mask s) i = true ∨ i ∈ events c event index s p := by
  induction p generalizing s with
  | nil => simp [rawRun,events]
  | cons g p ih =>
    rw [rawRun,ih,step]
    cases he : event s g with
    | false => simp [events,he]
    | true =>
      simp only [events,he,ite_true,Bool.true_and,
        Bool.or_eq_true,decide_eq_true_eq,List.mem_cons,or_assoc]
      rw [eq_comm (a := index g) (b := i)]

theorem raw_returned (c : Config) (s : State) (p : List (Nat × Nat)) (i : Nat) :
    has (rawRun c s p).returned i = true ↔
      has s.returned i = true ∨ i ∈ events c (returnEvent c) Prod.fst s p :=
  raw_event_mask c (returnEvent c) Prod.fst State.returned (advance_returned c) s p i

theorem raw_copied (c : Config) (s : State) (p : List (Nat × Nat)) (i : Nat) :
    has (rawRun c s p).copied i = true ↔
      has s.copied i = true ∨
        i ∈ events c (copyEvent c) (fun g => g.1-c.sources.length-1) s p :=
  raw_event_mask c (copyEvent c) (fun g => g.1-c.sources.length-1)
    State.copied (advance_copied c) s p i

theorem path_guards {c : Config} {depth : Nat} {s z : State} {p : List (Nat × Nat)}
    (h : Path c depth s p z) : GuardsHold c depth s p := by
  induction h with
  | nil => trivial
  | @cons depth s g p t z hm hp ih =>
    obtain ⟨ha,ht⟩ := (move_eq_some_iff c depth s t g.1 g.2).mp hm
    rw [proposal_state_depth] at ht
    exact ⟨ha,by simpa only [ht] using ih⟩

theorem path_iff {c : Config} {depth : Nat} {s z : State} {p : List (Nat × Nat)} :
    Path c depth s p z ↔ GuardsHold c depth s p ∧ z = rawRun c s p := by
  constructor
  · intro h
    exact ⟨path_guards h,path_raw h⟩
  · rintro ⟨h,rfl⟩
    exact guards_path c depth s p h

def repeatEvent (c : Config) (s : State) (g : Nat × Nat) : Bool :=
  base.contains (value c s g &&& 127) || has (projected s.history) (value c s g &&& 127)

def mandatoryEvent (c : Config) (s : State) (g : Nat × Nat) : Bool :=
  (returnEvent c s g && !has s.returned g.1) ||
  (copyEvent c s g && !has s.copied (g.1-c.sources.length-1))

def extraEvent (c : Config) (s : State) (g : Nat × Nat) : Bool :=
  repeatEvent c s g && !mandatoryEvent c s g

def extraCount (c : Config) (s : State) : List (Nat × Nat) → Nat
  | [] => 0
  | g :: p => (if extraEvent c s g then 1 else 0) + extraCount c (advance c s g) p

theorem advance_extra (c : Config) (s : State) (g : Nat × Nat) :
    (advance c s g).extra = s.extra + if extraEvent c s g then 1 else 0 := by rfl

theorem raw_extra (c : Config) (s : State) (p : List (Nat × Nat)) :
    (rawRun c s p).extra = s.extra + extraCount c s p := by
  induction p generalizing s with
  | nil => simp [rawRun,extraCount]
  | cons g p ih =>
    rw [rawRun,ih,advance_extra,extraCount]
    omega

theorem accepted_extra_budget (c : Config) (depth : Nat) (s z : State) (t j : Nat)
    (h : move c depth s t j = some z) : z.extra ≤ 2-c.sources.length := by
  obtain ⟨ha,hz⟩ := (move_eq_some_iff c depth s z t j).mp h
  have he := ha.2.2.1
  change decide ((propose c depth s t j).state.extra > 2-c.sources.length) = false at he
  rw [hz]
  exact Nat.le_of_not_gt (of_decide_eq_false he)

end HGP13.TransitionChecks
