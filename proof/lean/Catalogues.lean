import TransposeFree
import Projection
import TransposeBudget

/-! Source Lemma 7.1: finite XOR saturation and arbitrary free programs.
The fuel bound is derived from the number of candidate values; it is not
a cutoff on the length of a program being excluded. -/
namespace HGP13.Catalogues
open FreeXor (validMasks)
abbrev Value := BitVec 7

def derivable (available : List Value) (z : Value) : Bool :=
  available.any (fun x => available.any (fun y => x ^^^ y == z))
def ready (available : List Value) (z : Value) : Bool :=
  !available.contains z && derivable available z

def build : Nat → List Value → List Value → List Value
  | 0, _, _ => []
  | n+1, todo, available =>
    match todo.find? (ready available) with
    | none => []
    | some z => z :: build n (todo.erase z) (z :: available)

def endState (available : List Value) : List Value → List Value
  | [] => available
  | z :: p => endState (z :: available) p
def saturation (available todo : List Value) : List Value :=
  endState available (build todo.length todo available)
def accepts (available todo : List Value) : Bool := todo.all (saturation available todo).contains

theorem endState_members (available p : List Value) (z : Value) :
    z ∈ endState available p ↔ z ∈ available ++ p := by
  induction p generalizing available with
  | nil => simp [endState]
  | cons a p ih =>
    simp only [endState,ih,List.mem_append,List.mem_cons,or_assoc,or_left_comm,or_comm]

theorem endState_initial (available p : List Value) : available ⊆ endState available p := by
  intro z hz
  exact (endState_members available p z).mpr (List.mem_append_left _ hz)

theorem found_ready (todo available : List Value) (z : Value)
    (h : todo.find? (ready available) = some z) :
    z ∈ todo ∧ z ∉ available ∧ derivable available z = true := by
  have hr := List.find?_some h
  refine ⟨List.mem_of_find?_eq_some h,?_⟩
  simpa [ready] using hr

theorem build_valid (n : Nat) (todo available : List Value) :
    validMasks available (build n todo available) = true := by
  induction n generalizing todo available with
  | zero => rfl
  | succ n ih =>
    cases hf : todo.find? (ready available) with
    | none => simp [build,hf,validMasks]
    | some z =>
      have hr := (found_ready todo available z hf).2.2
      simp only [build,hf,validMasks,Bool.and_eq_true]
      exact ⟨hr,ih (todo.erase z) (z :: available)⟩

theorem build_subset (n : Nat) (todo available : List Value) : build n todo available ⊆ todo := by
  induction n generalizing todo available with
  | zero => simp [build]
  | succ n ih =>
    cases hf : todo.find? (ready available) with
    | none => simp [build,hf]
    | some z =>
      intro a ha
      simp only [build,hf,List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact List.mem_of_find?_eq_some hf
      · exact List.mem_of_mem_erase (ih (todo.erase z) (z :: available) ha)

theorem build_closed (n : Nat) (todo available : List Value) (enough : todo.length ≤ n) :
    ∀ z ∈ todo, derivable (endState available (build n todo available)) z = true →
      z ∈ endState available (build n todo available) := by
  induction n generalizing todo available with
  | zero =>
    have hn : todo = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [hn]
  | succ n ih =>
    cases hf : todo.find? (ready available) with
    | none =>
      intro z hz hd
      simp only [build,hf,endState] at hd ⊢
      have no := List.find?_eq_none.mp hf z hz
      have nn : ¬ ready available z = true := no
      by_cases hs : z ∈ available
      · exact hs
      · have yes : ready available z = true := by simp [ready,hs,hd]
        exact False.elim (nn yes)
    | some a =>
      have ha := (found_ready todo available a hf).1
      have smaller : (todo.erase a).length ≤ n := by
        rw [List.length_erase_of_mem ha]
        omega
      intro z hz hd
      simp only [build,hf,endState] at hd ⊢
      by_cases he : z = a
      · subst z
        exact endState_initial (a :: available) _ List.mem_cons_self
      · apply ih (todo.erase a) (a :: available) smaller z _ hd
        exact (List.mem_erase_of_ne he).mpr hz

theorem saturation_closed (available todo : List Value) :
    ∀ z ∈ todo, derivable (saturation available todo) z = true → z ∈ saturation available todo :=
  build_closed todo.length todo available (Nat.le_refl _)

theorem saturation_initial (available todo : List Value) : available ⊆ saturation available todo :=
  endState_initial available _

theorem derivable_of_parents (available : List Value) (a b : Value)
    (ha : a ∈ available) (hb : b ∈ available) : derivable available (a ^^^ b) = true := by
  exact List.any_eq_true.mpr ⟨a,ha,List.any_eq_true.mpr ⟨b,hb,by simp⟩⟩

/-- Every arbitrary-length program restricted to the candidate values lies
inside the computed saturation. -/
theorem every_program_in_saturation (available todo p : List Value)
    (hv : validMasks available p = true) (restricted : p ⊆ todo) :
    available ++ p ⊆ saturation available todo := by
  apply TransposeFree.cut_preserved p available (saturation available todo) todo hv
    (saturation_initial available todo) restricted
  intro a ha b hb hz
  exact saturation_closed available todo (a ^^^ b) hz (derivable_of_parents _ a b ha hb)

theorem accepts_iff_program (available todo : List Value) :
    accepts available todo = true ↔
      ∃ p : List Value, validMasks available p = true ∧ p ⊆ todo ∧ todo ⊆ available ++ p := by
  constructor
  · intro h
    refine ⟨build todo.length todo available,build_valid _ _ _,build_subset _ _ _,?_⟩
    intro z hz
    have hm := List.contains_iff_mem.mp (List.all_eq_true.mp h z hz)
    exact (endState_members _ _ z).mp hm
  · rintro ⟨p,hv,hr,hg⟩
    apply List.all_eq_true.mpr
    intro z hz
    exact List.contains_iff_mem.mpr (every_program_in_saturation available todo p hv hr (hg hz))

/-- A complete valid schedule has the same acceptance result, regardless of
which currently available addition was chosen first. -/
theorem closed_schedule_equivalent (available todo p : List Value)
    (hv : validMasks available p = true) (restricted : p ⊆ todo)
    (closed : ∀ z ∈ todo, derivable (endState available p) z = true → z ∈ endState available p) :
    accepts available todo = true ↔ todo ⊆ endState available p := by
  constructor
  · intro h
    obtain ⟨q,hq,hr,hg⟩ := (accepts_iff_program available todo).mp h
    have sub := TransposeFree.cut_preserved q available (endState available p) todo hq
      (endState_initial available p) hr
      (by intro a ha b hb hz; exact closed (a ^^^ b) hz (derivable_of_parents _ a b ha hb))
    exact fun z hz => sub (hg hz)
  · intro h
    apply (accepts_iff_program available todo).mpr
    exact ⟨p,hv,restricted,fun z hz => (endState_members available p z).mp (h hz)⟩

def Fresh (available : List Value) : List Value → Prop
  | [] => True
  | z :: p => z ∉ available ∧ Fresh (z :: available) p

theorem build_fresh (n : Nat) (todo available : List Value) : Fresh available (build n todo available) := by
  induction n generalizing todo available with
  | zero => trivial
  | succ n ih =>
    cases hf : todo.find? (ready available) with
    | none => simp [build,hf,Fresh]
    | some z =>
      simp only [build,hf,Fresh]
      exact ⟨(found_ready todo available z hf).2.1,ih _ _⟩

theorem accepts_iff_fresh_program (available todo : List Value) :
    accepts available todo = true ↔ ∃ p : List Value,
      validMasks available p = true ∧ Fresh available p ∧ p ⊆ todo ∧ todo ⊆ available ++ p := by
  constructor
  · intro h
    refine ⟨build todo.length todo available,build_valid _ _ _,build_fresh _ _ _,build_subset _ _ _,?_⟩
    intro z hz
    exact (endState_members _ _ z).mp
      (List.contains_iff_mem.mp (List.all_eq_true.mp h z hz))
  · rintro ⟨p,hv,_,hr,hg⟩
    exact (accepts_iff_program available todo).mpr ⟨p,hv,hr,hg⟩

/-- Initially available values and a free zero may be repeated arbitrarily.
This does not allow any new nonzero candidate to escape saturation. -/
theorem relaxed_program_in_saturation (available todo p : List Value)
    (hv : validMasks (0 :: available) p = true)
    (restricted : p ⊆ 0 :: (available ++ todo)) :
    (0 :: available) ++ p ⊆ 0 :: saturation available todo := by
  refine TransposeFree.cut_preserved p (0 :: available) (0 :: saturation available todo)
    (0 :: (available ++ todo)) hv ?_ restricted ?_
  · intro z hz
    rcases List.mem_cons.mp hz with he | hz
    · exact List.mem_cons.mpr (Or.inl he)
    · exact List.mem_cons_of_mem _ (saturation_initial available todo hz)
  · intro a ha b hb hz
    rcases List.mem_cons.mp ha with ha | ha
    · subst a
      simpa using hb
    rcases List.mem_cons.mp hb with hb | hb
    · subst b
      simpa using List.mem_cons_of_mem (0 : Value) ha
    rcases List.mem_cons.mp hz with hz | hz
    · exact List.mem_cons.mpr (Or.inl hz)
    · apply List.mem_cons_of_mem
      rcases List.mem_append.mp hz with hz | hz
      · exact saturation_initial available todo hz
      · exact saturation_closed available todo (a ^^^ b) hz (derivable_of_parents _ a b ha hb)

theorem accepts_of_relaxed_program (available todo p : List Value)
    (nonzero : ∀ z ∈ todo, z ≠ 0)
    (hv : validMasks (0 :: available) p = true)
    (restricted : p ⊆ 0 :: (available ++ todo))
    (reaches : todo ⊆ (0 :: available) ++ p) : accepts available todo = true := by
  have all := relaxed_program_in_saturation available todo p hv restricted
  apply List.all_eq_true.mpr
  intro z hz
  have hm := all (reaches hz)
  exact List.contains_iff_mem.mpr ((List.mem_cons.mp hm).resolve_left (nonzero z hz))

def extras (goals p : List Value) : List Value :=
  (p.filter (fun z => !(0 :: (FreeXor.maskBasis ++ goals)).contains z)).eraseDups

theorem extras_membership (goals p : List Value) (z : Value) :
    z ∈ extras goals p ↔ z ∈ p ∧ z ≠ 0 ∧ z ∉ FreeXor.maskBasis ∧ z ∉ goals := by
  simp [extras]

theorem actual_extras_accepted (goals p : List Value)
    (nonzero : ∀ z ∈ goals, z ≠ 0)
    (hv : validMasks (0 :: FreeXor.maskBasis) p = true)
    (reaches : goals ⊆ (0 :: FreeXor.maskBasis) ++ p) :
    accepts FreeXor.maskBasis (goals ++ extras goals p) = true := by
  refine accepts_of_relaxed_program FreeXor.maskBasis (goals ++ extras goals p) p ?_ hv ?_ ?_
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact nonzero z hz
    · exact ((extras_membership goals p z).mp hz).2.1
  · intro z hz
    by_cases h0 : z = 0
    · exact List.mem_cons.mpr (Or.inl h0)
    apply List.mem_cons_of_mem
    by_cases hb : z ∈ FreeXor.maskBasis
    · exact List.mem_append_left _ hb
    apply List.mem_append_right
    by_cases hg : z ∈ goals
    · exact List.mem_append_left _ hg
    exact List.mem_append_right _ ((extras_membership goals p z).mpr ⟨hz,h0,hb,hg⟩)
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact reaches hz
    · exact List.mem_append_right _ ((extras_membership goals p z).mp hz).1

def Catalogued (goals : List Value) (k : Nat) (extra : List Value) : Prop :=
  extra.Nodup ∧ extra.length = k ∧
  (∀ z ∈ extra, z ≠ 0 ∧ z ∉ FreeXor.maskBasis ∧ z ∉ goals) ∧
  accepts FreeXor.maskBasis (goals ++ extra) = true

theorem actual_extras_catalogued (goals p : List Value)
    (nonzero : ∀ z ∈ goals, z ≠ 0)
    (hv : validMasks (0 :: FreeXor.maskBasis) p = true)
    (reaches : goals ⊆ (0 :: FreeXor.maskBasis) ++ p) :
    Catalogued goals (extras goals p).length (extras goals p) := by
  refine ⟨CountHelpers.eraseDups_nodup _,rfl,?_,actual_extras_accepted goals p nonzero hv reaches⟩
  intro z hz
  exact ((extras_membership goals p z).mp hz).2

theorem original_catalogue (p : HGP13.Program) (h : HGP13.run HGP13.identity p = HGP13.target) :
    Catalogued FreeXor.maskGoals (FreeXor.maskAuxiliaries (Projection.trace HGP13.identity p)).length
      (FreeXor.maskAuxiliaries (Projection.trace HGP13.identity p)) := by
  exact actual_extras_catalogued FreeXor.maskGoals (Projection.trace HGP13.identity p)
    (by decide) (Projection.trace_valid p HGP13.identity _ Projection.initial_supported)
    (fun z hz => Projection.trace_reaches_targets p h z hz)

theorem transpose_extras (p : List Value) : extras TransposeFree.goals p = TransposeBudget.auxiliaries p := by
  rfl

theorem transpose_catalogue (p : HGP13.Program)
    (h : HGP13.run HGP13.identity p = TransposeTarget.matrix) :
    Catalogued TransposeFree.goals (TransposeBudget.auxiliaries (Projection.trace HGP13.identity p)).length
      (TransposeBudget.auxiliaries (Projection.trace HGP13.identity p)) := by
  rw [← transpose_extras]
  exact actual_extras_catalogued TransposeFree.goals (Projection.trace HGP13.identity p)
    (by decide) (Projection.trace_valid p HGP13.identity _ Projection.initial_supported)
    (TransposeTarget.trace_reaches p h)


/-- The catalogue test is exactly existence of a first-appearance schedule. -/
theorem catalogue_characterization (goals extra : List Value) (k : Nat) :
    Catalogued goals k extra ↔ extra.Nodup ∧ extra.length = k ∧
      (∀ z ∈ extra, z ≠ 0 ∧ z ∉ FreeXor.maskBasis ∧ z ∉ goals) ∧
      ∃ p : List Value, validMasks FreeXor.maskBasis p = true ∧
        Fresh FreeXor.maskBasis p ∧ p ⊆ goals ++ extra ∧
        goals ++ extra ⊆ FreeXor.maskBasis ++ p := by
  unfold Catalogued
  rw [accepts_iff_fresh_program]

/-- Matching the complement lookup used by the executable closure. -/
theorem derivable_complement_test (available : List Value) (z : Value) :
    derivable available z = true ↔
      available.any (fun a => available.contains (z ^^^ a)) = true := by
  constructor
  · intro h
    obtain ⟨a,ha,hh⟩ := List.any_eq_true.mp h
    obtain ⟨b,hb,he⟩ := List.any_eq_true.mp hh
    have eq : a ^^^ b = z := by simpa using he
    have solved : b = z ^^^ a := by
      have hh := TransposeFree.xor_solve b a z (by simpa [BitVec.xor_comm] using eq)
      simpa [BitVec.xor_comm] using hh
    exact List.any_eq_true.mpr ⟨a,ha,List.contains_iff_mem.mpr (solved ▸ hb)⟩
  · intro h
    obtain ⟨a,ha,hb⟩ := List.any_eq_true.mp h
    apply List.any_eq_true.mpr
    refine ⟨a,ha,List.any_eq_true.mpr ⟨z ^^^ a,List.contains_iff_mem.mp hb,?_⟩⟩
    have he : a ^^^ (z ^^^ a) = z := by
      rw [BitVec.xor_comm z a, ← BitVec.xor_assoc]
      simp
    simpa using he

theorem extras_mono (goals q p : List Value) (h : q ⊆ p) :
    extras goals q ⊆ extras goals p := by
  intro z hz
  obtain ⟨hz,h0,hb,hg⟩ := (extras_membership goals q z).mp hz
  exact (extras_membership goals p z).mpr ⟨h hz,h0,hb,hg⟩

/-- Abstract prefix test; no claim about an external serialized table. -/
def Extendible (goals observed : List Value) (capacity : Nat) : Prop :=
  ∃ extra : List Value, Catalogued goals extra.length extra ∧
    extra.length ≤ capacity ∧ observed ⊆ extra

theorem original_short_catalogue (p : HGP13.Program)
    (h : HGP13.run HGP13.identity p = HGP13.target) (hl : p.length ≤ 18)
    (hu : (Budget.touchedSources p).length = 1 ∨ (Budget.touchedSources p).length = 2) :
    ∃ k, (k = 3 ∨ k = 4) ∧
      Catalogued FreeXor.maskGoals k (FreeXor.maskAuxiliaries (Projection.trace HGP13.identity p)) := by
  have hb := ExactBudget.exact_budget p h
  refine ⟨_,?_,original_catalogue p h⟩
  omega

theorem transpose_short_catalogue (p : HGP13.Program)
    (h : HGP13.run HGP13.identity p = TransposeTarget.matrix) (hl : p.length ≤ 18)
    (hu : (Budget.touchedSources p).length = 1 ∨ (Budget.touchedSources p).length = 2) :
    ∃ k, (k = 3 ∨ k = 4) ∧
      Catalogued TransposeFree.goals k (TransposeBudget.auxiliaries (Projection.trace HGP13.identity p)) := by
  have hb := TransposeBudget.exact_oriented_budget p h
  refine ⟨_,?_,transpose_catalogue p h⟩
  omega

theorem original_tight_catalogue (p : HGP13.Program)
    (h : HGP13.run HGP13.identity p = HGP13.target) (hl : p.length ≤ 18)
    (hu : (Budget.touchedSources p).length = 2) :
    Catalogued FreeXor.maskGoals 3 (FreeXor.maskAuxiliaries (Projection.trace HGP13.identity p)) := by
  have hc := original_catalogue p h
  rw [(ExactBudget.two_sources_saturation p h hl hu).2.1] at hc
  exact hc

theorem transpose_tight_catalogue (p : HGP13.Program)
    (h : HGP13.run HGP13.identity p = TransposeTarget.matrix) (hl : p.length ≤ 18)
    (hu : (Budget.touchedSources p).length = 2) :
    Catalogued TransposeFree.goals 3 (TransposeBudget.auxiliaries (Projection.trace HGP13.identity p)) := by
  have hc := transpose_catalogue p h
  rw [(TransposeBudget.two_sources_saturation p h hl hu).2.1] at hc
  exact hc

/-- Any partial history, including one with omitted passive operations,
passes the abstract subset-of-a-complete-catalogue test. -/
theorem partial_history_extendible (goals p q : List Value) (capacity : Nat)
    (hn : ∀ z ∈ goals, z ≠ 0)
    (hv : validMasks (0 :: FreeXor.maskBasis) p = true)
    (hr : goals ⊆ (0 :: FreeXor.maskBasis) ++ p)
    (hq : q ⊆ p) (hc : (extras goals p).length ≤ capacity) :
    Extendible goals (extras goals q) capacity := by
  exact ⟨extras goals p,actual_extras_catalogued goals p hn hv hr,hc,extras_mono goals q p hq⟩

end HGP13.Catalogues


