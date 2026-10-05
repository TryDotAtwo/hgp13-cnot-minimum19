import Transposition

namespace HGP13.CoordinateRestriction

abbrev SmallMatrix (n : Nat) := Fin n → Fin n → Bool
abbrev SmallGate (n : Nat) := Fin n × Fin n

def restrict {n : Nat} (e : Fin n → Wire) (x : Matrix) : SmallMatrix n :=
  fun i j => coefficient x (e i) (e j)

def smallStep {n : Nat} (x : SmallMatrix n) (g : SmallGate n) : SmallMatrix n :=
  fun i j => if i = g.2 then x i j ^^ x g.1 j else x i j

def liftGate {n : Nat} (e : Fin n → Wire) (g : SmallGate n) : Gate :=
  (e g.1, e g.2)

def smallRun {n : Nat} (x : SmallMatrix n) (p : List (SmallGate n)) :=
  p.foldl smallStep x

theorem restrict_step {n : Nat} (e : Fin n → Wire)
    (inj : Function.Injective e) (x : Matrix) (g : SmallGate n) :
    restrict e (step x (liftGate e g)) = smallStep (restrict e x) g := by
  funext i j
  simp only [restrict, step_coefficient, liftGate, smallStep]
  have he : e i = e g.2 ↔ i = g.2 := ⟨fun h => inj h, congrArg e⟩
  simp only [he]

theorem restrict_run {n : Nat} (e : Fin n → Wire)
    (inj : Function.Injective e) (x : Matrix) (p : List (SmallGate n)) :
    restrict e (run x (p.map (liftGate e))) = smallRun (restrict e x) p := by
  induction p generalizing x with
  | nil => rfl
  | cons g p ih =>
    simp only [List.map_cons, run_cons]
    rw [ih, restrict_step e inj]
    rfl

theorem restrict_identity {n : Nat} (e : Fin n → Wire)
    (inj : Function.Injective e) :
    restrict e identity = fun i j => decide (i = j) := by
  funext i j
  simp only [restrict, Transposition.coefficient_identity, Transposition.unit]
  have he : e i = e j ↔ i = j := ⟨fun h => inj h, congrArg e⟩
  simp only [he]

theorem lifted_length {n : Nat} (e : Fin n → Wire) (p : List (SmallGate n)) :
    (p.map (liftGate e)).length = p.length := List.length_map _

theorem lifted_legal_iff {n : Nat} (e : Fin n → Wire)
    (inj : Function.Injective e) (p : List (SmallGate n)) :
    Legal (p.map (liftGate e)) ↔ ∀ g ∈ p, g.1 ≠ g.2 := by
  constructor
  · intro h g hg he
    exact h (liftGate e g) (List.mem_map.mpr ⟨g, hg, rfl⟩) (congrArg e he)
  · intro h g hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    exact fun he => h a ha (inj he)

/-- Retained rows have no coefficients in the discarded columns. -/
def Supported {n : Nat} (e : Fin n → Wire) (x : Matrix) : Prop :=
  ∀ i j, (∀ k, e k ≠ j) → coefficient x (e i) j = false

theorem identity_supported {n : Nat} (e : Fin n → Wire) : Supported e identity := by
  intro i j hj
  simp [Transposition.coefficient_identity, Transposition.unit, hj i]

theorem step_supported {n : Nat} (e : Fin n → Wire) (x : Matrix)
    (g : SmallGate n) (h : Supported e x) : Supported e (step x (liftGate e g)) := by
  intro i j hj
  simp only [step_coefficient, liftGate]
  rw [h i j hj, h g.1 j hj]
  split <;> rfl

theorem run_supported {n : Nat} (e : Fin n → Wire) (x : Matrix)
    (p : List (SmallGate n)) (h : Supported e x) :
    Supported e (run x (p.map (liftGate e))) := by
  induction p generalizing x with
  | nil => exact h
  | cons g p ih =>
    simp only [List.map_cons, run_cons]
    exact ih _ (step_supported e x g h)

/-- Equality in the retained square determines every coefficient of retained rows. -/
theorem restriction_faithful {n : Nat} (e : Fin n → Wire) (x y : Matrix)
    (hx : Supported e x) (hy : Supported e y) (h : restrict e x = restrict e y) :
    ∀ i j, coefficient x (e i) j = coefficient y (e i) j := by
  intro i j
  by_cases hj : ∃ k, e k = j
  · obtain ⟨k, rfl⟩ := hj
    exact congrFun (congrFun h i) k
  · have hn : ∀ k, e k ≠ j := fun k hk => hj ⟨k, hk⟩
    rw [hx i j hn, hy i j hn]

/-- Every word whose endpoints are retained has a word in the smaller alphabet. -/
theorem word_lifts {n : Nat} (e : Fin n → Wire) (p : Program)
    (h : ∀ g ∈ p, (∃ c, e c = g.1) ∧ (∃ t, e t = g.2)) :
    ∃ q : List (SmallGate n), q.map (liftGate e) = p := by
  induction p with
  | nil => exact ⟨[], rfl⟩
  | cons g p ih =>
    obtain ⟨⟨c, hc⟩, ⟨t, ht⟩⟩ := h g (by simp)
    obtain ⟨q, hq⟩ := ih (fun a ha => h a (by simp [ha]))
    refine ⟨(c,t) :: q, ?_⟩
    simp only [List.map_cons, hq]
    have hg : liftGate e (c,t) = g := by
      apply Prod.ext <;> assumption
    rw [hg]

theorem normalized_word_exists {n : Nat} (e : Fin n → Wire)
    (inj : Function.Injective e) (p : Program) (legal : Legal p)
    (h : ∀ g ∈ p, (∃ c, e c = g.1) ∧ (∃ t, e t = g.2)) :
    ∃ q : List (SmallGate n), q.length = p.length ∧
      (∀ g ∈ q, g.1 ≠ g.2) ∧
      smallRun (fun i j => decide (i = j)) q = restrict e (run identity p) := by
  obtain ⟨q, rfl⟩ := word_lifts e p h
  refine ⟨q, (lifted_length e q).symm, (lifted_legal_iff e inj q).mp legal, ?_⟩
  rw [restrict_run e inj, restrict_identity e inj]

end HGP13.CoordinateRestriction

