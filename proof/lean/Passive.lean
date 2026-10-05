import HGP13

namespace HGP13

/-- Agreement of full 13-bit rows, including all private coefficients. -/
def AgreeOn (keep : Wire → Bool) (x y : Matrix) : Prop :=
  ∀ i, keep i = true → x i = y i

theorem step_agrees {keep : Wire → Bool} {x y : Matrix} (g : Gate)
    (h : AgreeOn keep x y) (hc : keep g.1 = true) :
    AgreeOn keep (step x g) (step y g) := by
  intro i hi
  simp only [step]
  split
  · rw [h i hi, h g.1 hc]
  · exact h i hi

theorem passive_step_agrees {keep : Wire → Bool} (x : Matrix) (g : Gate)
    (ht : keep g.2 = false) : AgreeOn keep (step x g) x := by
  intro i hi
  have hn : i ≠ g.2 := by
    intro he
    subst i
    simp [ht] at hi
  exact step_other x g i hn

/-- Removing gates with passive targets preserves every full core row.
    The premise states the sector alphabet: no passive wire is a control. -/
theorem erase_passive_preserves_core (keep : Wire → Bool) (p : Program)
    (hc : ∀ g ∈ p, keep g.1 = true) (x y : Matrix)
    (hxy : AgreeOn keep x y) :
    AgreeOn keep (run x p) (run y (p.filter (fun g => keep g.2))) := by
  induction p generalizing x y with
  | nil => exact hxy
  | cons g p ih =>
    have hcg : keep g.1 = true := hc g (by simp)
    have hcp : ∀ a ∈ p, keep a.1 = true := by
      intro a ha
      exact hc a (by simp [ha])
    cases ht : keep g.2 with
    | true =>
      simp only [List.filter_cons, ht, ↓reduceIte, run_cons]
      exact ih hcp (step x g) (step y g) (step_agrees g hxy hcg)
    | false =>
      simp only [List.filter_cons, ht, Bool.false_eq_true, ↓reduceIte, run_cons]
      apply ih hcp (step x g) y
      intro i hi
      exact (passive_step_agrees x g ht i hi).trans (hxy i hi)

def contributions (j : Wire) (x : Matrix) : Program → List Row
  | [] => []
  | g :: p =>
    if g.2 = j then x g.1 :: contributions j (step x g) p
    else contributions j (step x g) p

def xorSum : List Row → Row
  | [] => 0
  | a :: l => a ^^^ xorSum l

/-- A row's final value is its initial value plus all actual control values
    sent to it. Nothing in this statement discards private bits. -/
theorem row_accounting (p : Program) (x : Matrix) (j : Wire) :
    run x p j = x j ^^^ xorSum (contributions j x p) := by
  induction p generalizing x with
  | nil => simp [run, contributions, xorSum]
  | cons g p ih =>
    rw [run_cons, ih]
    by_cases h : g.2 = j
    · subst j
      simp [contributions, step, xorSum, BitVec.xor_assoc]
    · have h' : j ≠ g.2 := Ne.symm h
      simp [contributions, step, h, h']

theorem contributions_length_le (p : Program) (x : Matrix) (j : Wire) :
    (contributions j x p).length ≤ p.length := by
  induction p generalizing x with
  | nil => simp [contributions]
  | cons g p ih =>
    have hh := ih (step x g)
    simp only [contributions]
    split <;> simp only [List.length_cons] <;> omega

end HGP13
