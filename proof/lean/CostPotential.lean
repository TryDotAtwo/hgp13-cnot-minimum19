import PassiveCost
import Projection

namespace HGP13.CostPotential

/-- A dual certificate needs only inequalities, not an exact dynamic program. -/
def Valid (d : List Row) (weight : Row → Nat) : Prop :=
  weight 0 = 0 ∧ ∀ v ∈ d, ∀ x, weight (v ^^^ x) ≤ weight x + 1

theorem xor_bound (d b : List Row) (weight : Row → Nat)
    (valid : Valid d weight) (available : b ⊆ d) :
    weight (xorSum b) ≤ b.length := by
  induction b with
  | nil => simpa [xorSum] using Nat.le_of_eq valid.1
  | cons v b ih =>
    have hv : v ∈ d := available (by simp)
    have hb : b ⊆ d := fun x hx => available (by simp [hx])
    have hstep := valid.2 v hv (xorSum b)
    have htail := ih hb
    simpa only [xorSum,List.length_cons] using Nat.le_trans hstep (Nat.add_le_add_right htail 1)

theorem cost_bound (d : List Row) (z : Row) (n : Nat) (weight : Row → Nat)
    (valid : Valid d weight) (hc : PassiveCost.cost d z = some n) :
    weight z ≤ n := by
  obtain ⟨b,hb,hz,hn⟩ := PassiveCost.cost_attains d z n hc
  have h := xor_bound d b weight valid hb.subset
  simpa [hz,hn] using h

/-- A seven-bit table can certify costs of arbitrary full rows. -/
theorem projected_valid (d : List Row) (weight : BitVec 7 → Nat)
    (zero : weight 0 = 0)
    (edges : ∀ v ∈ d, ∀ x, weight (Projection.project v ^^^ x) ≤ weight x + 1) :
    Valid d (fun r => weight (Projection.project r)) := by
  constructor
  · have h : Projection.project (0 : Row) = 0 := by decide
    exact (congrArg weight h).trans zero
  · intro v hv x
    change weight (Projection.project (v ^^^ x)) ≤ weight (Projection.project x) + 1
    rw [Projection.project_add]
    exact edges v hv (Projection.project x)

end HGP13.CostPotential
