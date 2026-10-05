import PackedRows
import CostPotential

namespace HGP13.FullPackedPotential

def tableWeight {n : Nat} (table : Nat) (x : BitVec n) : Nat :=
  (table >>> (2*x.toNat)) &&& 3

def check {n : Nat} (e : Fin n → Wire) (d : List Row) (table : Nat) : Bool :=
  decide (tableWeight table (0 : BitVec n) = 0) &&
    d.all (fun v =>
      (List.finRange (2^n)).all (fun x =>
        decide (tableWeight table (PackedRows.pack e v ^^^ BitVec.ofNat n x.val) ≤
          tableWeight table (BitVec.ofNat n x.val) + 1)))

theorem packed_valid {n : Nat} (e : Fin n → Wire) (d : List Row)
    (weight : BitVec n → Nat)
    (zero : weight 0 = 0)
    (edges : ∀ v ∈ d, ∀ x,
      weight (PackedRows.pack e v ^^^ x) ≤ weight x + 1) :
    CostPotential.Valid d (fun r => weight (PackedRows.pack e r)) := by
  constructor
  · change weight (PackedRows.pack e (0 : Row)) = 0
    rw [PackedRows.pack_zero]
    exact zero
  · intro v hv x
    change weight (PackedRows.pack e (v ^^^ x)) ≤
      weight (PackedRows.pack e x) + 1
    rw [PackedRows.pack_xor]
    exact edges v hv (PackedRows.pack e x)

theorem valid_of_check {n : Nat} (e : Fin n → Wire) (d : List Row)
    (table : Nat) (hc : check e d table = true) :
    CostPotential.Valid d
      (fun r => tableWeight table (PackedRows.pack e r)) := by
  simp only [check,Bool.and_eq_true] at hc
  obtain ⟨hz,he⟩ := hc
  apply packed_valid e d (tableWeight table) (of_decide_eq_true hz)
  intro v hv x
  have h := List.all_eq_true.mp (List.all_eq_true.mp he v hv)
    ⟨x.toNat,x.isLt⟩ (List.mem_finRange _)
  simpa using (of_decide_eq_true h)

theorem excludes_completion {n : Nat} (e : Fin n → Wire)
    (d targets : List Row) (table : Nat) (depth : Nat)
    (costs : Row → Nat)
    (checked : check e d table = true)
    (hc : ∀ z ∈ targets, PassiveCost.cost d z = some (costs z))
    (bound : 18 < depth +
      (targets.map (fun z => tableWeight table (PackedRows.pack e z))).sum) :
    18 < depth + (targets.map costs).sum := by
  have hs := PassiveCost.sum_map_le targets
    (fun z => tableWeight table (PackedRows.pack e z)) costs
    (fun z hz => CostPotential.cost_bound d z (costs z) _
      (valid_of_check e d table checked) (hc z hz))
  omega

end HGP13.FullPackedPotential
