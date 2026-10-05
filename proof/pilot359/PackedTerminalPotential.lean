import CostPotential

namespace HGP13.PackedTerminalPotential

def tableWeight (table : Nat) (x : BitVec 7) : Nat := (table >>> (2*x.toNat)) &&& 3

def check (d : List Row) (table : Nat) : Bool :=
  decide (tableWeight table 0 = 0) && d.all (fun v =>
    (List.finRange 128).all (fun x =>
      decide (tableWeight table (Projection.project v ^^^ BitVec.ofNat 7 x.val) ≤
        tableWeight table (BitVec.ofNat 7 x.val) + 1)))

theorem valid_of_check (d : List Row) (table : Nat) (hc : check d table = true) :
    CostPotential.Valid d (fun r => tableWeight table (Projection.project r)) := by
  simp only [check, Bool.and_eq_true] at hc
  obtain ⟨hz,he⟩ := hc
  apply CostPotential.projected_valid d (tableWeight table) (of_decide_eq_true hz)
  intro v hv x
  have h := List.all_eq_true.mp (List.all_eq_true.mp he v hv)
    ⟨x.toNat,x.isLt⟩ (List.mem_finRange _)
  simpa using (of_decide_eq_true h)

theorem excludes_completion (d targets : List Row) (table : Nat)
    (depth : Nat) (costs : Row → Nat)
    (checked : check d table = true)
    (hc : ∀ z ∈ targets, PassiveCost.cost d z = some (costs z))
    (bound : 18 < depth + (targets.map (fun z => tableWeight table (Projection.project z))).sum) :
    18 < depth + (targets.map costs).sum := by
  have hs := PassiveCost.sum_map_le targets
    (fun z => tableWeight table (Projection.project z)) costs
    (fun z hz => CostPotential.cost_bound d z (costs z) _
      (valid_of_check d table checked) (hc z hz))
  omega

end HGP13.PackedTerminalPotential

