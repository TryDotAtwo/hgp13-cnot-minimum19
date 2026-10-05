import FullWordPath
import FullPackedPotential

namespace HGP13.FullPackedCompletion

/-- A checked packed potential bounds the passive contributions of an actual
full word.  The packing may retain private coordinates; no projection is
silently substituted for a full row. -/
theorem excludes_full_program {n : Nat} (e : Fin n → Wire)
    (p : Program) (keep : Wire → Bool) (js : List Wire)
    (d : List Row) (table : Nat) (m : Matrix)
    (controls : ∀ g ∈ p, keep g.1 = true)
    (cover : PassiveCost.CoversHistory keep identity p d)
    (distinct : js.Nodup) (coverage : ∀ j, j ∈ js ↔ keep j = false)
    (final : run identity p = m)
    (checked : FullPackedPotential.check e d table = true)
    (bound : 18 < (p.filter (fun g => keep g.2)).length +
      (js.map (fun j => FullPackedPotential.tableWeight table
        (PackedRows.pack e (identity j ^^^ m j)))).sum) :
    18 < p.length := by
  have each : ∀ j ∈ js,
      FullPackedPotential.tableWeight table
        (PackedRows.pack e (identity j ^^^ m j)) ≤
        (contributions j identity p).length := by
    intro j hj
    have h := CostPotential.xor_bound d
      (contributions j identity p)
      (fun r => FullPackedPotential.tableWeight table (PackedRows.pack e r))
      (FullPackedPotential.valid_of_check e d table checked)
      (PassiveCost.contributions_in_history p identity j keep d controls cover)
    simpa only [← final,row_accounting,
      PassiveCost.xor_cancel_left] using h
  have total := PassiveCost.sum_map_le js
    (fun j => FullPackedPotential.tableWeight table
      (PackedRows.pack e (identity j ^^^ m j)))
    (fun j => (contributions j identity p).length) each
  simp only [PassiveCost.contributions_count] at total
  rw [PassiveCost.passive_count_partition keep js p distinct coverage]
  omega

end HGP13.FullPackedCompletion
