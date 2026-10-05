import PackedTerminalPotential

/- Adapted from the independently reviewed contribution-bound candidate.
   Connects a checked potential directly to real control contributions,
   without requiring an exact-cost function or a dynamic-programming result. -/
namespace HGP13.ContributionCompletion

theorem excludes_contributions {ι : Type} (indices : List ι)
    (d : List Row) (table depth : Nat)
    (form : ι → Row) (contributions : ι → List Row)
    (checked : PackedTerminalPotential.check d table = true)
    (available : ∀ i ∈ indices, contributions i ⊆ d)
    (represents : ∀ i ∈ indices, xorSum (contributions i) = form i)
    (bound : 18 < depth + (indices.map (fun i =>
      PackedTerminalPotential.tableWeight table (Projection.project (form i)))).sum) :
    18 < depth + (indices.map (fun i => (contributions i).length)).sum := by
  have each : ∀ i ∈ indices,
      PackedTerminalPotential.tableWeight table (Projection.project (form i)) ≤
        (contributions i).length := by
    intro i hi
    have h := CostPotential.xor_bound d (contributions i)
      (fun r => PackedTerminalPotential.tableWeight table (Projection.project r))
      (PackedTerminalPotential.valid_of_check d table checked) (available i hi)
    simpa only [represents i hi] using h
  have total := PassiveCost.sum_map_le indices
    (fun i => PackedTerminalPotential.tableWeight table (Projection.project (form i)))
    (fun i => (contributions i).length) each
  omega

theorem excludes_full_program (p : Program) (keep : Wire → Bool) (js : List Wire)
    (d : List Row) (table : Nat) (m : Matrix)
    (controls : ∀ g ∈ p, keep g.1 = true)
    (cover : PassiveCost.CoversHistory keep identity p d)
    (distinct : js.Nodup) (coverage : ∀ j, j ∈ js ↔ keep j = false)
    (final : run identity p = m)
    (checked : PackedTerminalPotential.check d table = true)
    (bound : 18 < (p.filter (fun g => keep g.2)).length +
      (js.map (fun j => PackedTerminalPotential.tableWeight table
        (Projection.project (identity j ^^^ m j)))).sum) :
    18 < p.length := by
  have h := excludes_contributions js d table (p.filter (fun g => keep g.2)).length
    (fun j => identity j ^^^ m j) (fun j => contributions j identity p) checked
    (fun j _ => PassiveCost.contributions_in_history p identity j keep d controls cover)
    (fun j _ => by rw [← final,row_accounting,PassiveCost.xor_cancel_left]) bound
  simp only [PassiveCost.contributions_count] at h
  rw [PassiveCost.passive_count_partition keep js p distinct coverage]
  exact h

end HGP13.ContributionCompletion
