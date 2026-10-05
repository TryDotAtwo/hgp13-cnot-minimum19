import Budget

namespace HGP13.ExactBudget
open FreeXor Projection Budget

theorem fresh_cons (e : Event) (es : List Event) :
    freshRows (e :: es) = if e.fresh then project e.row :: freshRows es else freshRows es := by
  cases h : e.fresh <;> simp [freshRows,h]

theorem fresh_not_seen (p : Program) (x : Matrix) (seen : List (BitVec 7))
    (z : BitVec 7) (hz : z ∈ freshRows (record x seen p)) : z ∉ seen := by
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hz
  have he' := List.mem_filter.mp he
  intro hs
  have hf := initially_seen_is_repeat p x seen e he'.1 hs
  simp [hf] at he'

theorem fresh_nodup (p : Program) (x : Matrix) (seen : List (BitVec 7)) :
    (freshRows (record x seen p)).Nodup := by
  induction p generalizing x seen with
  | nil => simp [record,freshRows]
  | cons g p ih =>
    rw [record,fresh_cons]
    cases hf : (headEvent x seen g).fresh
    · simpa only [Bool.false_eq_true,↓reduceIte] using
        ih (step x g) (project (step x g g.2) :: seen)
    · simp only [↓reduceIte]
      apply List.nodup_cons.mpr
      refine ⟨?_,ih (step x g) (project (step x g g.2) :: seen)⟩
      intro hz
      exact fresh_not_seen p (step x g) (project (step x g g.2) :: seen)
        (project (headEvent x seen g).row) hz List.mem_cons_self

theorem fresh_in_trace (p : Program) (x : Matrix) (seen : List (BitVec 7)) :
    freshRows (record x seen p) ⊆ trace x p := by
  intro z hz
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hz
  rw [← record_projects_to_trace p x seen]
  exact List.mem_map.mpr ⟨e,(List.mem_filter.mp he).1,rfl⟩

theorem fresh_in_required (p : Program) :
    freshRows (record identity (0 :: maskBasis) p) ⊆
      maskGoals ++ maskAuxiliaries (trace identity p) := by
  intro z hz
  have ht := fresh_in_trace p identity (0 :: maskBasis) hz
  have hn := fresh_not_seen p identity (0 :: maskBasis) z hz
  by_cases hg : z ∈ maskGoals
  · exact List.mem_append_left _ hg
  · apply List.mem_append_right
    apply (Budget.auxiliary_membership z _).mpr
    refine ⟨ht,?_,?_,hg⟩
    · intro he; exact hn (List.mem_cons.mpr (Or.inl he))
    · intro hb; exact hn (List.mem_cons_of_mem _ hb)

theorem fresh_count_exact (p : Program) (h : run identity p = target) :
    (freshRows (record identity (0 :: maskBasis) p)).length =
      7 + (maskAuxiliaries (trace identity p)).length := by
  have lower := (targets_auxiliaries_nodup (trace identity p)).length_le_of_subset
    (required_fresh_rows p h)
  have upper := (fresh_nodup p identity (0 :: maskBasis)).length_le_of_subset
    (fresh_in_required p)
  simp only [List.length_append] at lower upper
  change 7 + (maskAuxiliaries (trace identity p)).length ≤ _ at lower
  change _ ≤ 7 + (maskAuxiliaries (trace identity p)).length at upper
  omega

/-- Number of repeats beyond the six mandatory first copies and source restorations. -/
def extraRepeats (p : Program) : Nat :=
  (repeatTargets (record identity (0 :: maskBasis) p)).length - (6 + (touchedSources p).length)

/-- Exact source budget, with a and e represented as natural counts. -/
theorem exact_budget (p : Program) (h : run identity p = target) :
    3 ≤ (maskAuxiliaries (trace identity p)).length ∧
    p.length = 13 + (maskAuxiliaries (trace identity p)).length +
      (touchedSources p).length + extraRepeats p := by
  have ha := every_realization_needs_three_auxiliaries p h
  have hf := fresh_count_exact p h
  have hr := repeated_count p h
  have he := event_partition p identity (0 :: maskBasis)
  unfold extraRepeats
  omega

theorem two_sources_saturation (p : Program) (h : run identity p = target)
    (hl : p.length ≤ 18) (hu : (touchedSources p).length = 2) :
    p.length = 18 ∧ (maskAuxiliaries (trace identity p)).length = 3 ∧ extraRepeats p = 0 := by
  have hb := exact_budget p h
  omega

theorem one_source_budget (p : Program) (h : run identity p = target)
    (hl : p.length ≤ 18) (hu : (touchedSources p).length = 1) :
    (maskAuxiliaries (trace identity p)).length + extraRepeats p ≤ 4 := by
  have hb := exact_budget p h
  omega

end HGP13.ExactBudget
