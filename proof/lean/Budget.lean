import Projection
import CountHelpers

namespace HGP13.Budget
open HGP13.FreeXor HGP13.Projection

structure Event where
  target : Wire
  row : Row
  fresh : Bool

def headEvent (x : Matrix) (seen : List (BitVec 7)) (g : Gate) : Event :=
  ⟨g.2, step x g g.2, !seen.contains (project (step x g g.2))⟩

def record (x : Matrix) (seen : List (BitVec 7)) : Program → List Event
  | [] => []
  | g :: p => headEvent x seen g ::
      record (step x g) (project (step x g g.2) :: seen) p

def freshRows (events : List Event) : List (BitVec 7) :=
  (events.filter (fun e => e.fresh)).map (fun e => project e.row)
def repeatTargets (events : List Event) : List Wire :=
  (events.filter (fun e => !e.fresh)).map Event.target

theorem fresh_tail (e : Event) (es : List Event) : freshRows es ⊆ freshRows (e :: es) := by
  intro z hz
  cases h : e.fresh <;> simp_all [freshRows]

theorem repeat_tail (e : Event) (es : List Event) : repeatTargets es ⊆ repeatTargets (e :: es) := by
  intro z hz
  cases h : e.fresh <;> simp_all [repeatTargets]

theorem record_length (p : Program) (x : Matrix) (seen : List (BitVec 7)) :
    (record x seen p).length = p.length := by
  induction p generalizing x seen with
  | nil => rfl
  | cons g p ih => simp [record, ih]

theorem record_projects_to_trace (p : Program) (x : Matrix) (seen : List (BitVec 7)) :
    (record x seen p).map (fun e => project e.row) = trace x p := by
  induction p generalizing x seen with
  | nil => rfl
  | cons g p ih => simp [record, headEvent, trace, ih]

theorem head_value_supported (x : Matrix) (seen : List (BitVec 7)) (g : Gate) (es : List Event) :
    project (step x g g.2) ∈ seen ∨
      project (step x g g.2) ∈ freshRows (headEvent x seen g :: es) := by
  by_cases h : project (step x g g.2) ∈ seen
  · exact Or.inl h
  · apply Or.inr
    simp [freshRows, headEvent, h]

theorem recorded_value_supported (p : Program) (x : Matrix) (seen : List (BitVec 7)) :
    ∀ z ∈ trace x p, z ∈ seen ∨ z ∈ freshRows (record x seen p) := by
  induction p generalizing x seen with
  | nil => simp [trace]
  | cons g p ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact head_value_supported x seen g _
    · rcases ih (step x g) (project (step x g g.2) :: seen) z hz with h | h
      · rcases List.mem_cons.mp h with rfl | h
        · exact head_value_supported x seen g _
        · exact Or.inl h
      · exact Or.inr (fresh_tail _ _ h)

theorem initially_seen_is_repeat (p : Program) (x : Matrix) (seen : List (BitVec 7))
    (e : Event) (he : e ∈ record x seen p) (hz : project e.row ∈ seen) : e.fresh = false := by
  induction p generalizing x seen with
  | nil => simp [record] at he
  | cons g p ih =>
    rcases List.mem_cons.mp he with rfl | he
    · simpa [headEvent] using hz
    · exact ih (step x g) _ he (List.mem_cons_of_mem _ hz)

theorem run_untargeted (p : Program) (x : Matrix) (j : Wire)
    (h : j ∉ p.map Prod.snd) : run x p j = x j := by
  induction p generalizing x with
  | nil => rfl
  | cons g p ih =>
    have ht : j ∉ p.map Prod.snd := by
      intro hj; apply h; simp [hj]
    have hg : j ≠ g.2 := by
      intro hj; apply h; simp [hj]
    rw [run_cons, ih (step x g) ht]
    exact step_other x g j hg

theorem last_target_result (p : Program) (x : Matrix) (seen : List (BitVec 7)) (j : Wire)
    (h : j ∈ p.map Prod.snd) :
    ∃ e ∈ record x seen p, e.target = j ∧ e.row = run x p j := by
  induction p generalizing x seen with
  | nil => simp at h
  | cons g p ih =>
    by_cases ht : j ∈ p.map Prod.snd
    · obtain ⟨e,he,hj,hr⟩ := ih (step x g) (project (step x g g.2) :: seen) ht
      exact ⟨e,List.mem_cons_of_mem _ he,hj,hr⟩
    · have hj : j = g.2 := by simpa [ht] using h
      refine ⟨headEvent x seen g,List.mem_cons_self,?_,?_⟩
      · exact hj.symm
      · rw [run_cons, run_untargeted p (step x g) j ht, hj]
        rfl

theorem first_nonzero_repeat (p : Program) (x : Matrix) (seen : List (BitVec 7)) (j : Wire)
    (supported : ∀ i, project (x i) ∈ seen)
    (start : project (x j) = 0) (finish : project (run x p j) ≠ 0) :
    ∃ e ∈ record x seen p, e.target = j ∧ e.fresh = false := by
  induction p generalizing x seen with
  | nil => exact False.elim (finish start)
  | cons g p ih =>
    by_cases hz : project (step x g j) = 0
    · obtain ⟨e,he,hj,hf⟩ := ih (step x g) _
        (step_supported x g seen supported) hz finish
      exact ⟨e,List.mem_cons_of_mem _ he,hj,hf⟩
    · have hj : j = g.2 := by
        by_cases hj : j = g.2
        · exact hj
        · exact False.elim (hz (by simpa [step, hj] using start))
      have hc : project (step x g g.2) ∈ seen := by
        have hs : project (x g.2) = 0 := by simpa [hj] using start
        simpa [step, project_add, hs] using supported g.1
      refine ⟨headEvent x seen g,List.mem_cons_self,hj.symm,?_⟩
      simp [headEvent, hc]

theorem repeat_target_mem (es : List Event) (e : Event) (he : e ∈ es) (h : e.fresh = false) :
    e.target ∈ repeatTargets es := by
  apply List.mem_map.mpr
  exact ⟨e,List.mem_filter.mpr ⟨he,by simp [h]⟩,rfl⟩

def sources : List Wire := [0,1,2,3,4,5]
def privateOutputs : List Wire := [6,7,9,10,11,12]
def touchedSources (p : Program) : List Wire :=
  sources.filter (fun j => (p.map Prod.snd).contains j)

theorem sources_nodup : sources.Nodup := by decide
theorem private_nodup : privateOutputs.Nodup := by decide
theorem source_private_disjoint : ∀ j ∈ sources, j ∉ privateOutputs := by decide
theorem sources_fixed : ∀ j ∈ sources, target j = identity j := by decide
theorem private_starts_zero : ∀ j ∈ privateOutputs, project (identity j) = 0 := by decide
theorem private_ends_nonzero : ∀ j ∈ privateOutputs, project (target j) ≠ 0 := by decide

theorem required_repeat_targets (p : Program) (h : run identity p = target) :
    privateOutputs ++ touchedSources p ⊆ repeatTargets (record identity (0 :: maskBasis) p) := by
  intro j hj
  rcases List.mem_append.mp hj with hj | hj
  · obtain ⟨e,he,hj',hf⟩ := first_nonzero_repeat p identity (0 :: maskBasis) j
      initial_supported (private_starts_zero j hj) (by rw [h]; exact private_ends_nonzero j hj)
    rw [← hj']
    exact repeat_target_mem _ e he hf
  · have hs : j ∈ sources := (List.mem_filter.mp hj).1
    have ht : j ∈ p.map Prod.snd := by simpa using (List.mem_filter.mp hj).2
    obtain ⟨e,he,hj',hr⟩ := last_target_result p identity (0 :: maskBasis) j ht
    rw [h, sources_fixed j hs] at hr
    have hp : project e.row ∈ 0 :: maskBasis := by rw [hr]; exact initial_supported j
    have hf := initially_seen_is_repeat p identity (0 :: maskBasis) e he hp
    rw [← hj']
    exact repeat_target_mem _ e he hf

theorem required_targets_nodup (p : Program) : (privateOutputs ++ touchedSources p).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨private_nodup, ?_, ?_⟩
  · exact List.Pairwise.filter _ sources_nodup
  · intro a ha b hb he
    subst b
    exact source_private_disjoint a (List.mem_filter.mp hb).1 ha

theorem repeated_count (p : Program) (h : run identity p = target) :
    6 + (touchedSources p).length ≤ (repeatTargets (record identity (0 :: maskBasis) p)).length := by
  have hh := (required_targets_nodup p).length_le_of_subset (required_repeat_targets p h)
  simpa only [List.length_append, show privateOutputs.length = 6 from rfl] using hh

theorem auxiliary_membership (z : BitVec 7) (p : List (BitVec 7)) :
    z ∈ maskAuxiliaries p ↔ z ∈ p ∧ z ≠ 0 ∧ z ∉ maskBasis ∧ z ∉ maskGoals := by
  simp [maskAuxiliaries]

theorem targets_auxiliaries_nodup (p : List (BitVec 7)) :
    (maskGoals ++ maskAuxiliaries p).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨by decide, CountHelpers.eraseDups_nodup _, ?_⟩
  intro a ha b hb he
  subst b
  exact (auxiliary_membership a p).mp hb |>.2.2.2 ha

theorem maskGoals_not_initial : ∀ z ∈ maskGoals, z ∉ 0 :: maskBasis := by decide

theorem required_fresh_rows (p : Program) (h : run identity p = target) :
    maskGoals ++ maskAuxiliaries (trace identity p) ⊆
      freshRows (record identity (0 :: maskBasis) p) := by
  intro z hz
  have nz : z ∉ 0 :: maskBasis := by
    rcases List.mem_append.mp hz with hz | hz
    · exact maskGoals_not_initial z hz
    · have hh := (auxiliary_membership z _).mp hz
      intro hm
      rcases List.mem_cons.mp hm with he | hm
      · exact hh.2.1 he
      · exact hh.2.2.1 hm
  have seen : z ∈ trace identity p := by
    rcases List.mem_append.mp hz with hz | hz
    · exact (List.mem_append.mp (trace_reaches_targets p h z hz)).resolve_left nz
    · exact ((auxiliary_membership z _).mp hz).1
  exact (recorded_value_supported p identity (0 :: maskBasis) z seen).resolve_left nz

theorem fresh_count (p : Program) (h : run identity p = target) :
    10 ≤ (freshRows (record identity (0 :: maskBasis) p)).length := by
  have hh := (targets_auxiliaries_nodup (trace identity p)).length_le_of_subset
    (required_fresh_rows p h)
  have ha := every_realization_needs_three_auxiliaries p h
  simp only [List.length_append] at hh
  change 7 + (maskAuxiliaries (trace identity p)).length ≤ _ at hh
  omega

theorem event_partition (p : Program) (x : Matrix) (seen : List (BitVec 7)) :
    (freshRows (record x seen p)).length + (repeatTargets (record x seen p)).length = p.length := by
  simp only [freshRows, repeatTargets, List.length_map]
  rw [CountHelpers.filter_partition, record_length]

/-- Original-orientation part of source Lemma 4.1, with no sector
    restriction: u counts distinct source coordinates ever targeted. -/
theorem length_ge_sixteen_plus_u (p : Program) (h : run identity p = target) :
    16 + (touchedSources p).length ≤ p.length := by
  have hf := fresh_count p h
  have hr := repeated_count p h
  have he := event_partition p identity (0 :: maskBasis)
  omega

theorem short_program_touches_at_most_two_sources (p : Program)
    (h : run identity p = target) (hl : p.length ≤ 18) :
    (touchedSources p).length ≤ 2 := by
  have hh := length_ge_sixteen_plus_u p h
  omega

end HGP13.Budget
