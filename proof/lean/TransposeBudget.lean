import TransposeTarget
import TransposeCertificate
import ExactBudget

namespace HGP13.TransposeBudget
open FreeXor (validMasks masks_two_cover)
open Projection Budget Transposition TransposeFree

def auxiliaries (p : List (BitVec 7)) : List (BitVec 7) :=
  (p.filter (fun z => !base.contains z)).eraseDups

theorem auxiliary_membership (p : List (BitVec 7)) (z : BitVec 7) :
    z ∈ auxiliaries p ↔ z ∈ p ∧ z ∉ base := by simp [auxiliaries]

theorem three_auxiliaries (p : List (BitVec 7))
    (hv : validMasks initial p = true) (reaches : goals ⊆ initial ++ p) :
    3 ≤ (auxiliaries p).length := by
  by_cases h : 3 ≤ (auxiliaries p).length
  · exact h
  · have small : (auxiliaries p).length ≤ 2 := by omega
    obtain ⟨x,y,cover⟩ := masks_two_cover (auxiliaries p) small
    apply False.elim
    apply TransposeCertificate.two_extras_impossible p x y hv _ reaches
    intro z hz
    by_cases hb : z ∈ base
    · have hh : z ∈ (initial ++ goals) ++ [x,y] := List.mem_append_left _ hb
      simpa only [allowed,List.append_assoc] using hh
    · have hc := cover z ((auxiliary_membership p z).mpr ⟨hz,hb⟩)
      have hm : z ∈ [x,y] := by simpa using hc
      have hh : z ∈ (initial ++ goals) ++ [x,y] := List.mem_append_right _ hm
      simpa only [allowed,List.append_assoc] using hh

theorem goals_not_initial : ∀ z ∈ goals, z ∉ initial := by decide
theorem goals_nodup : goals.Nodup := by decide

theorem required_nodup (p : List (BitVec 7)) : (goals ++ auxiliaries p).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨goals_nodup,CountHelpers.eraseDups_nodup _,?_⟩
  intro a ha b hb he
  subst b
  exact ((auxiliary_membership p a).mp hb).2 (by simp [base,ha])

theorem required_in_trace (p : List (BitVec 7)) (reaches : goals ⊆ initial ++ p) :
    goals ++ auxiliaries p ⊆ p := by
  intro z hz
  rcases List.mem_append.mp hz with hz | hz
  · exact (List.mem_append.mp (reaches hz)).resolve_left (goals_not_initial z hz)
  · exact ((auxiliary_membership p z).mp hz).1

theorem free_lower_bound_ten (p : List (BitVec 7))
    (hv : validMasks initial p = true) (reaches : goals ⊆ initial ++ p) : 10 ≤ p.length := by
  have hh := (required_nodup p).length_le_of_subset (required_in_trace p reaches)
  have ha := three_auxiliaries p hv reaches
  simp only [List.length_append] at hh
  change 7 + (auxiliaries p).length ≤ _ at hh
  omega

def witnessTen : List (BitVec 7) := [17,21,96,104,65,67,48,50,12,62]
theorem witness_valid : validMasks initial witnessTen = true := by decide
theorem witness_reaches : goals ⊆ initial ++ witnessTen := by decide
theorem witness_length : witnessTen.length = 10 := rfl
theorem exact_free_minimum_ten :
    (∃ p : List (BitVec 7), validMasks initial p = true ∧
      goals ⊆ initial ++ p ∧ p.length = 10) ∧
    (∀ p : List (BitVec 7), validMasks initial p = true →
      goals ⊆ initial ++ p → 10 ≤ p.length) :=
  ⟨⟨witnessTen,witness_valid,witness_reaches,witness_length⟩,free_lower_bound_ten⟩

theorem valid_initial_mono (p a b : List (BitVec 7)) (hs : a ⊆ b)
    (hv : validMasks a p = true) : validMasks b p = true := by
  induction p generalizing a b with
  | nil => rfl
  | cons z p ih =>
    simp only [validMasks,Bool.and_eq_true] at hv ⊢
    constructor
    · obtain ⟨x,hx,hy⟩ := List.any_eq_true.mp hv.1
      obtain ⟨y,hy,he⟩ := List.any_eq_true.mp hy
      exact List.any_eq_true.mpr ⟨x,hs hx,List.any_eq_true.mpr ⟨y,hs hy,he⟩⟩
    · apply ih (z :: a) (z :: b) _ hv.2
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hs hx)

theorem original_free_lower_bound_ten (p : List (BitVec 7))
    (hv : validMasks FreeXor.maskBasis p = true)
    (reaches : goals ⊆ FreeXor.maskBasis ++ p) : 10 ≤ p.length := by
  apply free_lower_bound_ten p
  · exact valid_initial_mono p FreeXor.maskBasis initial
      (by intro z hz; exact List.mem_cons_of_mem _ hz) hv
  · intro z hz
    have hh := reaches hz
    simpa only [initial,List.mem_append,List.mem_cons,or_assoc] using Or.inr hh

theorem witness_original_valid : validMasks FreeXor.maskBasis witnessTen = true := by decide
theorem witness_original_reaches : goals ⊆ FreeXor.maskBasis ++ witnessTen := by decide
theorem original_exact_free_minimum_ten :
    (∃ p : List (BitVec 7), validMasks FreeXor.maskBasis p = true ∧
      goals ⊆ FreeXor.maskBasis ++ p ∧ p.length = 10) ∧
    (∀ p : List (BitVec 7), validMasks FreeXor.maskBasis p = true →
      goals ⊆ FreeXor.maskBasis ++ p → 10 ≤ p.length) :=
  ⟨⟨witnessTen,witness_original_valid,witness_original_reaches,witness_length⟩,
    original_free_lower_bound_ten⟩

theorem required_fresh (p : Program) (h : run identity p = TransposeTarget.matrix) :
    goals ++ auxiliaries (trace identity p) ⊆ freshRows (record identity initial p) := by
  intro z hz
  have ni : z ∉ initial := by
    rcases List.mem_append.mp hz with hz | hz
    · exact goals_not_initial z hz
    · intro hi
      exact ((auxiliary_membership _ z).mp hz).2 (by simp [base,hi])
  have ht := required_in_trace (trace identity p) (TransposeTarget.trace_reaches p h) hz
  exact (recorded_value_supported p identity initial z ht).resolve_left ni

theorem fresh_count (p : Program) (h : run identity p = TransposeTarget.matrix) :
    10 ≤ (freshRows (record identity initial p)).length := by
  have hh := (required_nodup (trace identity p)).length_le_of_subset (required_fresh p h)
  have ha := three_auxiliaries (trace identity p)
    (trace_valid p identity initial initial_supported) (TransposeTarget.trace_reaches p h)
  simp only [List.length_append] at hh
  change 7 + (auxiliaries (trace identity p)).length ≤ _ at hh
  omega

theorem oriented_lower_bound (p : Program) (h : run identity p = TransposeTarget.matrix) :
    16 + (touchedSources p).length ≤ p.length := by
  have hf := fresh_count p h
  have hr := TransposeTarget.repeated_count p h
  have he := event_partition p identity initial
  change 6 + (touchedSources p).length ≤ (repeatTargets (record identity initial p)).length at hr
  omega

/-- Transposed-orientation part of source Lemma 4.1. The quantity v is the
number of distinct private outputs ever used as controls in the original word. -/
theorem length_ge_sixteen_plus_v (p : Program) (h : run identity p = target) :
    16 + (TransposeTarget.usedOutputs p).length ≤ p.length := by
  have hh := oriented_lower_bound (oriented p) (TransposeTarget.realizes_oriented p h)
  simpa only [TransposeTarget.touched_sources_length,oriented_length] using hh

theorem short_program_small_sector (p : Program) (h : run identity p = target)
    (hl : p.length ≤ 18) :
    (touchedSources p).length ≤ 2 ∧ (TransposeTarget.usedOutputs p).length ≤ 2 := by
  have hu := length_ge_sixteen_plus_u p h
  have hv := length_ge_sixteen_plus_v p h
  omega

theorem fresh_in_required (p : Program) :
    freshRows (record identity initial p) ⊆ goals ++ auxiliaries (trace identity p) := by
  intro z hz
  have ht := ExactBudget.fresh_in_trace p identity initial hz
  have hn := ExactBudget.fresh_not_seen p identity initial z hz
  by_cases hg : z ∈ goals
  · exact List.mem_append_left _ hg
  · apply List.mem_append_right
    apply (auxiliary_membership _ z).mpr
    refine ⟨ht,?_⟩
    intro hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hn hb
    · exact hg hb

theorem fresh_count_exact (p : Program) (h : run identity p = TransposeTarget.matrix) :
    (freshRows (record identity initial p)).length = 7 + (auxiliaries (trace identity p)).length := by
  have lower := (required_nodup (trace identity p)).length_le_of_subset (required_fresh p h)
  have upper := (ExactBudget.fresh_nodup p identity initial).length_le_of_subset (fresh_in_required p)
  simp only [List.length_append] at lower upper
  change 7 + (auxiliaries (trace identity p)).length ≤ _ at lower
  change _ ≤ 7 + (auxiliaries (trace identity p)).length at upper
  omega

theorem exact_oriented_budget (p : Program) (h : run identity p = TransposeTarget.matrix) :
    3 ≤ (auxiliaries (trace identity p)).length ∧
    p.length = 13 + (auxiliaries (trace identity p)).length +
      (touchedSources p).length + ExactBudget.extraRepeats p := by
  have ha := three_auxiliaries (trace identity p)
    (trace_valid p identity initial initial_supported) (TransposeTarget.trace_reaches p h)
  have hf := fresh_count_exact p h
  have hr := TransposeTarget.repeated_count p h
  have he := event_partition p identity initial
  change 6 + (touchedSources p).length ≤ (repeatTargets (record identity initial p)).length at hr
  change _ ∧ p.length = 13 + (auxiliaries (trace identity p)).length +
    (touchedSources p).length +
    ((repeatTargets (record identity initial p)).length - (6 + (touchedSources p).length))
  omega

theorem two_sources_saturation (p : Program) (h : run identity p = TransposeTarget.matrix)
    (hl : p.length ≤ 18) (hu : (touchedSources p).length = 2) :
    p.length = 18 ∧ (auxiliaries (trace identity p)).length = 3 ∧ ExactBudget.extraRepeats p = 0 := by
  have hb := exact_oriented_budget p h
  omega

theorem one_source_budget (p : Program) (h : run identity p = TransposeTarget.matrix)
    (hl : p.length ≤ 18) (hu : (touchedSources p).length = 1) :
    (auxiliaries (trace identity p)).length + ExactBudget.extraRepeats p ≤ 4 := by
  have hb := exact_oriented_budget p h
  omega

end HGP13.TransposeBudget
