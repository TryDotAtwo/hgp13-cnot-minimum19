import Transposition
import Budget
import TransposeFree

namespace HGP13.TransposeTarget
open Transposition Projection Budget

def rows : List Row := [1,2,4,8,16,32,85,190,259,808,1041,2098,4384]
def matrix : Matrix := fun i => rows[i.val]!

theorem coefficients : ∀ i j : Wire,
    coefficient matrix i j = coefficient target (perm j) (perm i) := by decide

theorem realizes_oriented (p : Program) (h : run identity p = target) :
    run identity (oriented p) = matrix := by
  funext i
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change coefficient (run identity (oriented p)) i ⟨j,hj⟩ = coefficient matrix i ⟨j,hj⟩
  rw [full_program_oriented,h,coefficients]

theorem target_projection : outputWires.map (fun i => project (matrix i)) = TransposeFree.goals := by decide
theorem sources_fixed : ∀ j ∈ sources, matrix j = identity j := by decide
theorem private_ends_nonzero : ∀ j ∈ privateOutputs, project (matrix j) ≠ 0 := by decide

def usedOutputs (p : Program) : List Wire :=
  privateOutputs.filter (fun j => (p.map Prod.fst).contains j)

theorem oriented_targets (p : Program) (j : Wire) :
    j ∈ (oriented p).map Prod.snd ↔ perm j ∈ p.map Prod.fst := by
  have hm : (oriented p).map Prod.snd = (p.map (fun g => perm g.1)).reverse := by
    simp [oriented,rename,dual,List.map_reverse,List.map_map,Function.comp_def,renameGate,swap]
  rw [hm,List.mem_reverse]
  constructor
  · intro hj
    obtain ⟨g,hg,he⟩ := List.mem_map.mp hj
    exact List.mem_map.mpr ⟨g,hg,(perm_eq g.1 j).mp he⟩
  · intro hj
    obtain ⟨g,hg,he⟩ := List.mem_map.mp hj
    exact List.mem_map.mpr ⟨g,hg,(perm_eq g.1 j).mpr he⟩

theorem sources_permuted : privateOutputs.map perm = sources := by decide

theorem touched_sources (p : Program) : touchedSources (oriented p) = (usedOutputs p).map perm := by
  unfold touchedSources usedOutputs
  rw [← sources_permuted,List.filter_map]
  congr 1
  apply List.filter_congr
  intro j hj
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply,List.contains_iff_mem,oriented_targets,perm_involution]

theorem touched_sources_length (p : Program) :
    (touchedSources (oriented p)).length = (usedOutputs p).length := by
  rw [touched_sources,List.length_map]

theorem required_repeat_targets (p : Program) (h : run identity p = matrix) :
    privateOutputs ++ touchedSources p ⊆ repeatTargets (record identity (0 :: FreeXor.maskBasis) p) := by
  intro j hj
  rcases List.mem_append.mp hj with hj | hj
  · obtain ⟨e,he,hj',hf⟩ := first_nonzero_repeat p identity (0 :: FreeXor.maskBasis) j
      initial_supported (private_starts_zero j hj) (by rw [h]; exact private_ends_nonzero j hj)
    rw [← hj']
    exact repeat_target_mem _ e he hf
  · have hs : j ∈ sources := (List.mem_filter.mp hj).1
    have ht : j ∈ p.map Prod.snd := by simpa using (List.mem_filter.mp hj).2
    obtain ⟨e,he,hj',hr⟩ := last_target_result p identity (0 :: FreeXor.maskBasis) j ht
    have hv : project e.row ∈ 0 :: FreeXor.maskBasis := by
      rw [hr,h,sources_fixed j hs]
      exact initial_supported j
    have hf := initially_seen_is_repeat p identity (0 :: FreeXor.maskBasis) e he hv
    rw [← hj']
    exact repeat_target_mem _ e he hf

theorem repeated_count (p : Program) (h : run identity p = matrix) :
    6 + (touchedSources p).length ≤ (repeatTargets (record identity (0 :: FreeXor.maskBasis) p)).length := by
  have hh := (required_targets_nodup p).length_le_of_subset (required_repeat_targets p h)
  simpa only [List.length_append, show privateOutputs.length = 6 from rfl] using hh

theorem trace_reaches (p : Program) (h : run identity p = matrix) :
    TransposeFree.goals ⊆ (0 :: FreeXor.maskBasis) ++ trace identity p := by
  intro z hz
  rw [← target_projection] at hz
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hz
  rw [← h]
  exact final_rows_supported p identity (0 :: FreeXor.maskBasis) initial_supported i

end HGP13.TransposeTarget
