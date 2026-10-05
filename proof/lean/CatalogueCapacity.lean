import CorePrefixConditions
namespace HGP13.CatalogueCapacity
open Budget Projection FreeXor SectorCover SectorCoordinates SectorIndexing CoreRowEncoding
open SharedSearch TransitionChecks RepeatErasure

def fullAux (s : Sector) (p : Program) : List (BitVec 7) :=
  if s.transposed then TransposeBudget.auxiliaries (trace identity (word s p))
  else maskAuxiliaries (trace identity (word s p))

theorem word_fresh_exact (s : Sector) (p : Program) (real : run identity p = HGP13.target) :
    (freshRows (record identity (0 :: maskBasis) (word s p))).length = 7 + (fullAux s p).length := by
  have hr := word_realizes s p real
  cases h : s.transposed with
  | false =>
    simp only [h,Bool.false_eq_true,ite_false] at hr
    simpa only [fullAux,h,Bool.false_eq_true,ite_false] using ExactBudget.fresh_count_exact (word s p) hr
  | true =>
    simp only [h,ite_true] at hr
    simpa only [fullAux,h,ite_true,TransposeFree.initial] using TransposeBudget.fresh_count_exact (word s p) hr

theorem covered_aux_budget (s : Sector) (hs : s ∈ sectors)
    (lookup : Nat → Nat → Bool) (p : Program) (hp : Legal p)
    (hc : Compatible s p) (real : run identity p = HGP13.target) :
    ∃ q : List (IndexedGate (changing s) (fixedWires s)),
      q.map (fullGate (changing s) (fixedWires s)) = core s p ∧
      q.length = (core s p).length ∧
      (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (q.map label)).extra +
        13+s.active.length+(fullAux s p).length ≤ p.length := by
  obtain ⟨q,hq,hl,hm⟩ := IndexedEffectiveness.covered_core_mandatory_count s hs lookup p hp hc real
  have rawBound := raw_repeat_bound s hs lookup q
  rw [hq] at rawBound
  have fullBound := core_plus_passive_repeats s hs p hc real
  have split := KnownControls.indexed_repeat_partition s hs lookup q
  have count := raw_extra (ofSector s lookup) (initial (ofSector s lookup)) (q.map label)
  have fresh := word_fresh_exact s p real
  have partition := event_partition (word s p) identity (0 :: maskBasis)
  have hqsmall := (layout_properties s hs).2.2.1
  rw [word_length] at partition
  change (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (q.map label)).extra =
    0 + extraCount (ofSector s lookup) (initial (ofSector s lookup)) (q.map label) at count
  dsimp only at split
  refine ⟨q,hq,hl,?_⟩
  omega

theorem covered_prefix_capacity (s : Sector) (hs : s ∈ sectors)
    (lookup : Nat → Nat → Bool) (p : Program) (hp : Legal p)
    (hc : Compatible s p) (real : run identity p = HGP13.target) (short : p.length ≤ 18) :
    ∃ q : List (IndexedGate (changing s) (fixedWires s)),
      q.map (fullGate (changing s) (fixedWires s)) = core s p ∧
      q.length = (core s p).length ∧
      ∀ a b, q.map label = a ++ b →
        (fullAux s p).length ≤ 5 - (ofSector s lookup).sources.length -
          (rawRun (ofSector s lookup) (initial (ofSector s lookup)) a).extra := by
  obtain ⟨q,hq,hl,hbound⟩ := covered_aux_budget s hs lookup p hp hc real
  refine ⟨q,hq,hl,?_⟩
  intro a b he
  have mono := CounterBudget.extra_prefix (ofSector s lookup) (initial (ofSector s lookup)) a b
  rw [← he] at mono
  have ns : (ofSector s lookup).sources.length = s.active.length := by simp [ofSector]
  rw [ns]
  omega
end HGP13.CatalogueCapacity

