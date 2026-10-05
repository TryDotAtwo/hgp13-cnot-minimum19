import IndexedEffectiveness

namespace HGP13.RepeatErasure
open Budget Projection FreeXor

def repeats (select : Wire → Bool) (x : Matrix) (seen : List (BitVec 7)) : Program → Nat
  | [] => 0
  | g :: p =>
      (if select g.2 && seen.contains (project (step x g g.2)) then 1 else 0) +
      repeats select (step x g) (project (step x g g.2) :: seen) p

theorem repeats_record (select : Wire → Bool) (x : Matrix) (seen : List (BitVec 7)) (p : Program) :
    repeats select x seen p = ((repeatTargets (record x seen p)).filter select).length := by
  induction p generalizing x seen with
  | nil => rfl
  | cons g p ih =>
    simp only [repeats,ih,record,repeatTargets,headEvent]
    cases hs : seen.contains (project (step x g g.2)) <;> cases ht : select g.2 <;>
      simp [hs,ht] <;> omega

theorem all_repeats (x : Matrix) (seen : List (BitVec 7)) (p : Program) :
    repeats (fun _ => true) x seen p = (repeatTargets (record x seen p)).length := by
  rw [repeats_record]
  simp

theorem seen_increment (small large : List (BitVec 7)) (sub : small ⊆ large) (v : BitVec 7) :
    (if small.contains v then 1 else 0) ≤ (if large.contains v then 1 else 0) := by
  by_cases h : v ∈ small
  · have hl := sub h
    simp [h,hl]
  · simp [h]

theorem erasure_bound (keep : Wire → Bool) (p : Program)
    (controls : ∀ g ∈ p, keep g.1 = true)
    (x y : Matrix) (large small : List (BitVec 7))
    (agree : AgreeOn keep x y) (sub : small ⊆ large) :
    repeats (fun _ => true) y small (p.filter (fun g => keep g.2)) ≤
      repeats keep x large p := by
  induction p generalizing x y large small with
  | nil => exact Nat.le_refl _
  | cons g p ih =>
    have hcontrol := controls g List.mem_cons_self
    have tail : ∀ a ∈ p, keep a.1 = true := fun a ha => controls a (List.mem_cons_of_mem _ ha)
    cases ht : keep g.2 with
    | false =>
      have ha : AgreeOn keep (step x g) y := by
        intro i hi
        exact (passive_step_agrees x g ht i hi).trans (agree i hi)
      have hsub : small ⊆ project (step x g g.2) :: large := by
        intro v hv
        exact List.mem_cons_of_mem _ (sub hv)
      have hb := ih tail (step x g) y _ small ha hsub
      simpa only [List.filter_cons,ht,Bool.false_eq_true,ite_false,repeats,
        Bool.false_and,Nat.zero_add] using hb
    | true =>
      have ha := step_agrees g agree hcontrol
      have he := congrArg project (ha g.2 ht)
      have hsub : project (step y g g.2) :: small ⊆ project (step x g g.2) :: large := by
        rw [he]
        intro v hv
        rcases List.mem_cons.mp hv with hv | hv
        · exact List.mem_cons.mpr (Or.inl hv)
        · exact List.mem_cons_of_mem _ (sub hv)
      have hb := ih tail (step x g) (step y g) _ _ ha hsub
      rw [he] at hb
      have hi := seen_increment small large sub (project (step y g g.2))
      simp only [List.filter_cons,ht,ite_true,repeats,Bool.true_and,he]
      omega

theorem passive_repeat_bound (s : SectorCover.Sector) (hs : s ∈ SectorCover.sectors)
    (p : Program) (real : run identity p = SectorCoordinates.goal s) :
    (SectorCoordinates.passive s).length ≤
      ((repeatTargets (record identity (0 :: maskBasis) p)).filter
        (fun j => !SectorCoordinates.keep s j)).length := by
  obtain ⟨hd,_,hpass,_⟩ := SectorCoordinates.passive_properties s hs
  apply hd.length_le_of_subset
  intro j hj
  have hp : j ∈ privateOutputs := (List.mem_filter.mp hj).1
  have hkeep := (hpass j).mp hj
  have hend : project (run identity p j) ≠ 0 := by
    rw [real]
    unfold SectorCoordinates.goal
    split
    · exact TransposeTarget.private_ends_nonzero j hp
    · exact private_ends_nonzero j hp
  obtain ⟨e,he,ht,hf⟩ := first_nonzero_repeat p identity (0 :: maskBasis) j
    initial_supported (private_starts_zero j hp) hend
  apply List.mem_filter.mpr
  constructor
  · rw [← ht]
    exact repeat_target_mem _ e he hf
  · simp [hkeep]

theorem core_plus_passive_repeats (s : SectorCover.Sector) (hs : s ∈ SectorCover.sectors)
    (p : Program) (hc : SectorCover.Compatible s p) (real : run identity p = HGP13.target) :
    repeats (fun _ => true) identity (0 :: maskBasis) (SectorCoordinates.core s p) +
      (6-s.carriers.length) ≤
      (repeatTargets (record identity (0 :: maskBasis) (SectorCover.word s p))).length := by
  have hcore := erasure_bound (SectorCoordinates.keep s) (SectorCover.word s p)
    (SectorCoordinates.control_retained s p hc) identity identity (0 :: maskBasis) (0 :: maskBasis)
    (fun _ _ => rfl) (fun _ h => h)
  have hp := passive_repeat_bound s hs (SectorCover.word s p) (SectorCover.word_realizes s p real)
  have partition := CountHelpers.filter_partition (SectorCoordinates.keep s)
    (repeatTargets (record identity (0 :: maskBasis) (SectorCover.word s p)))
  have hlen := (SectorCoordinates.passive_properties s hs).2.1
  rw [repeats_record (SectorCoordinates.keep s) identity (0 :: maskBasis) (SectorCover.word s p)] at hcore
  change repeats (fun _ => true) identity (0 :: maskBasis) (SectorCoordinates.core s p) ≤ _ at hcore
  omega
open SectorCover SectorCoordinates SectorIndexing CoreRowEncoding
open SharedSearch TransitionChecks PackedRows

theorem raw_history_seen (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : List (IndexedGate (changing s) (fixedWires s))) (v : BitVec 7)
    (h : has (projected (rawRun (ofSector s lookup) (initial (ofSector s lookup))
      (p.map label)).history) v.toNat = true) :
    v ∈ TightRepeats.seenAfter identity (0 :: maskBasis)
      (p.map (fullGate (changing s) (fixedWires s))) := by
  obtain ⟨hd,_,hj⟩ := partition_properties s hs
  obtain ⟨hr,hh,hf,_⟩ := initial_matches_full_matrix s hs lookup
  have rh := raw_history_run (embed s) (changing s) (fixedWires s) hd hj
    (ofSector s lookup) (count_matches s lookup) p identity (initial (ofSector s lookup)) hr hf
  rw [rh,hh] at h
  obtain ⟨r,history,he⟩ := (KnownControls.trace_projection s hs
    (p.map (fullGate (changing s) (fixedWires s))) (KnownControls.indexed_targets s hs p)
    v.toNat (BitVec.isLt v)).mp h
  have hv : project r = v := BitVec.eq_of_toNat_eq he
  rw [← hv]
  exact CleanPersistence.core_history_projected _ _ _ history

theorem base_agreement : ∀ v : BitVec 7,
    SharedSearch.base.contains v.toNat = (0 :: maskBasis).contains v := by decide

theorem raw_seen_reflects (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : List (IndexedGate (changing s) (fixedWires s))) (v : BitVec 7)
    (h : (SharedSearch.base.contains v.toNat ||
      has (projected (rawRun (ofSector s lookup) (initial (ofSector s lookup))
        (p.map label)).history) v.toNat) = true) :
    v ∈ TightRepeats.seenAfter identity (0 :: maskBasis)
      (p.map (fullGate (changing s) (fixedWires s))) := by
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · rw [base_agreement] at h
    apply (TightRepeats.seenAfter_members _ _ _ _).mpr
    exact List.mem_append_left _ (List.contains_iff_mem.mp h)
  · exact raw_history_seen s hs lookup p v h
theorem raw_value_projection (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : List (IndexedGate (changing s) (fixedWires s)))
    (g : IndexedGate (changing s) (fixedWires s)) :
    value (ofSector s lookup) (rawRun (ofSector s lookup) (initial (ofSector s lookup))
      (p.map label)) (label g) &&& 127 =
      (project (step (run identity (p.map (fullGate (changing s) (fixedWires s))))
        (fullGate (changing s) (fixedWires s) g) (changing s)[g.2.val])).toNat := by
  let c := ofSector s lookup
  let z := rawRun c (initial c) (p.map label)
  let x := run identity (p.map (fullGate (changing s) (fixedWires s)))
  obtain ⟨hd,_,hj⟩ := partition_properties s hs
  obtain ⟨hr,_,hf,_⟩ := initial_matches_full_matrix s hs lookup
  have rr : z.rows = rows (embed s) (changing s) x :=
    raw_rows_run (embed s) (changing s) (fixedWires s) hd hj c
      (count_matches s lookup) p identity (initial c) hr hf
  have hf' : fixed c = rows (embed s) (fixedWires s) x := by
    rw [KnownControls.fixed_run (embed s) (changing s) (fixedWires s) hj]
    exact hf
  have hv : value c z (label g) =
      (pack (embed s) (step x (fullGate (changing s) (fixedWires s) g) (changing s)[g.2.val])).toNat := by
    change (z.rows[g.2.val]! ^^^ (if g.1.val < count c then z.rows[g.1.val]! else (fixed c)[g.1.val-count c]!)) = _
    rw [control_read (embed s) (changing s) (fixedWires s) x c z g.1
      (count_matches s lookup) rr hf',rr,rows_get _ _ _ _ g.2.isLt]
    simp [fullGate,step,pack_nat_xor]
  change value c z (label g) &&& 127 = _
  rw [hv,show (127 : Nat) = 2^7-1 from rfl,Nat.and_two_pow_sub_one_eq_mod]
  exact ProjectedHistory.packed_mod128 s _

theorem raw_repeat_reflects (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : List (IndexedGate (changing s) (fixedWires s)))
    (g : IndexedGate (changing s) (fixedWires s))
    (h : repeatEvent (ofSector s lookup)
      (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (p.map label)) (label g) = true) :
    project (step (run identity (p.map (fullGate (changing s) (fixedWires s))))
      (fullGate (changing s) (fixedWires s) g) (fullGate (changing s) (fixedWires s) g).2) ∈
        TightRepeats.seenAfter identity (0 :: maskBasis) (p.map (fullGate (changing s) (fixedWires s))) := by
  apply raw_seen_reflects s hs lookup p
  simpa only [repeatEvent,raw_value_projection s hs lookup p g,fullGate] using h

theorem raw_repeat_bound_after_prefix (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p q : List (IndexedGate (changing s) (fixedWires s))) :
    CounterBudget.eventCount (ofSector s lookup) (repeatEvent (ofSector s lookup))
      (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (p.map label)) (q.map label) ≤
    repeats (fun _ => true) (run identity (p.map (fullGate (changing s) (fixedWires s))))
      (TightRepeats.seenAfter identity (0 :: maskBasis) (p.map (fullGate (changing s) (fixedWires s))))
      (q.map (fullGate (changing s) (fixedWires s))) := by
  induction q generalizing p with
  | nil => exact Nat.le_refl _
  | cons g q ih =>
    have tail := ih (p ++ [g])
    simp only [List.map_append,List.map_cons,List.map_nil,CounterBudget.raw_append,rawRun,
      run_append,run_cons,run_nil,CleanPersistence.seenAfter_append,TightRepeats.seenAfter] at tail
    have head : (if repeatEvent (ofSector s lookup)
        (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (p.map label)) (label g) then 1 else 0) ≤
        (if (TightRepeats.seenAfter identity (0 :: maskBasis)
          (p.map (fullGate (changing s) (fixedWires s)))).contains
            (project (step (run identity (p.map (fullGate (changing s) (fixedWires s))))
              (fullGate (changing s) (fixedWires s) g) (fullGate (changing s) (fixedWires s) g).2)) then 1 else 0) := by
      by_cases h : repeatEvent (ofSector s lookup)
        (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (p.map label)) (label g) = true
      · have hm := List.contains_iff_mem.mpr (raw_repeat_reflects s hs lookup p g h)
        simp only [h,hm,ite_true]
        exact Nat.le_refl _
      · simp [h]
    simp only [List.map_cons,CounterBudget.eventCount,repeats,Bool.true_and]
    omega

theorem raw_repeat_bound (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : List (IndexedGate (changing s) (fixedWires s))) :
    CounterBudget.eventCount (ofSector s lookup) (repeatEvent (ofSector s lookup))
      (initial (ofSector s lookup)) (p.map label) ≤
    repeats (fun _ => true) identity (0 :: maskBasis)
      (p.map (fullGate (changing s) (fixedWires s))) := by
  simpa only [List.map_nil,rawRun,run_nil,TightRepeats.seenAfter] using
    raw_repeat_bound_after_prefix s hs lookup [] p
theorem word_fresh_ten (s : Sector) (p : Program) (real : run identity p = HGP13.target) :
    10 ≤ (freshRows (record identity (0 :: maskBasis) (word s p))).length := by
  have hr := word_realizes s p real
  cases h : s.transposed with
  | false =>
    simp only [h,Bool.false_eq_true,ite_false] at hr
    exact Budget.fresh_count (word s p) hr
  | true =>
    simp only [h,ite_true] at hr
    exact TransposeBudget.fresh_count (word s p) hr

theorem covered_extra_length_bound (s : Sector) (hs : s ∈ sectors)
    (lookup : Nat → Nat → Bool) (p : Program) (hp : Legal p)
    (hc : Compatible s p) (real : run identity p = HGP13.target) :
    ∃ q : List (IndexedGate (changing s) (fixedWires s)),
      q.map (fullGate (changing s) (fixedWires s)) = core s p ∧
      q.length = (core s p).length ∧
      (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (q.map label)).extra +
        16+s.active.length ≤ p.length := by
  obtain ⟨q,hq,hl,hm⟩ := IndexedEffectiveness.covered_core_mandatory_count s hs lookup p hp hc real
  have rawBound := raw_repeat_bound s hs lookup q
  rw [hq] at rawBound
  have fullBound := core_plus_passive_repeats s hs p hc real
  have split := KnownControls.indexed_repeat_partition s hs lookup q
  have count := raw_extra (ofSector s lookup) (initial (ofSector s lookup)) (q.map label)
  have fresh := word_fresh_ten s p real
  have partition := event_partition (word s p) identity (0 :: maskBasis)
  have hqsmall := (layout_properties s hs).2.2.1
  rw [word_length] at partition
  change (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (q.map label)).extra =
    0 + extraCount (ofSector s lookup) (initial (ofSector s lookup)) (q.map label) at count
  dsimp only at split
  refine ⟨q,hq,hl,?_⟩
  omega

theorem covered_extra_guards (s : Sector) (hs : s ∈ sectors)
    (lookup : Nat → Nat → Bool) (p : Program) (hp : Legal p)
    (hc : Compatible s p) (real : run identity p = HGP13.target) (short : p.length ≤ 18) :
    ∃ q : List (IndexedGate (changing s) (fixedWires s)),
      q.map (fullGate (changing s) (fixedWires s)) = core s p ∧
      q.length = (core s p).length ∧
      ∀ a g b, q.map label = a ++ g :: b →
        (propose (ofSector s lookup) a.length
          (rawRun (ofSector s lookup) (initial (ofSector s lookup)) a) g.1 g.2).extraBad = false := by
  obtain ⟨q,hq,hl,hbound⟩ := covered_extra_length_bound s hs lookup p hp hc real
  have hb : (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (q.map label)).extra ≤
      2-(ofSector s lookup).sources.length := by
    have hn : (ofSector s lookup).sources.length = s.active.length := by simp [ofSector]
    rw [hn]
    omega
  refine ⟨q,hq,hl,?_⟩
  intro a g b he
  rw [he] at hb
  simpa only [Nat.zero_add] using CounterBudget.extra_guard_of_endpoint_bound
    (ofSector s lookup) 0 (initial (ofSector s lookup)) a b g hb
end HGP13.RepeatErasure






