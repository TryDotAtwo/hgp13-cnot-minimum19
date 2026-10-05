import NonzeroRows
import ReturnTracking

namespace HGP13.IndexedEffectiveness
open SectorCover SectorCoordinates SectorIndexing CoreRowEncoding KnownControls
open SharedSearch TransitionChecks PackedRows CoordinateRestriction

theorem gate_endpoints (s : Sector) (hs : s ∈ sectors)
    (g : IndexedGate (changing s) (fixedWires s)) :
    (∃ c, embed s c = (fullGate (changing s) (fixedWires s) g).1) ∧
    (∃ t, embed s t = (fullGate (changing s) (fixedWires s) g).2) := by
  constructor
  · apply (embed_image s _).mpr
    apply List.contains_iff_mem.mp
    exact input_retained s hs _ (List.getElem_mem (by simpa using g.1.isLt))
  · apply (embed_image s _).mpr
    apply List.contains_iff_mem.mp
    exact changing_retained s hs _ (List.getElem_mem g.2.isLt)

theorem indexed_supported (s : Sector) (hs : s ∈ sectors)
    (p : List (IndexedGate (changing s) (fixedWires s))) :
    Supported (embed s) (run identity (p.map (fullGate (changing s) (fixedWires s)))) := by
  obtain ⟨q,hq⟩ := CoordinateRestriction.word_lifts (embed s)
    (p.map (fullGate (changing s) (fixedWires s))) (by
      intro g hg
      obtain ⟨a,_,rfl⟩ := List.mem_map.mp hg
      exact gate_endpoints s hs a)
  rw [← hq]
  exact run_supported (embed s) identity q (identity_supported (embed s))

theorem retained_row_supported (s : Sector) (hs : s ∈ sectors)
    (p : List (IndexedGate (changing s) (fixedWires s))) (i : Wire)
    (hi : keep s i = true) :
    RowSupported (embed s) (run identity (p.map (fullGate (changing s) (fixedWires s))) i) := by
  obtain ⟨k,hk⟩ := (embed_image s i).mpr (List.contains_iff_mem.mp hi)
  intro j hj
  have h := indexed_supported s hs p k j hj
  simpa only [coefficient,hk] using h

theorem raw_step_effective (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : List (IndexedGate (changing s) (fixedWires s)))
    (hp : Legal (p.map (fullGate (changing s) (fixedWires s))))
    (g : IndexedGate (changing s) (fixedWires s)) :
    let c := ofSector s lookup
    let z := rawRun c (initial c) (p.map label)
    value c z (label g) ≠ z.rows[g.2.val]! := by
  let c := ofSector s lookup
  let z := rawRun c (initial c) (p.map label)
  let x := run identity (p.map (fullGate (changing s) (fixedWires s)))
  change value c z (label g) ≠ z.rows[g.2.val]!
  obtain ⟨hd,_,hj⟩ := partition_properties s hs
  obtain ⟨hr,_,hf,_⟩ := initial_matches_full_matrix s hs lookup
  have rr : z.rows = rows (embed s) (changing s) x :=
    raw_rows_run (embed s) (changing s) (fixedWires s) hd hj c
      (count_matches s lookup) p identity (initial c) hr hf
  have hf' : fixed c = rows (embed s) (fixedWires s) x := by
    rw [fixed_run (embed s) (changing s) (fixedWires s) hj]
    exact hf
  have hv : value c z (label g) =
      (pack (embed s) (step x (fullGate (changing s) (fixedWires s) g) (changing s)[g.2.val])).toNat := by
    change (z.rows[g.2.val]! ^^^ (if g.1.val < count c then z.rows[g.1.val]! else (fixed c)[g.1.val-count c]!)) = _
    rw [control_read (embed s) (changing s) (fixedWires s) x c z g.1
      (count_matches s lookup) rr hf',rr,rows_get _ _ _ _ g.2.isLt]
    simp [fullGate,step,pack_nat_xor]
  rw [hv,rr,rows_get _ _ _ _ g.2.isLt]
  apply NonzeroRows.packed_next_changes (embed s) _ hp
  · exact retained_row_supported s hs p _ (changing_retained s hs _ (List.getElem_mem g.2.isLt))
  · have h := retained_row_supported s hs (p ++ [g]) _
      (changing_retained s hs _ (List.getElem_mem g.2.isLt))
    simpa only [List.map_append,List.map_cons,List.map_nil,run_append,run_cons,run_nil,fullGate] using h

theorem effective_after_prefix (s : Sector) (hs : s ∈ sectors)
    (lookup : Nat → Nat → Bool)
    (p q : List (IndexedGate (changing s) (fixedWires s)))
    (hp : Legal ((p ++ q).map (fullGate (changing s) (fixedWires s)))) :
    ReturnTracking.Effective (ofSector s lookup)
      (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (p.map label))
      (q.map label) := by
  induction q generalizing p with
  | nil => trivial
  | cons g q ih =>
    simp only [List.map_cons,ReturnTracking.Effective]
    constructor
    · apply raw_step_effective s hs lookup p
      intro a ha
      apply hp a
      rw [List.map_append]
      exact List.mem_append_left _ ha
    · have he : advance (ofSector s lookup)
          (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (p.map label)) (label g) =
          rawRun (ofSector s lookup) (initial (ofSector s lookup)) ((p ++ [g]).map label) := by
        rw [List.map_append,CounterBudget.raw_append]
        rfl
      rw [he]
      apply ih (p ++ [g])
      simpa only [List.append_assoc,List.singleton_append] using hp

theorem indexed_effective (s : Sector) (hs : s ∈ sectors)
    (lookup : Nat → Nat → Bool)
    (p : List (IndexedGate (changing s) (fixedWires s)))
    (hp : Legal (p.map (fullGate (changing s) (fixedWires s)))) :
    ReturnTracking.Effective (ofSector s lookup) (initial (ofSector s lookup)) (p.map label) := by
  simpa only [List.nil_append,List.map_nil,rawRun] using effective_after_prefix s hs lookup [] p hp

theorem active_index_hit (s : Sector) (hs : s ∈ sectors) (p : Program)
    (hc : Compatible s p) (q : List (IndexedGate (changing s) (fixedWires s)))
    (hq : q.map (fullGate (changing s) (fixedWires s)) = core s p)
    (i : Nat) (hi : i < s.active.length) :
    ∃ g ∈ q.map label, g.1 = i := by
  obtain ⟨a,ha,he⟩ := active_is_used s p hc s.active[i] (List.getElem_mem hi)
  have hm : a ∈ core s p := by
    apply List.mem_filter.mpr
    refine ⟨ha,?_⟩
    rw [he]
    apply changing_retained s hs
    simp [changing,List.getElem_mem hi]
  rw [← hq] at hm
  obtain ⟨g,hg,hga⟩ := List.mem_map.mp hm
  have hlen : i < (changing s).length := by simp [changing]; omega
  have hval : (changing s)[i] = s.active[i] := by simp [changing,hi,List.getElem_append]
  have heq : (changing s)[g.2.val] = (changing s)[i] := by
    rw [hval]
    exact (congrArg Prod.snd hga).trans he
  have hn := (partition_properties s hs).1
  have idx : g.2.val = i := (List.Nodup.getElem_inj hn).mp heq
  exact ⟨label g,List.mem_map.mpr ⟨g,hg,rfl⟩,idx⟩
theorem covered_core_mandatory_count (s : Sector) (hs : s ∈ sectors)
    (lookup : Nat → Nat → Bool) (p : Program) (hp : Legal p)
    (hc : Compatible s p) (real : run identity p = HGP13.target) :
    ∃ q : List (IndexedGate (changing s) (fixedWires s)),
      q.map (fullGate (changing s) (fixedWires s)) = core s p ∧
      q.length = (core s p).length ∧
      s.active.length+s.carriers.length ≤
        CounterBudget.eventCount (ofSector s lookup) (mandatoryEvent (ofSector s lookup))
          (initial (ofSector s lookup)) (q.map label) := by
  obtain ⟨q,hq,hl,ht⟩ := core_raw_target s hs p hc real lookup
  let c := ofSector s lookup
  have hlegal : Legal (q.map (fullGate (changing s) (fixedWires s))) := by
    rw [hq]
    intro g hg
    exact word_legal s p hp g (List.mem_filter.mp hg).1
  have heffective := indexed_effective s hs lookup q hlegal
  have hr : ∀ i ∈ List.range c.sources.length,
      has (rawRun c (initial c) (q.map label)).returned i = true := by
    intro i hi
    have hib : i < c.sources.length := List.mem_range.mp hi
    apply ReturnTracking.target_forces_returned c (q.map label) i hib heffective _ ht
    apply active_index_hit s hs p hc q hq
    simpa only [c,ofSector,List.length_map] using hib
  have hcopy : ∀ i ∈ List.range c.relays.length,
      has (rawRun c (initial c) (q.map label)).copied i = true := by
    intro i hi
    exact MandatoryCount.target_forces_copied s hs lookup (q.map label) ht i (List.mem_range.mp hi)
  have bound := MandatoryCount.mandatory_endpoint_bound c (initial c) (q.map label)
    (List.range c.sources.length) (List.range c.relays.length)
    List.nodup_range List.nodup_range
    (by intro i _; simp [initial,has]) (by intro i _; simp [initial,has]) hr hcopy
  refine ⟨q,hq,hl,?_⟩
  simpa only [List.length_range,c,ofSector,List.length_map] using bound
end HGP13.IndexedEffectiveness




