import CounterBudget

namespace HGP13.KnownControls
open SectorCover SectorCoordinates SectorIndexing CoreRowEncoding
open SharedSearch TransitionChecks PackedRows ProjectedHistory

theorem trace_projection (s : Sector) (hs : s ∈ sectors) (p : Program)
    (ht : ∀ g ∈ p, keep s g.2 = true) (v : Nat) (hv : v < 128) :
    has (projected (traceHistory (embed s) identity p (initialBits s))) v = true ↔
      ∃ r, CleanPersistence.CoreHistory (keep s) p r ∧ (Projection.project r).toNat = v := by
  change has (foldHistory (traceHistory (embed s) identity p
    (encodeHistory ((PassiveInsertion.currentRows (keep s) identity).map
      (fun r => (pack (embed s) r).toNat))))) v = true ↔ _
  rw [traceHistory_encode,← List.map_append,packed_fold_membership s hs _ v hv]
  simp only [produced_history (keep s) p identity ht,PassiveInsertion.historyRows_exact]

theorem current_projection_known (s : Sector) (hs : s ∈ sectors) (p : Program)
    (ht : ∀ g ∈ p, keep s g.2 = true) (i : Wire) (hi : keep s i = true) :
    has (projected (traceHistory (embed s) identity p (initialBits s)))
      (Projection.project (run identity p i)).toNat = true := by
  apply (trace_projection s hs p ht _ (BitVec.isLt _)).mpr
  refine ⟨run identity p i,?_,rfl⟩
  exact ⟨p,[],by simp,i,hi,rfl⟩

theorem input_retained (s : Sector) (hs : s ∈ sectors) (i : Wire)
    (hi : i ∈ changing s ++ fixedWires s) : keep s i = true := by
  rcases List.mem_append.mp hi with ha | hb
  · exact changing_retained s hs i ha
  · apply List.contains_iff_mem.mpr
    have hm : i ∈ Budget.sources := (List.mem_filter.mp hb).1
    simp [layout,hm]

theorem indexed_targets (s : Sector) (hs : s ∈ sectors)
    (p : List (IndexedGate (changing s) (fixedWires s))) :
    ∀ g ∈ p.map (fullGate (changing s) (fixedWires s)), keep s g.2 = true := by
  intro g hg
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hg
  exact changing_retained s hs _ (List.getElem_mem a.2.isLt)

theorem fixed_run {n : Nat} (e : Fin n → Wire) (a b : List Wire)
    (disjoint : ∀ i ∈ a, ∀ j ∈ b, i ≠ j)
    (p : List (IndexedGate a b)) (x : Matrix) :
    rows e b (run x (p.map (fullGate a b))) = rows e b x := by
  induction p generalizing x with
  | nil => rfl
  | cons g p ih =>
    simp only [List.map_cons,run_cons,ih,fullGate]
    exact fixed_rows_step e a b disjoint x _ g.2

theorem raw_control_known (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : List (IndexedGate (changing s) (fixedWires s)))
    (j : Fin ((changing s).length+(fixedWires s).length)) :
    let c := ofSector s lookup
    let z := rawRun c (initial c) (p.map label)
    has (projected z.history)
      ((if j.val < count c then z.rows[j.val]! else (fixed c)[j.val-count c]!) &&& 127) = true := by
  let c := ofSector s lookup
  let z := rawRun c (initial c) (p.map label)
  change has (projected z.history)
    ((if j.val < count c then z.rows[j.val]! else (fixed c)[j.val-count c]!) &&& 127) = true
  obtain ⟨hd,_,hj⟩ := partition_properties s hs
  obtain ⟨hr,hh,hf,_⟩ := initial_matches_full_matrix s hs lookup
  have rr := raw_rows_run (embed s) (changing s) (fixedWires s) hd hj c
    (count_matches s lookup) p identity (initial c) hr hf
  have rh := raw_history_run (embed s) (changing s) (fixedWires s) hd hj c
    (count_matches s lookup) p identity (initial c) hr hf
  have hf' : fixed c = rows (embed s) (fixedWires s)
      (run identity (p.map (fullGate (changing s) (fixedWires s)))) := by
    rw [fixed_run (embed s) (changing s) (fixedWires s) hj]
    exact hf
  rw [control_read (embed s) (changing s) (fixedWires s) _ c z j
    (count_matches s lookup) rr hf',rh,hh]
  rw [show (127 : Nat) = 2^7-1 from rfl,Nat.and_two_pow_sub_one_eq_mod]
  change has (projected (traceHistory (embed s) identity
    (p.map (fullGate (changing s) (fixedWires s))) (initialBits s)))
    ((pack (embed s) (run identity (p.map (fullGate (changing s) (fixedWires s)))
      ((changing s ++ fixedWires s)[j.val]'(by simpa using j.isLt)))).toNat % 128) = true
  rw [packed_mod128]
  apply current_projection_known s hs _ (indexed_targets s hs p)
  exact input_retained s hs _ (List.getElem_mem (by simpa using j.isLt))

theorem raw_copy_is_repeat (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : List (IndexedGate (changing s) (fixedWires s)))
    (g : IndexedGate (changing s) (fixedWires s)) :
    let c := ofSector s lookup
    let z := rawRun c (initial c) (p.map label)
    copyEvent c z (label g) = true → repeatEvent c z (label g) = true := by
  intro c z h
  apply CounterBudget.copy_is_repeat c z (label g) h
  have hk := raw_control_known s hs lookup p g.1
  change (base.contains _ || has (projected z.history) _) = true
  simp only [Bool.or_eq_true]
  exact Or.inr hk

theorem raw_mandatory_is_repeat (s : Sector) (hs : s ∈ sectors)
    (lookup : Nat → Nat → Bool)
    (p : List (IndexedGate (changing s) (fixedWires s)))
    (g : IndexedGate (changing s) (fixedWires s)) :
    let c := ofSector s lookup
    let z := rawRun c (initial c) (p.map label)
    mandatoryEvent c z (label g) = true → repeatEvent c z (label g) = true := by
  intro c z h
  simp only [mandatoryEvent,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with h | h
  · exact CounterBudget.sector_return_is_repeat s hs lookup z (label g) h.1
  · exact raw_copy_is_repeat s hs lookup p g h.1

theorem mandatory_seen_after_prefix (s : Sector) (hs : s ∈ sectors)
    (lookup : Nat → Nat → Bool)
    (p q : List (IndexedGate (changing s) (fixedWires s))) :
    CounterBudget.MandatorySeen (ofSector s lookup)
      (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (p.map label))
      (q.map label) := by
  induction q generalizing p with
  | nil => trivial
  | cons g q ih =>
    simp only [List.map_cons,CounterBudget.MandatorySeen]
    constructor
    · exact raw_mandatory_is_repeat s hs lookup p g
    · have he : advance (ofSector s lookup)
          (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (p.map label)) (label g) =
          rawRun (ofSector s lookup) (initial (ofSector s lookup)) ((p ++ [g]).map label) := by
        rw [List.map_append,CounterBudget.raw_append]
        rfl
      rw [he]
      exact ih (p ++ [g])

theorem indexed_mandatory_seen (s : Sector) (hs : s ∈ sectors)
    (lookup : Nat → Nat → Bool)
    (p : List (IndexedGate (changing s) (fixedWires s))) :
    CounterBudget.MandatorySeen (ofSector s lookup) (initial (ofSector s lookup))
      (p.map label) := by
  simpa only [List.map_nil,rawRun] using mandatory_seen_after_prefix s hs lookup [] p

theorem indexed_repeat_partition (s : Sector) (hs : s ∈ sectors)
    (lookup : Nat → Nat → Bool)
    (p : List (IndexedGate (changing s) (fixedWires s))) :
    let c := ofSector s lookup
    CounterBudget.eventCount c (repeatEvent c) (initial c) (p.map label) =
      extraCount c (initial c) (p.map label) +
      CounterBudget.eventCount c (mandatoryEvent c) (initial c) (p.map label) :=
  CounterBudget.repeat_partition_mandatory _ _ _ (indexed_mandatory_seen s hs lookup p)
end HGP13.KnownControls



