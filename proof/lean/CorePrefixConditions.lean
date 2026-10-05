import MissingEncoding

namespace HGP13.CorePrefixConditions
open SectorCover SectorCoordinates SectorIndexing CoreRowEncoding
open SharedSearch TransitionChecks PackedRows CleanPersistence

theorem active_count (s : Sector) (hs : s ∈ sectors) (p : Program) (hc : Compatible s p) :
    s.active.length = (Budget.touchedSources (word s p)).length := by
  have ha : s.active.Nodup :=
    (List.nodup_append.mp (List.nodup_append.mp (partition_properties s hs).1).1).1
  have hb : (Budget.touchedSources (word s p)).Nodup := List.Pairwise.filter _ Budget.sources_nodup
  have h1 := ha.length_le_of_subset (fun i hi => (hc.1 i).mp hi)
  have h2 := hb.length_le_of_subset (fun i hi => (hc.1 i).mpr hi)
  omega

theorem core_prefix_conditions (s : Sector) (hs : s ∈ sectors)
    (p : Program) (hp : Legal p) (hc : Compatible s p) (real : run identity p = HGP13.target)
    (short : p.length ≤ 18) (two : s.active.length = 2)
    (a b : Program) (split : core s p = a ++ b) : CoreConditions (keep s) a (goal s) := by
  obtain ⟨x,y,hxy,hxa,_⟩ := List.filter_eq_append_iff.mp split
  have hlegal : Legal (x ++ y) := by rw [← hxy]; exact word_legal s p hp
  have hreal : run identity (x ++ y) = goal s := by rw [← hxy]; exact word_realizes s p real
  have hshort : (x ++ y).length ≤ 18 := by rw [← hxy,word_length]; exact short
  have htwo : (Budget.touchedSources (x ++ y)).length = 2 := by
    rw [← hxy,← active_count s hs p hc]
    exact two
  have controls : ∀ g ∈ x ++ y, keep s g.1 = true := by
    intro g hg
    apply control_retained s p hc g
    rwa [hxy]
  have center : keep s 8 = true := by simp [keep,layout]
  cases ho : s.transposed with
  | false =>
    have hr : run identity (x ++ y) = HGP13.target := by simpa [goal,ho] using hreal
    have h := original_core_conditions (keep s) x y hlegal hr hshort htwo controls center
    simpa only [hxa,goal,ho,Bool.false_eq_true,ite_false] using h
  | true =>
    have hr : run identity (x ++ y) = TransposeTarget.matrix := by simpa [goal,ho] using hreal
    have h := transpose_core_conditions (keep s) x y hlegal hr hshort htwo controls center
    simpa only [hxa,goal,ho,ite_true] using h

theorem indexed_prefix_conditions (s : Sector) (hs : s ∈ sectors)
    (p : Program) (hp : Legal p) (hc : Compatible s p) (real : run identity p = HGP13.target)
    (short : p.length ≤ 18) (two : s.active.length = 2)
    (q a b : List (IndexedGate (changing s) (fixedWires s)))
    (hq : q.map (fullGate (changing s) (fixedWires s)) = core s p) (he : q = a ++ b) :
    CoreConditions (keep s) (a.map (fullGate (changing s) (fixedWires s))) (goal s) := by
  apply core_prefix_conditions s hs p hp hc real short two _ (b.map (fullGate (changing s) (fixedWires s)))
  rw [← hq,he,List.map_append]

theorem trace_contains_history (s : Sector) (p : Program)
    (targets : ∀ g ∈ p, keep s g.2 = true) (r : Row)
    (history : CoreHistory (keep s) p r) :
    has (traceHistory (embed s) identity p (ProjectedHistory.initialBits s)) (pack (embed s) r).toNat = true := by
  unfold ProjectedHistory.initialBits
  rw [traceHistory_encode,← List.map_append,has_history]
  apply List.mem_map.mpr
  refine ⟨r,?_,rfl⟩
  apply (produced_history (keep s) p identity targets r).mpr
  exact (PassiveInsertion.historyRows_exact (keep s) p r).mpr history

theorem raw_contains_history (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (a : List (IndexedGate (changing s) (fixedWires s))) (r : Row)
    (history : CoreHistory (keep s) (a.map (fullGate (changing s) (fixedWires s))) r) :
    has (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (a.map label)).history
      (pack (embed s) r).toNat = true := by
  obtain ⟨hd,_,hj⟩ := partition_properties s hs
  obtain ⟨hr,hh,hf,_⟩ := initial_matches_full_matrix s hs lookup
  have rh := raw_history_run (embed s) (changing s) (fixedWires s) hd hj
    (ofSector s lookup) (count_matches s lookup) a identity (initial (ofSector s lookup)) hr hf
  rw [rh,hh]
  exact trace_contains_history s _ (KnownControls.indexed_targets s hs a) r history

theorem raw_projected_reflects (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (a : List (IndexedGate (changing s) (fixedWires s))) (v : BitVec 7)
    (h : has (projected (rawRun (ofSector s lookup) (initial (ofSector s lookup))
      (a.map label)).history) v.toNat = true) :
    CleanPersistence.ProjectedHistory (keep s) (a.map (fullGate (changing s) (fixedWires s))) v := by
  obtain ⟨hd,_,hj⟩ := partition_properties s hs
  obtain ⟨hr,hh,hf,_⟩ := initial_matches_full_matrix s hs lookup
  have rh := raw_history_run (embed s) (changing s) (fixedWires s) hd hj
    (ofSector s lookup) (count_matches s lookup) a identity (initial (ofSector s lookup)) hr hf
  rw [rh,hh] at h
  obtain ⟨r,hist,he⟩ := (KnownControls.trace_projection s hs
    (a.map (fullGate (changing s) (fixedWires s))) (KnownControls.indexed_targets s hs a)
    v.toNat (BitVec.isLt v)).mp h
  exact ⟨r,hist,BitVec.eq_of_toNat_eq he⟩

def PassiveLiterals (s : Sector) : Prop :=
  SharedSearch.passive (ofSector s (fun _ _ => true)) =
    (SectorCoordinates.passive s).map (fun j => (Projection.project (goal s j)).toNat) ∧
  ∀ j : Wire, j ∈ Budget.privateOutputs →
    (pack (embed s) (identity j ^^^ goal s j)).toNat = (Projection.project (goal s j)).toNat

instance (s : Sector) : Decidable (PassiveLiterals s) := by
  unfold PassiveLiterals
  infer_instance

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem passive_literals_checked : sectors.all (fun s => decide (PassiveLiterals s)) = true := by decide

theorem passive_literals (s : Sector) (hs : s ∈ sectors) : PassiveLiterals s :=
  of_decide_eq_true (List.all_eq_true.mp passive_literals_checked s hs)

theorem passive_history_present (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : Program) (hp : Legal p) (hc : Compatible s p) (real : run identity p = HGP13.target)
    (short : p.length ≤ 18) (two : s.active.length = 2)
    (q a b : List (IndexedGate (changing s) (fixedWires s)))
    (hq : q.map (fullGate (changing s) (fixedWires s)) = core s p) (he : q = a ++ b)
    (v : Nat) (hv : v ∈ SharedSearch.passive (ofSector s lookup))
    (known : has (projected (rawRun (ofSector s lookup) (initial (ofSector s lookup))
      (a.map label)).history) v = true) :
    has (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (a.map label)).history v = true := by
  obtain ⟨hlit,hdelta⟩ := passive_literals s hs
  have hlist : SharedSearch.passive (ofSector s lookup) =
      (SectorCoordinates.passive s).map (fun j => (Projection.project (goal s j)).toNat) := hlit
  rw [hlist] at hv
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
  have hjprivate : j ∈ Budget.privateOutputs := (List.mem_filter.mp hj).1
  have hjkeep := ((passive_properties s hs).2.2.1 j).mp hj
  have conditions := indexed_prefix_conditions s hs p hp hc real short two q a b hq he
  have appeared := raw_projected_reflects s hs lookup a (Projection.project (goal s j)) known
  have hist := conditions.2.2 j hjprivate hjkeep appeared
  have result := raw_contains_history s hs lookup a (identity j ^^^ goal s j) hist
  rwa [hdelta j hjprivate] at result

theorem state_passive_false (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : Program) (hp : Legal p) (hc : Compatible s p) (real : run identity p = HGP13.target)
    (short : p.length ≤ 18) (two : s.active.length = 2)
    (q a b : List (IndexedGate (changing s) (fixedWires s)))
    (hq : q.map (fullGate (changing s) (fixedWires s)) = core s p) (he : q = a ++ b) :
    (SharedSearch.passive (ofSector s lookup)).any (fun v =>
      has (projected (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (a.map label)).history) v &&
        !has (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (a.map label)).history v) = false := by
  simp only [List.any_eq_false]
  intro v hv
  by_cases known : has (projected (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (a.map label)).history) v = true
  · have hh := passive_history_present s hs lookup p hp hc real short two q a b hq he v hv known
    simp [hh]
  · have hh := Bool.eq_false_iff.mpr known
    simp [hh]

theorem proposal_passive (c : Config) (depth : Nat) (z : State) (t j : Nat) :
    (propose c depth z t j).passiveBad =
      (SharedSearch.passive c).any (fun v => has (projected (advance c z (t,j)).history) v &&
        !has (advance c z (t,j)).history v) := by rfl

theorem core_passive_guard (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : Program) (hp : Legal p) (hc : Compatible s p) (real : run identity p = HGP13.target)
    (short : p.length ≤ 18) (two : s.active.length = 2)
    (q a b : List (IndexedGate (changing s) (fixedWires s)))
    (g : IndexedGate (changing s) (fixedWires s))
    (hq : q.map (fullGate (changing s) (fixedWires s)) = core s p) (he : q = a ++ g :: b) :
    (propose (ofSector s lookup) a.length
      (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (a.map label)) g.2.val g.1.val).passiveBad = false := by
  rw [proposal_passive]
  have hsplit : q = (a ++ [g]) ++ b := by simpa only [List.append_assoc,List.singleton_append] using he
  have h := state_passive_false s hs lookup p hp hc real short two q (a ++ [g]) b hq hsplit
  simpa only [List.map_append,List.map_cons,List.map_nil,CounterBudget.raw_append,rawRun,label] using h
end HGP13.CorePrefixConditions

