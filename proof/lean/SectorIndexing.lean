import CoreRowEncoding

namespace HGP13.SectorIndexing
open SectorCover SectorCoordinates CoreRowEncoding

def fixedWires (s : Sector) : List Wire :=
  Budget.sources.filter (fun i => !s.active.contains i)

theorem input_member (s : Sector) (i : Wire) (hi : i ∈ layout s) :
    i ∈ changing s ++ fixedWires s := by
  simp only [layout,List.mem_append,List.mem_singleton] at hi
  rcases hi with (hi | hi) | hi
  · by_cases ha : i ∈ s.active
    · simp [changing,ha]
    · simp [fixedWires,hi,ha]
  · simp [changing,hi]
  · simp [changing,hi]

theorem gate_lifts (a b : List Wire) (g : Gate)
    (hc : g.1 ∈ a ++ b) (ht : g.2 ∈ a) :
    ∃ q : IndexedGate a b, fullGate a b q = g := by
  obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hc
  obtain ⟨t,ht,hf⟩ := List.mem_iff_getElem.mp ht
  refine ⟨(⟨j,by simpa using hj⟩,⟨t,ht⟩),?_⟩
  apply Prod.ext
  · exact he
  · exact hf

theorem word_lifts (a b : List Wire) (p : Program)
    (hc : ∀ g ∈ p, g.1 ∈ a ++ b) (ht : ∀ g ∈ p, g.2 ∈ a) :
    ∃ q : List (IndexedGate a b), q.map (fullGate a b) = p ∧ q.length = p.length := by
  induction p with
  | nil => exact ⟨[],rfl,rfl⟩
  | cons g p ih =>
    obtain ⟨r,hr,hl⟩ := ih (fun k hk => hc k (List.mem_cons_of_mem _ hk))
      (fun k hk => ht k (List.mem_cons_of_mem _ hk))
    obtain ⟨h,he⟩ := gate_lifts a b g (hc g List.mem_cons_self) (ht g List.mem_cons_self)
    exact ⟨h :: r,by simp [he,hr],by simp [hl]⟩

theorem core_indexed (s : Sector) (p : Program) (hc : Compatible s p) :
    ∃ q : List (IndexedGate (changing s) (fixedWires s)),
      q.map (fullGate (changing s) (fixedWires s)) = core s p ∧
      q.length = (core s p).length := by
  apply word_lifts
  · intro g hg
    apply input_member
    exact List.contains_iff_mem.mp
      (control_retained s p hc g (List.mem_filter.mp hg).1)
  · exact retained_target_changes s p hc

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem partitions_checked :
    sectors.all (fun s => decide ((changing s ++ fixedWires s).Nodup)) = true := by decide

theorem partition_properties (s : Sector) (hs : s ∈ sectors) :
    (changing s).Nodup ∧ (fixedWires s).Nodup ∧
      ∀ i ∈ changing s, ∀ j ∈ fixedWires s, i ≠ j := by
  apply List.nodup_append.mp
  exact of_decide_eq_true (List.all_eq_true.mp partitions_checked s hs)

theorem count_matches (s : Sector) (lookup : Nat → Nat → Bool) :
    SharedSearch.count (SharedSearch.ofSector s lookup) = (changing s).length := by
  simp [SharedSearch.count, SharedSearch.ofSector, changing]; omega

theorem core_raw_execution (s : Sector) (hs : s ∈ sectors) (p : Program)
    (hc : Compatible s p) (lookup : Nat → Nat → Bool) :
    ∃ q : List (IndexedGate (changing s) (fixedWires s)),
      q.map (fullGate (changing s) (fixedWires s)) = core s p ∧
      q.length = (core s p).length ∧
      (TransitionChecks.rawRun (SharedSearch.ofSector s lookup)
        (SharedSearch.initial (SharedSearch.ofSector s lookup)) (q.map label)).rows =
        ProjectedHistory.rowCodes s (run identity (core s p)) ∧
      (TransitionChecks.rawRun (SharedSearch.ofSector s lookup)
        (SharedSearch.initial (SharedSearch.ofSector s lookup)) (q.map label)).history =
        PackedRows.traceHistory (embed s) identity (core s p) (ProjectedHistory.initialBits s) := by
  obtain ⟨q,hq,hl⟩ := core_indexed s p hc
  obtain ⟨hd,_,hj⟩ := partition_properties s hs
  obtain ⟨hr,hh,hf,_⟩ := SharedSearch.initial_matches_full_matrix s hs lookup
  have rr := raw_rows_run (embed s) (changing s) (fixedWires s) hd hj
    (SharedSearch.ofSector s lookup) (count_matches s lookup) q identity
    (SharedSearch.initial (SharedSearch.ofSector s lookup)) hr hf
  have rh := raw_history_run (embed s) (changing s) (fixedWires s) hd hj
    (SharedSearch.ofSector s lookup) (count_matches s lookup) q identity
    (SharedSearch.initial (SharedSearch.ofSector s lookup)) hr hf
  rw [hq] at rr rh
  rw [hh] at rh
  exact ⟨q,hq,hl,rr,rh⟩
theorem changing_retained (s : Sector) (hs : s ∈ sectors) (i : Wire)
    (hi : i ∈ changing s) : keep s i = true := by
  apply List.contains_iff_mem.mpr
  simp only [changing,List.mem_append,List.mem_singleton] at hi
  rcases hi with (hi | hi) | hi
  · have hm := (layout_properties s hs).2.2.2.1 hi
    simp [layout,hm]
  · simp [layout,hi]
  · simp [layout,hi]

theorem core_final_rows (s : Sector) (hs : s ∈ sectors) (p : Program)
    (hc : Compatible s p) (real : run identity p = target) :
    ProjectedHistory.rowCodes s (run identity (core s p)) =
      ProjectedHistory.rowCodes s (goal s) := by
  have ha := erase_passive_preserves_core (keep s) (word s p)
    (control_retained s p hc) identity identity (fun _ _ => rfl)
  have he : run identity (word s p) = goal s := word_realizes s p real
  unfold ProjectedHistory.rowCodes
  apply List.map_congr_left
  intro i hi
  have hr := ha i (changing_retained s hs i hi)
  rw [he] at hr
  exact congrArg (fun r => (PackedRows.pack (embed s) r).toNat) hr.symm

theorem core_raw_target (s : Sector) (hs : s ∈ sectors) (p : Program)
    (hc : Compatible s p) (real : run identity p = target)
    (lookup : Nat → Nat → Bool) :
    ∃ q : List (IndexedGate (changing s) (fixedWires s)),
      q.map (fullGate (changing s) (fixedWires s)) = core s p ∧
      q.length = (core s p).length ∧
      (TransitionChecks.rawRun (SharedSearch.ofSector s lookup)
        (SharedSearch.initial (SharedSearch.ofSector s lookup)) (q.map label)).rows =
        SharedSearch.want (SharedSearch.ofSector s lookup) := by
  obtain ⟨q,hq,hl,hr,_⟩ := core_raw_execution s hs p hc lookup
  rw [core_final_rows s hs p hc real] at hr
  exact ⟨q,hq,hl,hr.trans (SharedSearch.initial_matches_full_matrix s hs lookup).2.2.2.symm⟩
end HGP13.SectorIndexing



