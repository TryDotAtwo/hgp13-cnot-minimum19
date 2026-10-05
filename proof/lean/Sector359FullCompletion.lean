import Sector359Agreement
import FullPackedCompletion

namespace HGP13.Sector359FullCompletion

open SectorCoordinates CoreRowEncoding TransitionChecks

/-- The decoded terminal bitset contains every actual full-width row that
occurred on a retained wire of the selected core word. -/
theorem history_mem_decode (p : Program)
    (hs : Sector359Encoding.sector ∈ SectorCover.sectors)
    (hc : SectorCover.Compatible Sector359Encoding.sector p)
    (lookup : Nat → Nat → Bool)
    (q : List (IndexedGate (changing Sector359Encoding.sector)
      (SectorIndexing.fixedWires Sector359Encoding.sector)))
    (hq : q.map (fullGate (changing Sector359Encoding.sector)
      (SectorIndexing.fixedWires Sector359Encoding.sector)) =
        core Sector359Encoding.sector p)
    (r : Row)
    (hr : r ∈ PassiveInsertion.historyRows
      (keep Sector359Encoding.sector) identity
      (core Sector359Encoding.sector p)) :
    r ∈ SectorCost359.decode
      (rawRun (SharedSearch.ofSector Sector359Encoding.sector lookup)
        (SharedSearch.initial (SharedSearch.ofSector Sector359Encoding.sector lookup))
        (q.map label)).history := by
  have hrs := PackedRows.actual_history_supported Sector359Encoding.sector p hc r hr
  have hb := (FullWordPath.selected_history_exact Sector359Encoding.sector hs
    lookup p hc q hq r hrs).mpr hr
  unfold SectorCost359.decode
  apply List.mem_map.mpr
  refine ⟨(PackedRows.pack (embed Sector359Encoding.sector) r).toNat,?_,?_⟩
  · apply List.mem_filter.mpr
    exact ⟨List.mem_range.mpr (PackedRows.pack (embed Sector359Encoding.sector) r).isLt,hb⟩
  · change Sector359Encoding.liftMask
      (PackedRows.pack (embed Sector359Encoding.sector) r) = r
    exact Sector359Encoding.unpack_actual r hrs

theorem selected_decode_covers (p : Program)
    (hs : Sector359Encoding.sector ∈ SectorCover.sectors)
    (hc : SectorCover.Compatible Sector359Encoding.sector p)
    (lookup : Nat → Nat → Bool)
    (q : List (IndexedGate (changing Sector359Encoding.sector)
      (SectorIndexing.fixedWires Sector359Encoding.sector)))
    (hq : q.map (fullGate (changing Sector359Encoding.sector)
      (SectorIndexing.fixedWires Sector359Encoding.sector)) =
        core Sector359Encoding.sector p) :
    PassiveCost.CoversHistory (keep Sector359Encoding.sector) identity
      (SectorCover.word Sector359Encoding.sector p)
      (SectorCost359.decode
        (rawRun (SharedSearch.ofSector Sector359Encoding.sector lookup)
          (SharedSearch.initial (SharedSearch.ofSector Sector359Encoding.sector lookup))
          (q.map label)).history) := by
  let s := Sector359Encoding.sector
  have controls : ∀ g ∈ SectorCover.word s p, keep s g.1 = true :=
    SectorCoordinates.control_retained s p hc
  have cover := PassiveInsertion.erased_history_covers (keep s)
    (SectorCover.word s p) (core s p) controls rfl
  intro a b he i hi
  exact history_mem_decode p hs hc lookup q hq _ (cover a b he i hi)

theorem path_reach {d : Nat} {s z : SharedSearch.State}
    {q : List (Nat × Nat)}
    (h : TransitionChecks.Path SectorGraph359.config d s q z) :
    SectorGraph359.Reach d s q.length z := by
  induction h with
  | nil d s => exact SectorGraph359.Reach.refl d s
  | @cons d s g q t z hm hp ih =>
    apply SectorGraph359.Reach.step
    · exact (SharedSearch.next_iff _ _ _ _).mpr
        ⟨g.1, (TransitionChecks.admissible_indices _ _ _ _ _
          ((TransitionChecks.move_eq_some_iff _ _ _ _ _ _).mp hm).1).1,
          g.2, (TransitionChecks.admissible_indices _ _ _ _ _
            ((TransitionChecks.move_eq_some_iff _ _ _ _ _ _).mp hm).1).2.1, hm⟩
    · exact ih

theorem no_short_full_word_from_costs (p : Program)
    (hp : Legal p) (hc : SectorCover.Compatible Sector359Encoding.sector p)
    (real : run identity p = HGP13.target) (short : p.length ≤ 18)
    (hs : Sector359Encoding.sector ∈ SectorCover.sectors)
    (lookup : Nat → Nat → Bool)
    (hlookup : SectorGraph359.config = SharedSearch.ofSector
      Sector359Encoding.sector lookup)
    (q : List (IndexedGate (changing Sector359Encoding.sector)
      (SectorIndexing.fixedWires Sector359Encoding.sector)))
    (hq : q.map (fullGate (changing Sector359Encoding.sector)
      (SectorIndexing.fixedWires Sector359Encoding.sector)) =
        core Sector359Encoding.sector p)
    (hlen : q.length ≤ 12)
    (hpath : TransitionChecks.Path
      (SharedSearch.ofSector Sector359Encoding.sector lookup) 0
      (SharedSearch.initial (SharedSearch.ofSector Sector359Encoding.sector lookup))
      (q.map label)
      (rawRun (SharedSearch.ofSector Sector359Encoding.sector lookup)
        (SharedSearch.initial (SharedSearch.ofSector Sector359Encoding.sector lookup))
        (q.map label)))
    (hterminal : SharedSearch.terminal
      (SharedSearch.ofSector Sector359Encoding.sector lookup)
      (rawRun (SharedSearch.ofSector Sector359Encoding.sector lookup)
        (SharedSearch.initial (SharedSearch.ofSector Sector359Encoding.sector lookup))
        (q.map label)) = true) : False := by
  let s := Sector359Encoding.sector
  let z := rawRun (SharedSearch.ofSector s lookup)
    (SharedSearch.initial (SharedSearch.ofSector s lookup)) (q.map label)
  let d := SectorCost359.decode z.history
  have hreach : SectorGraph359.Reach 0
      (SharedSearch.initial SectorGraph359.config) q.length z := by
    have hpath' : TransitionChecks.Path SectorGraph359.config 0
        (SharedSearch.initial SectorGraph359.config) (q.map label) z := by
      rw [hlookup]
      exact hpath
    simpa only [List.length_map] using path_reach hpath'
  have hterminal' : SharedSearch.terminal SectorGraph359.config z = true := by
    rw [hlookup]
    exact hterminal
  have controls : ∀ g ∈ SectorCover.word s p, keep s g.1 = true :=
    SectorCoordinates.control_retained s p hc
  have hcover := selected_decode_covers p hs hc lookup q hq
  let costs : Row → Nat := fun r => (PassiveCost.cost d r).getD 0
  have hcost : ∀ r ∈ SectorTerminal359.targets,
      PassiveCost.cost d r = some (costs r) := by
    intro r hr
    rw [← Sector359Agreement.passive_targets_agree] at hr
    obtain ⟨j,hj,he⟩ := List.mem_map.mp hr
    subst r
    obtain ⟨n,hn,_⟩ := PassiveCost.actual_target_cost_bound
      (SectorCover.word s p) identity j (keep s) d controls hcover
    rw [SectorCover.word_realizes s p real] at hn
    simp only [s, Sector359Encoding.sector, ite_true] at hn
    simpa [costs, SectorCoordinates.goal, Sector359Encoding.sector, hn]
  have hstrong := SectorCost359.no_cheap_terminal hreach hlen hterminal' costs hcost
  have hpassive := SectorCoordinates.passive_properties s hs
  have hcost' : ∀ j ∈ passive s,
      PassiveCost.cost (SectorCost359.decode z.history)
        (identity j ^^^ goal s j) = some (costs (identity j ^^^ goal s j)) := by
    intro j hj
    apply hcost
    rw [← Sector359Agreement.passive_targets_agree]
    exact List.mem_map.mpr ⟨j,hj,rfl⟩
  have hlower := PassiveCost.total_cost_lower_bound (keep s) (passive s)
    (SectorCover.word s p) (SectorCost359.decode z.history) (goal s)
    (fun j => costs (identity j ^^^ goal s j)) controls hcover
    hpassive.1 hpassive.2.2.1 (SectorCover.word_realizes s p real) hcost'
  have hcore : (SectorCover.word s p).filter (fun g => keep s g.2) = core s p := rfl
  rw [hcore, ← hq] at hlower
  simp only [List.length_map] at hlower
  rw [SectorCover.word_length] at hlower
  rw [← Sector359Agreement.passive_targets_agree] at hstrong
  have hstrong' : 18 < q.length +
      ((passive s).map (fun j => costs (identity j ^^^ goal s j))).sum := by
    simpa only [List.map_map,Function.comp_def] using hstrong
  omega

theorem sector_mem : Sector359Encoding.sector ∈ SectorCover.sectors :=
  Sector359Encoding.sector_member

/-- Sector 359 is excluded for every full realization once its concrete
prefix lookup has been certified complete.  Terminal costs are derived from
the word itself, rather than assumed. -/
theorem no_short_sector359
    (hpc : FullWordPath.PrefixComplete Sector359Encoding.sector
      Sector359Agreement.lookup359)
    (p : Program) (hp : Legal p)
    (hc : SectorCover.Compatible Sector359Encoding.sector p)
    (real : run identity p = HGP13.target)
    (short : p.length ≤ 18) : False := by
  obtain ⟨q,hq,hlen,hpath,hterminal⟩ :=
    FullWordPath.short_word_accepted_path Sector359Encoding.sector
      sector_mem Sector359Agreement.lookup359 hpc p hp hc real short
  have hlen' : q.length ≤ 12 := by
    simpa [Sector359Encoding.sector] using hlen
  exact no_short_full_word_from_costs p hp hc real short sector_mem
    Sector359Agreement.lookup359
    Sector359Agreement.config_agrees q hq hlen' hpath hterminal

end HGP13.Sector359FullCompletion
