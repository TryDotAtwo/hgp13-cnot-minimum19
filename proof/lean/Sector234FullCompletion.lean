import Sector234Agreement
import FullPackedCompletion

namespace HGP13.Sector234FullCompletion

open SectorCoordinates CoreRowEncoding TransitionChecks

/-- The decoded terminal bitset contains every actual full-width row that
occurred on a retained wire of the selected core word. -/
theorem history_mem_decode (p : Program)
    (hs : Sector234Encoding.sector ∈ SectorCover.sectors)
    (hc : SectorCover.Compatible Sector234Encoding.sector p)
    (lookup : Nat → Nat → Bool)
    (q : List (IndexedGate (changing Sector234Encoding.sector)
      (SectorIndexing.fixedWires Sector234Encoding.sector)))
    (hq : q.map (fullGate (changing Sector234Encoding.sector)
      (SectorIndexing.fixedWires Sector234Encoding.sector)) =
        core Sector234Encoding.sector p)
    (r : Row)
    (hr : r ∈ PassiveInsertion.historyRows
      (keep Sector234Encoding.sector) identity
      (core Sector234Encoding.sector p)) :
    r ∈ SectorCost234.decode
      (rawRun (SharedSearch.ofSector Sector234Encoding.sector lookup)
        (SharedSearch.initial (SharedSearch.ofSector Sector234Encoding.sector lookup))
        (q.map label)).history := by
  have hrs := PackedRows.actual_history_supported Sector234Encoding.sector p hc r hr
  have hb := (FullWordPath.selected_history_exact Sector234Encoding.sector hs
    lookup p hc q hq r hrs).mpr hr
  unfold SectorCost234.decode
  apply List.mem_map.mpr
  refine ⟨(PackedRows.pack (embed Sector234Encoding.sector) r).toNat,?_,?_⟩
  · apply List.mem_filter.mpr
    exact ⟨List.mem_range.mpr (PackedRows.pack (embed Sector234Encoding.sector) r).isLt,hb⟩
  · have hwidth : (layout Sector234Encoding.sector).length = 8 := by rfl
    simp only [BitVec.ofNat_toNat]
    have hv : (PackedRows.pack (embed Sector234Encoding.sector) r).setWidth 8 =
        (PackedRows.pack (embed Sector234Encoding.sector) r).cast hwidth := by
      calc
        _ = ((PackedRows.pack (embed Sector234Encoding.sector) r).setWidth
            (layout Sector234Encoding.sector).length).cast hwidth := by
              exact (BitVec.cast_setWidth hwidth _).symm
        _ = _ := by rw [BitVec.setWidth_eq]
    rw [hv]
    exact Sector234Encoding.unpack_actual r hrs

theorem selected_decode_covers (p : Program)
    (hs : Sector234Encoding.sector ∈ SectorCover.sectors)
    (hc : SectorCover.Compatible Sector234Encoding.sector p)
    (lookup : Nat → Nat → Bool)
    (q : List (IndexedGate (changing Sector234Encoding.sector)
      (SectorIndexing.fixedWires Sector234Encoding.sector)))
    (hq : q.map (fullGate (changing Sector234Encoding.sector)
      (SectorIndexing.fixedWires Sector234Encoding.sector)) =
        core Sector234Encoding.sector p) :
    PassiveCost.CoversHistory (keep Sector234Encoding.sector) identity
      (SectorCover.word Sector234Encoding.sector p)
      (SectorCost234.decode
        (rawRun (SharedSearch.ofSector Sector234Encoding.sector lookup)
          (SharedSearch.initial (SharedSearch.ofSector Sector234Encoding.sector lookup))
          (q.map label)).history) := by
  let s := Sector234Encoding.sector
  have controls : ∀ g ∈ SectorCover.word s p, keep s g.1 = true :=
    SectorCoordinates.control_retained s p hc
  have cover := PassiveInsertion.erased_history_covers (keep s)
    (SectorCover.word s p) (core s p) controls rfl
  intro a b he i hi
  exact history_mem_decode p hs hc lookup q hq _ (cover a b he i hi)

theorem path_reach {d : Nat} {s z : SharedSearch.State}
    {q : List (Nat × Nat)}
    (h : TransitionChecks.Path SectorGraph234.config d s q z) :
    SectorGraph234.Reach d s q.length z := by
  induction h with
  | nil d s => exact SectorGraph234.Reach.refl d s
  | @cons d s g q t z hm hp ih =>
    apply SectorGraph234.Reach.step
    · exact (SharedSearch.next_iff _ _ _ _).mpr
        ⟨g.1, (TransitionChecks.admissible_indices _ _ _ _ _
          ((TransitionChecks.move_eq_some_iff _ _ _ _ _ _).mp hm).1).1,
          g.2, (TransitionChecks.admissible_indices _ _ _ _ _
            ((TransitionChecks.move_eq_some_iff _ _ _ _ _ _).mp hm).1).2.1, hm⟩
    · exact ih

theorem no_short_full_word_from_costs (p : Program)
    (hp : Legal p) (hc : SectorCover.Compatible Sector234Encoding.sector p)
    (real : run identity p = HGP13.target) (short : p.length ≤ 18)
    (hs : Sector234Encoding.sector ∈ SectorCover.sectors)
    (lookup : Nat → Nat → Bool)
    (hlookup : SectorGraph234.config = SharedSearch.ofSector
      Sector234Encoding.sector lookup)
    (q : List (IndexedGate (changing Sector234Encoding.sector)
      (SectorIndexing.fixedWires Sector234Encoding.sector)))
    (hq : q.map (fullGate (changing Sector234Encoding.sector)
      (SectorIndexing.fixedWires Sector234Encoding.sector)) =
        core Sector234Encoding.sector p)
    (hlen : q.length ≤ 13)
    (hpath : TransitionChecks.Path
      (SharedSearch.ofSector Sector234Encoding.sector lookup) 0
      (SharedSearch.initial (SharedSearch.ofSector Sector234Encoding.sector lookup))
      (q.map label)
      (rawRun (SharedSearch.ofSector Sector234Encoding.sector lookup)
        (SharedSearch.initial (SharedSearch.ofSector Sector234Encoding.sector lookup))
        (q.map label)))
    (hterminal : SharedSearch.terminal
      (SharedSearch.ofSector Sector234Encoding.sector lookup)
      (rawRun (SharedSearch.ofSector Sector234Encoding.sector lookup)
        (SharedSearch.initial (SharedSearch.ofSector Sector234Encoding.sector lookup))
        (q.map label)) = true) : False := by
  let s := Sector234Encoding.sector
  let z := rawRun (SharedSearch.ofSector s lookup)
    (SharedSearch.initial (SharedSearch.ofSector s lookup)) (q.map label)
  let d := SectorCost234.decode z.history
  have hreach : SectorGraph234.Reach 0
      (SharedSearch.initial SectorGraph234.config) q.length z := by
    have hpath' : TransitionChecks.Path SectorGraph234.config 0
        (SharedSearch.initial SectorGraph234.config) (q.map label) z := by
      rw [hlookup]
      exact hpath
    simpa only [List.length_map] using path_reach hpath'
  have hterminal' : SharedSearch.terminal SectorGraph234.config z = true := by
    rw [hlookup]
    exact hterminal
  have controls : ∀ g ∈ SectorCover.word s p, keep s g.1 = true :=
    SectorCoordinates.control_retained s p hc
  have hcover := selected_decode_covers p hs hc lookup q hq
  let costs : Row → Nat := fun r => (PassiveCost.cost d r).getD 0
  have hcost : ∀ r ∈ Sector234Potentials.targets,
      PassiveCost.cost d r = some (costs r) := by
    intro r hr
    rw [← Sector234Agreement.passive_targets_agree] at hr
    obtain ⟨j,hj,he⟩ := List.mem_map.mp hr
    subst r
    obtain ⟨n,hn,_⟩ := PassiveCost.actual_target_cost_bound
      (SectorCover.word s p) identity j (keep s) d controls hcover
    rw [SectorCover.word_realizes s p real] at hn
    simp only [s, Sector234Encoding.sector, ite_true] at hn
    simpa [costs, SectorCoordinates.goal, Sector234Encoding.sector, hn]
  have hstrong := SectorCost234.no_cheap_terminal hreach hlen hterminal' costs hcost
  have hpassive := SectorCoordinates.passive_properties s hs
  have hcost' : ∀ j ∈ passive s,
      PassiveCost.cost (SectorCost234.decode z.history)
        (identity j ^^^ goal s j) = some (costs (identity j ^^^ goal s j)) := by
    intro j hj
    apply hcost
    rw [← Sector234Agreement.passive_targets_agree]
    exact List.mem_map.mpr ⟨j,hj,rfl⟩
  have hlower := PassiveCost.total_cost_lower_bound (keep s) (passive s)
    (SectorCover.word s p) (SectorCost234.decode z.history) (goal s)
    (fun j => costs (identity j ^^^ goal s j)) controls hcover
    hpassive.1 hpassive.2.2.1 (SectorCover.word_realizes s p real) hcost'
  have hcore : (SectorCover.word s p).filter (fun g => keep s g.2) = core s p := rfl
  rw [hcore, ← hq] at hlower
  simp only [List.length_map] at hlower
  rw [SectorCover.word_length] at hlower
  rw [← Sector234Agreement.passive_targets_agree] at hstrong
  have hstrong' : 18 < q.length +
      ((passive s).map (fun j => costs (identity j ^^^ goal s j))).sum := by
    simpa only [List.map_map,Function.comp_def] using hstrong
  omega

def lookup234 (k x : Nat) : Bool :=
  SectorGraph234.lookup
    (if k ≤ 3 then SectorGraph234.prefix3 else SectorGraph234.prefix4) x

theorem sector_mem : Sector234Encoding.sector ∈ SectorCover.sectors :=
  List.mem_of_getElem? Sector234Encoding.sector_at_234

/-- Sector 234 is excluded for every full realization once its concrete
prefix lookup has been certified complete.  Terminal costs are derived from
the word itself, rather than assumed. -/
theorem no_short_sector234
    (hpc : FullWordPath.PrefixComplete Sector234Encoding.sector lookup234)
    (p : Program) (hp : Legal p)
    (hc : SectorCover.Compatible Sector234Encoding.sector p)
    (real : run identity p = HGP13.target)
    (short : p.length ≤ 18) : False := by
  obtain ⟨q,hq,hlen,hpath,hterminal⟩ :=
    FullWordPath.short_word_accepted_path Sector234Encoding.sector
      sector_mem lookup234 hpc p hp hc real short
  have hlen' : q.length ≤ 13 := by
    simpa [Sector234Encoding.sector] using hlen
  exact no_short_full_word_from_costs p hp hc real short sector_mem lookup234
    Sector234Agreement.config_agrees q hq hlen' hpath hterminal

end HGP13.Sector234FullCompletion
