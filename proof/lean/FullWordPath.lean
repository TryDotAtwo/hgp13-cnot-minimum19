import CatalogueHistory
import BasicGuards
import CoreGuardEncoding
import MissingEncoding

namespace HGP13.FullWordPath
open SectorCover SectorCoordinates SectorIndexing CoreRowEncoding
open SharedSearch TransitionChecks CatalogueCapacity CatalogueHistory

def PrefixComplete (s : Sector) (lookup : Nat → Nat → Bool) : Prop :=
  ∀ (extra : List Catalogues.Value) (observed : List Nat) (capacity : Nat),
    Catalogues.Catalogued (ProjectedHistory.projectedGoals s) extra.length extra →
    3 ≤ extra.length → extra.length ≤ capacity → 3 ≤ capacity → capacity ≤ 4 →
    observed.Nodup → observed ⊆ extra.map BitVec.toNat →
    lookup (if capacity ≤ 3 then 3 else 4) (SharedSearch.encode observed) = true

theorem full_aux_ge_three (s : Sector) (p : Program)
    (real : run identity p = HGP13.target) :
    3 ≤ (fullAux s p).length := by
  have he := word_fresh_exact s p real
  have ht := RepeatErasure.word_fresh_ten s p real
  omega

theorem selected_extra_bound (s : Sector) (lookup : Nat → Nat → Bool)
    (p : Program) (real : run identity p = HGP13.target)
    (q : List (IndexedGate (changing s) (fixedWires s)))
    (hcap : ∀ a b, q.map label = a ++ b →
      (fullAux s p).length ≤ 5 - (ofSector s lookup).sources.length -
        (rawRun (ofSector s lookup) (initial (ofSector s lookup)) a).extra) :
    (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (q.map label)).extra ≤
      2 - (ofSector s lookup).sources.length := by
  have hc := hcap (q.map label) [] (by simp)
  have hg := full_aux_ge_three s p real
  omega

theorem selected_extra_guard (s : Sector) (lookup : Nat → Nat → Bool)
    (p : Program) (real : run identity p = HGP13.target)
    (q a b : List (IndexedGate (changing s) (fixedWires s)))
    (g : IndexedGate (changing s) (fixedWires s))
    (hcap : ∀ x y, q.map label = x ++ y →
      (fullAux s p).length ≤ 5 - (ofSector s lookup).sources.length -
        (rawRun (ofSector s lookup) (initial (ofSector s lookup)) x).extra)
    (he : q = a ++ g :: b) :
    (propose (ofSector s lookup) a.length
      (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (a.map label))
      g.2.val g.1.val).extraBad = false := by
  have hf := selected_extra_bound s lookup p real q hcap
  rw [he] at hf
  simp only [List.map_append,List.map_cons] at hf
  have hh := CounterBudget.extra_guard_of_endpoint_bound
    (ofSector s lookup) 0 (initial (ofSector s lookup))
    (a.map label) (b.map label) (label g) hf
  simpa only [Nat.zero_add,List.length_map,label] using hh

theorem sector_active_bounds (s : Sector) (hs : s ∈ sectors) :
    1 ≤ s.active.length ∧ s.active.length ≤ 2 := by
  have checked : sectors.all (fun x => decide
      (1 ≤ x.active.length ∧ x.active.length ≤ 2)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp checked s hs)

theorem selected_catalogue_guard (s : Sector) (hs : s ∈ sectors)
    (lookup : Nat → Nat → Bool) (hpc : PrefixComplete s lookup)
    (p : Program) (hc : Compatible s p)
    (real : run identity p = HGP13.target)
    (q a b : List (IndexedGate (changing s) (fixedWires s)))
    (g : IndexedGate (changing s) (fixedWires s))
    (hq : q.map (fullGate (changing s) (fixedWires s)) = core s p)
    (hcap : ∀ x y, q.map label = x ++ y →
      (fullAux s p).length ≤ 5 - (ofSector s lookup).sources.length -
        (rawRun (ofSector s lookup) (initial (ofSector s lookup)) x).extra)
    (he : q = a ++ g :: b) :
    (propose (ofSector s lookup) a.length
      (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (a.map label))
      g.2.val g.1.val).catalogueBad = false := by
  let c := ofSector s lookup
  let z := rawRun c (initial c) (a.map label)
  let cap := 5 - c.sources.length - (advance c z (label g)).extra
  have hsplit : q.map label = (a ++ [g]).map label ++ b.map label := by
    rw [he]
    simp only [List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.singleton_append]
  have hcapAfter := hcap ((a ++ [g]).map label) (b.map label) hsplit
  have hbound : (fullAux s p).length ≤ cap := by
    simpa only [cap,c,z,List.map_append,List.map_cons,List.map_nil,
      CounterBudget.raw_append,rawRun,label] using hcapAfter
  have hsize := enlarged_length s hs lookup p hc q a b g hq he
  have hsubset := enlarged_subset s hs lookup p hc q a b g hq he
  have hnodup := enlarged_nodup c z (label g)
  have hn := (sector_active_bounds s hs).1
  have hcaphi : cap ≤ 4 := by
    simp only [cap,c,ofSector,List.length_map] at *
    omega
  have hcaplo : 3 ≤ cap := by
    have hg := full_aux_ge_three s p real
    omega
  have hlook := hpc (fullAux s p) (enlarged c z (label g)) cap
    (full_aux_catalogued s p real) (full_aux_ge_three s p real)
    hbound hcaplo hcaphi hnodup hsubset
  change (propose c a.length z (label g).1 (label g).2).catalogueBad = false
  rw [proposal_catalogue]
  have hsmall : decide ((enlarged c z (label g)).length > cap) = false :=
    decide_eq_false (Nat.not_lt.mpr (Nat.le_trans hsize hbound))
  change (decide ((enlarged c z (label g)).length > cap) ||
    !lookup (if cap ≤ 3 then 3 else 4)
      (encode (enlarged c z (label g)))) = false
  simp [hsmall,hlook]

theorem selected_admissible_step (s : Sector) (hs : s ∈ sectors)
    (lookup : Nat → Nat → Bool) (hpc : PrefixComplete s lookup)
    (p : Program) (hp : Legal p) (hc : Compatible s p)
    (real : run identity p = HGP13.target) (short : p.length ≤ 18)
    (q a b : List (IndexedGate (changing s) (fixedWires s)))
    (g : IndexedGate (changing s) (fixedWires s))
    (hq : q.map (fullGate (changing s) (fixedWires s)) = core s p)
    (hcap : ∀ x y, q.map label = x ++ y →
      (fullAux s p).length ≤ 5 - (ofSector s lookup).sources.length -
        (rawRun (ofSector s lookup) (initial (ofSector s lookup)) x).extra)
    (he : q = a ++ g :: b) :
    Admissible ((ofSector s lookup).sources.length == 2)
      (propose (ofSector s lookup) a.length
        (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (a.map label))
        g.2.val g.1.val) := by
  have hlegal : Legal (q.map (fullGate (changing s) (fixedWires s))) := by
    rw [hq]
    intro k hk
    exact word_legal s p hp k (List.mem_filter.mp hk).1
  have hg : (fullGate (changing s) (fixedWires s) g).1 ≠
      (fullGate (changing s) (fixedWires s) g).2 := by
    apply hlegal
    apply List.mem_map.mpr
    refine ⟨g,?_,rfl⟩
    rw [he]
    simp
  have hpref : Legal ((a ++ [g]).map (fullGate (changing s) (fixedWires s))) := by
    intro k hk
    apply hlegal k
    have hsplit : q = (a ++ [g]) ++ b := by
      simpa only [List.append_assoc,List.singleton_append] using he
    rw [hsplit,List.map_append]
    exact List.mem_append_left _ hk
  let proposal := propose (ofSector s lookup) a.length
    (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (a.map label))
    g.2.val g.1.val
  have ha : proposal.alphabetBad = false :=
    BasicGuards.indexed_alphabet s hs lookup g hg a.length _
  have hz : proposal.zeroBad = false :=
    BasicGuards.indexed_zero s hs lookup a g hpref a.length
  have hexc : proposal.extraBad = false :=
    selected_extra_guard s lookup p real q a b g hcap he
  have hcat : proposal.catalogueBad = false :=
    selected_catalogue_guard s hs lookup hpc p hc real q a b g hq hcap he
  have hdepth : proposal.depthBad = false :=
    MissingEncoding.core_depth_guard s hs lookup p hp hc real short q a b g hq he
  refine ⟨ha,hz,hexc,hcat,?_,hdepth⟩
  intro htwo
  have htwo' : s.active.length = 2 := by
    simpa only [ofSector,List.length_map,beq_iff_eq] using htwo
  exact ⟨CoreGuardEncoding.core_guard s hs lookup p hp hc real short htwo'
      q a b g hq he,
    CorePrefixConditions.core_passive_guard s hs lookup p hp hc real short htwo'
      q a b g hq he⟩

theorem selected_guards (s : Sector) (hs : s ∈ sectors)
    (lookup : Nat → Nat → Bool) (hpc : PrefixComplete s lookup)
    (p : Program) (hp : Legal p) (hc : Compatible s p)
    (real : run identity p = HGP13.target) (short : p.length ≤ 18)
    (q : List (IndexedGate (changing s) (fixedWires s)))
    (hq : q.map (fullGate (changing s) (fixedWires s)) = core s p)
    (hcap : ∀ x y, q.map label = x ++ y →
      (fullAux s p).length ≤ 5 - (ofSector s lookup).sources.length -
        (rawRun (ofSector s lookup) (initial (ofSector s lookup)) x).extra) :
    GuardsHold (ofSector s lookup) 0 (initial (ofSector s lookup)) (q.map label) := by
  let c := ofSector s lookup
  have hstep : ∀ (a b : List (IndexedGate (changing s) (fixedWires s))),
      q = a ++ b → GuardsHold c a.length
        (rawRun c (initial c) (a.map label)) (b.map label) := by
    intro a b
    induction b generalizing a with
    | nil =>
      intro _
      simp [GuardsHold]
    | cons g tail ih =>
      intro he
      have hg := selected_admissible_step s hs lookup hpc p hp hc real short
        q a tail g hq hcap he
      have htail : GuardsHold c (a ++ [g]).length
          (rawRun c (initial c) ((a ++ [g]).map label)) (tail.map label) :=
        ih (a ++ [g]) (by simpa only [List.append_assoc,List.singleton_append] using he)
      change Admissible (c.sources.length == 2)
          (propose c a.length (rawRun c (initial c) (a.map label))
            (label g).1 (label g).2) ∧
        GuardsHold c (a.length+1)
          (advance c (rawRun c (initial c) (a.map label)) (label g)) (tail.map label)
      refine ⟨hg,?_⟩
      simpa only [List.length_append,List.length_singleton,Nat.add_comm,
        List.map_append,List.map_cons,List.map_nil,CounterBudget.raw_append,rawRun] using htail
  simpa only [List.length_nil,List.map_nil,rawRun] using hstep [] q (by simp)

theorem short_word_accepted_path (s : Sector) (hs : s ∈ sectors)
    (lookup : Nat → Nat → Bool) (hpc : PrefixComplete s lookup)
    (p : Program) (hp : Legal p) (hc : Compatible s p)
    (real : run identity p = HGP13.target) (short : p.length ≤ 18) :
    ∃ q : List (IndexedGate (changing s) (fixedWires s)),
      q.map (fullGate (changing s) (fixedWires s)) = core s p ∧
      q.length ≤ 12 + s.carriers.length ∧
      Path (ofSector s lookup) 0 (initial (ofSector s lookup)) (q.map label)
        (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (q.map label)) ∧
      terminal (ofSector s lookup)
        (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (q.map label)) = true := by
  obtain ⟨q,hq,hlen,hcap⟩ := covered_prefix_capacity s hs lookup p hp hc real short
  refine ⟨q,hq,?_,?_,?_⟩
  · rw [hlen]
    exact core_depth_bound s hs p real short
  · exact guards_path _ _ _ _ (selected_guards s hs lookup hpc p hp hc real short q hq hcap)
  · exact BasicGuards.core_terminal s hs lookup p hc real q hq

theorem selected_history_exact (s : Sector) (hs : s ∈ sectors)
    (lookup : Nat → Nat → Bool) (p : Program) (hc : Compatible s p)
    (q : List (IndexedGate (changing s) (fixedWires s)))
    (hq : q.map (fullGate (changing s) (fixedWires s)) = core s p)
    (r : Row) (hr : RowSupported (embed s) r) :
    PackedRows.has (rawRun (ofSector s lookup) (initial (ofSector s lookup))
      (q.map label)).history (PackedRows.pack (embed s) r).toNat = true ↔
      r ∈ PassiveInsertion.historyRows (keep s) identity (core s p) := by
  obtain ⟨hd,_,hj⟩ := partition_properties s hs
  obtain ⟨hrows,hh,hfixed,_⟩ := initial_matches_full_matrix s hs lookup
  have htrace := raw_history_run (embed s) (changing s) (fixedWires s) hd hj
    (ofSector s lookup) (count_matches s lookup) q identity
    (initial (ofSector s lookup)) hrows hfixed
  rw [hq,hh] at htrace
  rw [htrace]
  exact (PackedRows.actual_trace_history s p hc r hr).trans
    (PassiveInsertion.historyRows_exact (keep s) (core s p) r).symm

end HGP13.FullWordPath
