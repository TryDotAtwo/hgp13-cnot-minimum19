import CorePrefixConditions
namespace HGP13.CoreGuardEncoding
open SectorCover SectorCoordinates SectorIndexing CoreRowEncoding
open SharedSearch TransitionChecks PackedRows CleanPersistence CorePrefixConditions

def CoreLiterals (s : Sector) : Prop :=
  (∀ i : Fin (changing s).length, s.active.length ≤ i.val →
    (i.val = s.active.length ∧ (changing s)[i.val] = 8) ∨
    (i.val ≠ s.active.length ∧ (changing s)[i.val] ∈ Budget.privateOutputs)) ∧
  (∀ j : Wire, j ∈ Budget.privateOutputs →
    (pack (embed s) (identity j)).toNat &&& 127 = 0) ∧
  (∀ j : Wire, j ∈ Budget.privateOutputs → ∀ k ∈ fixedWires s,
    (pack (embed s) (identity k)).toNat ≠ (Projection.project (goal s j)).toNat)
instance (s : Sector) : Decidable (CoreLiterals s) := by
  unfold CoreLiterals
  infer_instance
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem core_literals_checked : sectors.all (fun s => decide (CoreLiterals s)) = true := by decide

theorem core_literals (s : Sector) (hs : s ∈ sectors) : CoreLiterals s :=
  of_decide_eq_true (List.all_eq_true.mp core_literals_checked s hs)

theorem raw_rows (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (a : List (IndexedGate (changing s) (fixedWires s))) :
    (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (a.map label)).rows =
      rows (embed s) (changing s) (run identity (a.map (fullGate (changing s) (fixedWires s)))) := by
  obtain ⟨hd,_,hj⟩ := partition_properties s hs
  obtain ⟨hr,_,hf,_⟩ := initial_matches_full_matrix s hs lookup
  exact raw_rows_run (embed s) (changing s) (fixedWires s) hd hj
    (ofSector s lookup) (count_matches s lookup) a identity _ hr hf

theorem clean_witness_mutable (s : Sector) (hs : s ∈ sectors)
    (a : List (IndexedGate (changing s) (fixedWires s)))
    (j : Wire) (hj : j ∈ Budget.privateOutputs) (k : Wire) (hk : keep s k = true)
    (he : run identity (a.map (fullGate (changing s) (fixedWires s))) k = identity j ^^^ goal s j) :
    k ∈ changing s := by
  have hm : k ∈ layout s := by simpa only [keep,List.contains_iff_mem] using hk
  rcases List.mem_append.mp (input_member s k hm) with hm | hm
  · exact hm
  · have hf := MissingEncoding.fixed_pointwise (changing s) (fixedWires s)
      (partition_properties s hs).2.2 a k hm
    have hcode := congrArg (fun r => (pack (embed s) r).toNat) (hf.symm.trans he)
    rw [(passive_literals s hs).2 j hj] at hcode
    exact False.elim ((core_literals s hs).2.2 j hj k hm hcode)

def stateCore (c : Config) (z : State) : Bool :=
  (List.range (count c)).any fun i =>
    i ≥ c.sources.length &&
    let f := (want c)[i]! &&& 127
    has (projected z.history) f && z.rows[i]! != (want c)[i]! &&
      (i == c.sources.length || z.rows[i]! &&& 127 != 0 || !z.rows.contains f)

theorem proposal_core (c : Config) (depth : Nat) (z : State) (t j : Nat) :
    (propose c depth z t j).coreBad = stateCore c (advance c z (t,j)) := by rfl
theorem state_core_false (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : Program) (hp : Legal p) (hc : Compatible s p) (real : run identity p = HGP13.target)
    (short : p.length ≤ 18) (two : s.active.length = 2)
    (q a b : List (IndexedGate (changing s) (fixedWires s)))
    (hq : q.map (fullGate (changing s) (fixedWires s)) = core s p) (he : q = a ++ b) :
    stateCore (ofSector s lookup)
      (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (a.map label)) = false := by
  let x := run identity (a.map (fullGate (changing s) (fixedWires s)))
  let z := rawRun (ofSector s lookup) (initial (ofSector s lookup)) (a.map label)
  have hz : z.rows = rows (embed s) (changing s) x := raw_rows s hs lookup a
  have hw : want (ofSector s lookup) = rows (embed s) (changing s) (goal s) :=
    (initial_matches_full_matrix s hs lookup).2.2.2
  have conditions := indexed_prefix_conditions s hs p hp hc real short two q a b hq he
  have ns : (ofSector s lookup).sources.length = s.active.length := by simp [ofSector]
  unfold stateCore
  rw [List.any_eq_false]
  intro i hi
  have hi' : i < (changing s).length := by
    rw [List.mem_range,count_matches] at hi
    exact hi
  apply Bool.eq_false_iff.mp
  change (decide (i ≥ (ofSector s lookup).sources.length) && (
    has (projected z.history) ((want (ofSector s lookup))[i]! &&& 127) &&
    (z.rows[i]! != (want (ofSector s lookup))[i]!) &&
    (i == (ofSector s lookup).sources.length || z.rows[i]! &&& 127 != 0 ||
      !z.rows.contains ((want (ofSector s lookup))[i]! &&& 127)))) = false
  rw [ns]
  by_cases hin : s.active.length ≤ i
  · let j : Wire := (changing s)[i]
    have hgoal : (want (ofSector s lookup))[i]! = (pack (embed s) (goal s j)).toNat := by
      rw [hw,rows_get _ _ _ i hi']
    have hrow : z.rows[i]! = (pack (embed s) (x j)).toNat := by
      rw [hz,rows_get _ _ _ i hi']
    have hproj : (want (ofSector s lookup))[i]! &&& 127 = (Projection.project (goal s j)).toNat := by
      rw [hgoal]
      exact (Nat.and_two_pow_sub_one_eq_mod _ 7).trans (ProjectedHistory.packed_mod128 s _)
    by_cases known : has (projected z.history) (Projection.project (goal s j)).toNat = true
    · have appeared := raw_projected_reflects s hs lookup a (Projection.project (goal s j)) known
      by_cases done : x j = goal s j
      · have heq : z.rows[i]! = (want (ofSector s lookup))[i]! := by rw [hrow,hgoal,done]
        simp [heq]
      · rcases (core_literals s hs).1 ⟨i,hi'⟩ hin with center | carrier
        · have hj : j = 8 := center.2
          have finished : x j = goal s j := by
            rw [hj] at appeared ⊢
            exact conditions.1 appeared
          exact False.elim (done finished)
        · have hj : j ∈ Budget.privateOutputs := carrier.2
          have keepj : keep s j = true := changing_retained s hs j (List.getElem_mem hi')
          obtain ⟨empty,k,keepk,cleanrow,_⟩ := conditions.2.1 j hj keepj done appeared
          change x j = identity j at empty
          change x k = identity j ^^^ goal s j at cleanrow
          have hzero : z.rows[i]! &&& 127 = 0 := by
            rw [hrow,empty]
            exact (core_literals s hs).2.1 j hj
          have hk := clean_witness_mutable s hs a j hj k keepk cleanrow
          have hmem : (Projection.project (goal s j)).toNat ∈ z.rows := by
            rw [hz]
            apply List.mem_map.mpr
            refine ⟨k,hk,?_⟩
            rw [cleanrow]
            exact (passive_literals s hs).2 j hj
          have hcontains : z.rows.contains (Projection.project (goal s j)).toNat = true :=
            List.contains_iff_mem.mpr hmem
          rw [hproj,hzero,hcontains]
          simp [carrier.1]
    · have unknown := Bool.eq_false_iff.mpr known
      rw [hproj,unknown]
      simp
  · simp [hin]

theorem core_guard (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : Program) (hp : Legal p) (hc : Compatible s p) (real : run identity p = HGP13.target)
    (short : p.length ≤ 18) (two : s.active.length = 2)
    (q a b : List (IndexedGate (changing s) (fixedWires s)))
    (g : IndexedGate (changing s) (fixedWires s))
    (hq : q.map (fullGate (changing s) (fixedWires s)) = core s p) (he : q = a ++ g :: b) :
    (propose (ofSector s lookup) a.length
      (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (a.map label)) g.2.val g.1.val).coreBad = false := by
  rw [proposal_core]
  have hsplit : q = (a ++ [g]) ++ b := by simpa only [List.append_assoc,List.singleton_append] using he
  have h := state_core_false s hs lookup p hp hc real short two q (a ++ [g]) b hq hsplit
  simpa only [List.map_append,List.map_cons,List.map_nil,CounterBudget.raw_append,rawRun,label] using h

end HGP13.CoreGuardEncoding



