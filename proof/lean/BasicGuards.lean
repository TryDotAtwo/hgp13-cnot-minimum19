import RepeatErasure

namespace HGP13.BasicGuards
open SectorCover SectorCoordinates SectorIndexing CoreRowEncoding KnownControls IndexedEffectiveness
open SharedSearch TransitionChecks PackedRows

theorem fixed_length (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool) :
    (fixed (ofSector s lookup)).length = (fixedWires s).length := by
  have h := congrArg List.length (initial_matches_full_matrix s hs lookup).2.2.1
  simpa only [ProjectedHistory.initialFixedCodes,fixedWires,List.length_map] using h

theorem indexed_alphabet (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (g : IndexedGate (changing s) (fixedWires s))
    (hg : (fullGate (changing s) (fixedWires s) g).1 ≠
      (fullGate (changing s) (fixedWires s) g).2) (depth : Nat) (z : State) :
    (propose (ofSector s lookup) depth z g.2.val g.1.val).alphabetBad = false := by
  have hne : g.1.val ≠ g.2.val := by
    intro he
    apply hg
    simp only [fullGate]
    simp [he,g.2.isLt,List.getElem_append]
  change (decide (g.2.val ≥ count (ofSector s lookup)) ||
    decide (g.1.val ≥ count (ofSector s lookup) + (fixed (ofSector s lookup)).length) ||
    (g.1.val == g.2.val)) = false
  rw [count_matches,fixed_length s hs lookup]
  simp [Nat.not_le.mpr g.2.isLt,Nat.not_le.mpr g.1.isLt,hne]

theorem raw_value_full (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : List (IndexedGate (changing s) (fixedWires s)))
    (g : IndexedGate (changing s) (fixedWires s)) :
    value (ofSector s lookup) (rawRun (ofSector s lookup) (initial (ofSector s lookup))
      (p.map label)) (label g) =
    (pack (embed s) (step (run identity (p.map (fullGate (changing s) (fixedWires s))))
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
    rw [fixed_run (embed s) (changing s) (fixedWires s) hj]
    exact hf
  change (z.rows[g.2.val]! ^^^ (if g.1.val < count c then z.rows[g.1.val]! else (fixed c)[g.1.val-count c]!)) = _
  rw [control_read (embed s) (changing s) (fixedWires s) x c z g.1
    (count_matches s lookup) rr hf',rr,rows_get _ _ _ _ g.2.isLt]
  simp [fullGate,step,pack_nat_xor,x]

theorem indexed_zero (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : List (IndexedGate (changing s) (fixedWires s)))
    (g : IndexedGate (changing s) (fixedWires s))
    (hp : Legal ((p ++ [g]).map (fullGate (changing s) (fixedWires s)))) (depth : Nat) :
    (propose (ofSector s lookup) depth
      (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (p.map label))
      g.2.val g.1.val).zeroBad = false := by
  change (value (ofSector s lookup)
    (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (p.map label)) (label g) == 0) = false
  have hz := NonzeroRows.packed_row_nonzero (embed s)
    ((p ++ [g]).map (fullGate (changing s) (fixedWires s))) hp (changing s)[g.2.val]
    (retained_row_supported s hs (p ++ [g]) _ (changing_retained s hs _ (List.getElem_mem g.2.isLt)))
  rw [raw_value_full s hs lookup p g]
  simp only [List.map_append,List.map_cons,List.map_nil,run_append,run_cons,run_nil] at hz
  exact beq_eq_false_iff_ne.mpr hz

theorem covered_three_guards (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : Program) (hp : Legal p) (hc : Compatible s p)
    (real : run identity p = HGP13.target) (short : p.length ≤ 18) :
    ∃ q : List (IndexedGate (changing s) (fixedWires s)),
      q.map (fullGate (changing s) (fixedWires s)) = core s p ∧
      q.length = (core s p).length ∧
      ∀ a g b, q = a ++ g :: b →
        let proposal := propose (ofSector s lookup) a.length
          (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (a.map label)) g.2.val g.1.val
        proposal.alphabetBad = false ∧ proposal.zeroBad = false ∧ proposal.extraBad = false := by
  obtain ⟨q,hq,hl,hextra⟩ := RepeatErasure.covered_extra_guards s hs lookup p hp hc real short
  have hlegal : Legal (q.map (fullGate (changing s) (fixedWires s))) := by
    rw [hq]
    intro g hg
    exact word_legal s p hp g (List.mem_filter.mp hg).1
  refine ⟨q,hq,hl,?_⟩
  intro a g b he
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
    have hsplit : q = (a ++ [g]) ++ b := by simpa only [List.append_assoc,List.singleton_append] using he
    rw [hsplit,List.map_append]
    exact List.mem_append_left _ hk
  refine ⟨indexed_alphabet s hs lookup g hg a.length _,indexed_zero s hs lookup a g hpref a.length,?_⟩
  have hx := hextra (a.map label) (label g) (b.map label) (by rw [he]; simp)
  simpa only [List.length_map,label] using hx
theorem core_changed_mask (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : Program) (hc : Compatible s p)
    (q : List (IndexedGate (changing s) (fixedWires s)))
    (hq : q.map (fullGate (changing s) (fixedWires s)) = core s p) :
    (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (q.map label)).changed =
      2^(ofSector s lookup).sources.length-1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [← has_testBit,Nat.testBit_two_pow_sub_one]
  apply Bool.eq_iff_iff.mpr
  rw [raw_changed]
  have hz : has (initial (ofSector s lookup)).changed i = false := by simp [initial,has]
  simp only [hz,Bool.false_eq_true,false_or,decide_eq_true_eq]
  constructor
  · rintro ⟨g,_,_,hi⟩
    exact hi
  · intro hi
    have hib : i < s.active.length := by simpa only [ofSector,List.length_map] using hi
    obtain ⟨g,hg,he⟩ := active_index_hit s hs p hc q hq i hib
    exact ⟨g,hg,he,hi⟩

theorem core_terminal (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : Program) (hc : Compatible s p) (real : run identity p = HGP13.target)
    (q : List (IndexedGate (changing s) (fixedWires s)))
    (hq : q.map (fullGate (changing s) (fixedWires s)) = core s p) :
    terminal (ofSector s lookup)
      (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (q.map label)) = true := by
  obtain ⟨hd,_,hj⟩ := partition_properties s hs
  obtain ⟨hr,_,hf,hw⟩ := initial_matches_full_matrix s hs lookup
  have rr := raw_rows_run (embed s) (changing s) (fixedWires s) hd hj
    (ofSector s lookup) (count_matches s lookup) q identity (initial (ofSector s lookup)) hr hf
  rw [hq] at rr
  have hrows : (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (q.map label)).rows =
      want (ofSector s lookup) := rr.trans ((core_final_rows s hs p hc real).trans hw.symm)
  have hchanged := core_changed_mask s hs lookup p hc q hq
  simp only [terminal,hrows,hchanged,beq_self_eq_true,Bool.and_self]
end HGP13.BasicGuards


