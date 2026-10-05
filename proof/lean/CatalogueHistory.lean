import CatalogueCapacity
import Catalogues
import CoreGuardEncoding
namespace HGP13.CatalogueHistory
open Budget Projection FreeXor SectorCover SectorCoordinates SectorIndexing CoreRowEncoding
open SharedSearch TransitionChecks PackedRows CleanPersistence CorePrefixConditions CatalogueCapacity

theorem full_aux_extras (s : Sector) (p : Program) :
    fullAux s p = Catalogues.extras (ProjectedHistory.projectedGoals s) (trace identity (word s p)) := by
  cases h : s.transposed with
  | false => simp only [fullAux,ProjectedHistory.projectedGoals,h,Bool.false_eq_true,ite_false]; rfl
  | true =>
    simp only [fullAux,ProjectedHistory.projectedGoals,h,ite_true]
    exact (Catalogues.transpose_extras _).symm

theorem prefix_seen_in_full (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : Program) (hc : Compatible s p)
    (q a b : List (IndexedGate (changing s) (fixedWires s)))
    (hq : q.map (fullGate (changing s) (fixedWires s)) = core s p) (he : q = a ++ b)
    (v : BitVec 7) (known : has (projected (rawRun (ofSector s lookup)
      (initial (ofSector s lookup)) (a.map label)).history) v.toNat = true) :
    v ∈ TightRepeats.seenAfter identity (0 :: maskBasis) (word s p) := by
  obtain ⟨r,hist,hproj⟩ := raw_projected_reflects s hs lookup a v known
  have extended := core_history_extend (keep s) (a.map (fullGate (changing s) (fixedWires s)))
    (b.map (fullGate (changing s) (fixedWires s))) r hist
  rw [← List.map_append,← he,hq] at extended
  have reflected := core_history_reflects_erasure (keep s) (word s p) r
    (control_retained s p hc) extended
  rw [← hproj]
  exact core_history_projected (keep s) (word s p) r reflected

theorem known_aux_in_full (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : Program) (hc : Compatible s p)
    (q a b : List (IndexedGate (changing s) (fixedWires s)))
    (hq : q.map (fullGate (changing s) (fixedWires s)) = core s p) (he : q = a ++ b)
    (v : BitVec 7) (known : has (projected (rawRun (ofSector s lookup)
      (initial (ofSector s lookup)) (a.map label)).history) v.toNat = true)
    (nb : SharedSearch.base.contains v.toNat = false)
    (ng : (ofSector s lookup).goals.contains v.toNat = false) : v ∈ fullAux s p := by
  have seen := prefix_seen_in_full s hs lookup p hc q a b hq he v known
  have notbase : v ∉ (0 :: maskBasis) := by
    intro hm
    have hh := List.contains_iff_mem.mpr hm
    rw [← RepeatErasure.base_agreement] at hh
    rw [nb] at hh
    contradiction
  have notgoal : v ∉ ProjectedHistory.projectedGoals s := by
    intro hm
    have hn : v.toNat ∈ (ofSector s lookup).goals := List.mem_map.mpr ⟨v,hm,rfl⟩
    have hh := List.contains_iff_mem.mpr hn
    rw [ng] at hh
    contradiction
  have ht := (List.mem_append.mp ((TightRepeats.seenAfter_members _ _ _ _).mp seen)).resolve_left notbase
  rw [full_aux_extras]
  apply (Catalogues.extras_membership _ _ _).mpr
  refine ⟨ht,?_,?_,notgoal⟩
  · intro hv
    exact notbase (List.mem_cons.mpr (Or.inl hv))
  · intro hv
    exact notbase (List.mem_cons_of_mem _ hv)

def auxiliaryList (c : Config) (z : State) : List Nat :=
  (List.range 128).filter (fun v => v != 0 && has (projected z.history) v &&
    !SharedSearch.base.contains v && !c.goals.contains v)

theorem auxiliary_list_subset (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : Program) (hc : Compatible s p)
    (q a b : List (IndexedGate (changing s) (fixedWires s)))
    (hq : q.map (fullGate (changing s) (fixedWires s)) = core s p) (he : q = a ++ b) :
    auxiliaryList (ofSector s lookup) (rawRun (ofSector s lookup)
      (initial (ofSector s lookup)) (a.map label)) ⊆ (fullAux s p).map BitVec.toNat := by
  intro n hn
  obtain ⟨hn,ht⟩ := List.mem_filter.mp hn
  have hnlt : n < 128 := List.mem_range.mp hn
  let v : BitVec 7 := BitVec.ofNat 7 n
  have hv : v.toNat = n := Nat.mod_eq_of_lt hnlt
  simp only [Bool.and_eq_true] at ht
  have hm := known_aux_in_full s hs lookup p hc q a b hq he v
    (by rw [hv]; exact ht.1.1.2) (by rw [hv]; simpa using ht.1.2) (by rw [hv]; simpa using ht.2)
  exact List.mem_map.mpr ⟨v,hm,hv⟩

theorem auxiliary_list_length (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : Program) (hc : Compatible s p)
    (q a b : List (IndexedGate (changing s) (fixedWires s)))
    (hq : q.map (fullGate (changing s) (fixedWires s)) = core s p) (he : q = a ++ b) :
    (auxiliaryList (ofSector s lookup) (rawRun (ofSector s lookup)
      (initial (ofSector s lookup)) (a.map label))).length ≤ (fullAux s p).length := by
  have hn : (auxiliaryList (ofSector s lookup) (rawRun (ofSector s lookup)
      (initial (ofSector s lookup)) (a.map label))).Nodup := List.Pairwise.filter _ List.nodup_range
  have bound := hn.length_le_of_subset (auxiliary_list_subset s hs lookup p hc q a b hq he)
  simpa only [List.length_map] using bound

def enlarged (c : Config) (z : State) (g : Nat × Nat) : List Nat :=
  let v := value c z g &&& 127
  if !(SharedSearch.base.contains v || has (projected z.history) v) && !c.goals.contains v
  then v :: auxiliaryList c z else auxiliaryList c z

theorem enlarged_nodup (c : Config) (z : State) (g : Nat × Nat) : (enlarged c z g).Nodup := by
  have ha : (auxiliaryList c z).Nodup := List.Pairwise.filter _ List.nodup_range
  unfold enlarged
  dsimp only
  split
  · apply List.nodup_cons.mpr
    refine ⟨?_,ha⟩
    intro hm
    have ht := (List.mem_filter.mp hm).2
    simp only [Bool.and_eq_true] at ht
    rename_i hnew
    simp [ht.1.1.2] at hnew
  · exact ha

theorem next_projection_known (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (a : List (IndexedGate (changing s) (fixedWires s)))
    (g : IndexedGate (changing s) (fixedWires s)) :
    has (projected (rawRun (ofSector s lookup) (initial (ofSector s lookup))
      ((a ++ [g]).map label)).history)
      (value (ofSector s lookup) (rawRun (ofSector s lookup) (initial (ofSector s lookup))
        (a.map label)) (label g) &&& 127) = true := by
  have h := KnownControls.raw_control_known s hs lookup (a ++ [g])
    ⟨g.2.val,by have hg := g.2.isLt; omega⟩
  dsimp only at h
  rw [count_matches,if_pos g.2.isLt] at h
  have after : rawRun (ofSector s lookup) (initial (ofSector s lookup)) ((a ++ [g]).map label) =
      advance (ofSector s lookup)
        (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (a.map label)) (label g) := by
    simp only [List.map_append,List.map_cons,List.map_nil,CounterBudget.raw_append,rawRun]
  have hlen := congrArg List.length (CoreGuardEncoding.raw_rows s hs lookup a)
  have hi : g.2.val < (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (a.map label)).rows.length := by
    rw [hlen]
    simpa only [rows,List.length_map] using g.2.isLt
  conv at h => lhs; arg 2; rw [after,MandatoryCount.advance_row_read _ _ _ _ hi]
  simpa only [label,ite_true] using h

theorem enlarged_subset (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : Program) (hc : Compatible s p)
    (q a b : List (IndexedGate (changing s) (fixedWires s)))
    (g : IndexedGate (changing s) (fixedWires s))
    (hq : q.map (fullGate (changing s) (fixedWires s)) = core s p) (he : q = a ++ g :: b) :
    enlarged (ofSector s lookup) (rawRun (ofSector s lookup)
      (initial (ofSector s lookup)) (a.map label)) (label g) ⊆ (fullAux s p).map BitVec.toNat := by
  let c := ofSector s lookup
  let z := rawRun c (initial c) (a.map label)
  have old := auxiliary_list_subset s hs lookup p hc q a (g :: b) hq he
  intro n hn
  unfold enlarged at hn
  dsimp only at hn
  split at hn
  · rename_i hnew
    rcases List.mem_cons.mp hn with hn | hn
    · let v : BitVec 7 := project (step (run identity (a.map (fullGate (changing s) (fixedWires s))))
        (fullGate (changing s) (fixedWires s) g) (changing s)[g.2.val])
      have hv : value c z (label g) &&& 127 = v.toNat := RepeatErasure.raw_value_projection s hs lookup a g
      change (!(SharedSearch.base.contains (value c z (label g) &&& 127) ||
        has (projected z.history) (value c z (label g) &&& 127)) &&
        !c.goals.contains (value c z (label g) &&& 127)) = true at hnew
      rw [hv] at hnew
      have hb : SharedSearch.base.contains v.toNat = false := by
        cases hb : SharedSearch.base.contains v.toNat with
        | false => rfl
        | true => simp only [hb,Bool.true_or,Bool.not_true,Bool.false_and,Bool.false_eq_true] at hnew
      have hg : c.goals.contains v.toNat = false := by
        cases hg : c.goals.contains v.toNat with
        | false => rfl
        | true => simp only [hg,Bool.not_true,Bool.and_false,Bool.false_eq_true] at hnew
      have seen := next_projection_known s hs lookup a g
      change has _ (value c z (label g) &&& 127) = true at seen
      rw [hv] at seen
      have splitq : q = (a ++ [g]) ++ b := by simpa only [List.append_assoc,List.singleton_append] using he
      have hm := known_aux_in_full s hs lookup p hc q (a ++ [g]) b hq splitq v seen hb hg
      exact List.mem_map.mpr ⟨v,hm,hv.symm.trans hn.symm⟩
    · exact old hn
  · exact old hn

theorem enlarged_length (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : Program) (hc : Compatible s p)
    (q a b : List (IndexedGate (changing s) (fixedWires s)))
    (g : IndexedGate (changing s) (fixedWires s))
    (hq : q.map (fullGate (changing s) (fixedWires s)) = core s p) (he : q = a ++ g :: b) :
    (enlarged (ofSector s lookup) (rawRun (ofSector s lookup)
      (initial (ofSector s lookup)) (a.map label)) (label g)).length ≤ (fullAux s p).length := by
  have bound := (enlarged_nodup (ofSector s lookup) _ (label g)).length_le_of_subset
    (enlarged_subset s hs lookup p hc q a b g hq he)
  simpa only [List.length_map] using bound


theorem proposal_catalogue (c : Config) (depth : Nat) (z : State) (g : Nat × Nat) :
    (propose c depth z g.1 g.2).catalogueBad =
      (decide ((enlarged c z g).length > 5-c.sources.length-(advance c z g).extra) ||
       !c.prefixAccept (if 5-c.sources.length-(advance c z g).extra ≤ 3 then 3 else 4)
         (encode (enlarged c z g))) := by rfl

theorem covered_size_bound (s : Sector) (hs : s ∈ sectors)
    (lookup : Nat → Nat → Bool) (p : Program) (hp : Legal p)
    (hc : Compatible s p) (real : run identity p = HGP13.target) (short : p.length ≤ 18) :
    ∃ q : List (IndexedGate (changing s) (fixedWires s)),
      q.map (fullGate (changing s) (fixedWires s)) = core s p ∧
      q.length = (core s p).length ∧
      ∀ a g b, q = a ++ g :: b →
        (enlarged (ofSector s lookup) (rawRun (ofSector s lookup)
          (initial (ofSector s lookup)) (a.map label)) (label g)).length ≤
          5-(ofSector s lookup).sources.length-
            (advance (ofSector s lookup) (rawRun (ofSector s lookup)
              (initial (ofSector s lookup)) (a.map label)) (label g)).extra := by
  obtain ⟨q,hq,hl,hcap⟩ := covered_prefix_capacity s hs lookup p hp hc real short
  refine ⟨q,hq,hl,?_⟩
  intro a g b he
  have hsplit : q.map label = (a ++ [g]).map label ++ b.map label := by
    rw [he]
    simp only [List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.singleton_append]
  have hbound := hcap ((a ++ [g]).map label) (b.map label) hsplit
  have hlength := enlarged_length s hs lookup p hc q a b g hq he
  have result := Nat.le_trans hlength hbound
  simpa only [List.map_append,List.map_cons,List.map_nil,CounterBudget.raw_append,rawRun] using result

theorem full_aux_catalogued (s : Sector) (p : Program) (real : run identity p = HGP13.target) :
    Catalogues.Catalogued (ProjectedHistory.projectedGoals s) (fullAux s p).length (fullAux s p) := by
  have hr := word_realizes s p real
  cases h : s.transposed with
  | false =>
    simp only [h,Bool.false_eq_true,ite_false] at hr
    simpa only [ProjectedHistory.projectedGoals,fullAux,h,Bool.false_eq_true,ite_false] using
      Catalogues.original_catalogue (word s p) hr
  | true =>
    simp only [h,ite_true] at hr
    simpa only [ProjectedHistory.projectedGoals,fullAux,h,ite_true] using
      Catalogues.transpose_catalogue (word s p) hr

end HGP13.CatalogueHistory





