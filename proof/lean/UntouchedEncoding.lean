import BasicGuards

namespace HGP13.UntouchedEncoding
open SectorCover SectorCoordinates SectorIndexing CoreRowEncoding
open SharedSearch TransitionChecks PackedRows

theorem range_reads {α : Type} [Inhabited α] (xs : List α) :
    (List.range xs.length).map (fun i => xs[i]!) = xs := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp [hj]

theorem changed_iff_target (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : List (IndexedGate (changing s) (fixedWires s))) (i : Nat) (hi : i < s.active.length) :
    has (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (p.map label)).changed i = true ↔
      s.active[i] ∈ (p.map (fullGate (changing s) (fixedWires s))).map Prod.snd := by
  rw [raw_changed]
  have hz : has (initial (ofSector s lookup)).changed i = false := by simp [initial,has]
  simp only [hz,Bool.false_eq_true,false_or]
  have hlen : i < (changing s).length := by simp [changing]; omega
  have hv : (changing s)[i] = s.active[i] := by simp [changing,hi]
  constructor
  · rintro ⟨a,ha,he,_⟩
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp ha
    refine List.mem_map.mpr ⟨fullGate (changing s) (fixedWires s) g,List.mem_map.mpr ⟨g,hg,rfl⟩,?_⟩
    change (changing s)[g.2.val] = s.active[i]
    change g.2.val = i at he
    simpa only [he] using hv
  · intro hm
    obtain ⟨a,ha,he⟩ := List.mem_map.mp hm
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp ha
    have hv' : (changing s)[g.2.val] = (changing s)[i] := by
      rw [hv]
      exact he
    have idx : g.2.val = i := (List.Nodup.getElem_inj (partition_properties s hs).1).mp hv'
    refine ⟨label g,List.mem_map.mpr ⟨g,hg,rfl⟩,idx,?_⟩
    simpa only [ofSector,List.length_map] using hi

theorem changed_bit_target (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : List (IndexedGate (changing s) (fixedWires s))) (i : Nat) (hi : i < s.active.length) :
    has (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (p.map label)).changed i =
      ((p.map (fullGate (changing s) (fixedWires s))).map Prod.snd).contains s.active[i]! := by
  apply Bool.eq_iff_iff.mpr
  rw [changed_iff_target s hs lookup p i hi,List.contains_iff_mem]
  simp [hi]

theorem untouched_count (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : List (IndexedGate (changing s) (fixedWires s))) :
    ((List.range (ofSector s lookup).sources.length).filter
      (fun i => !has (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (p.map label)).changed i)).length =
      (RemainingBound.untouched s.active (p.map (fullGate (changing s) (fixedWires s)))).length := by
  have hn : (ofSector s lookup).sources.length = s.active.length := by simp [ofSector]
  rw [hn]
  unfold RemainingBound.untouched
  conv => rhs; rw [← range_reads s.active,List.filter_map,List.length_map]
  congr 1
  apply List.filter_congr
  intro i hi
  have hb := changed_bit_target s hs lookup p i (List.mem_range.mp hi)
  simpa only [Function.comp_apply,hb]

theorem filter_indices_count {α : Type} [Inhabited α] (xs : List α) (f : α → Bool) :
    ((List.range xs.length).filter (fun i => f xs[i]!)).length = (xs.filter f).length := by
  conv => rhs; rw [← range_reads xs,List.filter_map,List.length_map]
  rfl

theorem packed_mismatch_count {n : Nat} (e : Fin n → Wire) (a : List Wire) (x z : Matrix)
    (hx : ∀ i ∈ a, RowSupported e (x i)) (hz : ∀ i ∈ a, RowSupported e (z i)) :
    ((List.range a.length).filter (fun i => (rows e a x)[i]! != (rows e a z)[i]!)).length =
      (a.filter (fun i => x i != z i)).length := by
  rw [← filter_indices_count a (fun i => x i != z i)]
  apply congrArg List.length
  apply List.filter_congr
  intro i hi
  have hb : i < a.length := List.mem_range.mp hi
  rw [rows_get e a x i hb,rows_get e a z i hb]
  have he : (pack e (x a[i])).toNat = (pack e (z a[i])).toNat ↔ x a[i] = z a[i] := by
    constructor
    · intro h
      exact (pack_faithful e _ _ (hx _ (List.getElem_mem hb)) (hz _ (List.getElem_mem hb))).mp
        (BitVec.eq_of_toNat_eq h)
    · intro h
      rw [h]
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne]
  simpa [hb] using not_congr he

theorem packed_mismatch_bound {n : Nat} (e : Fin n → Wire) (a : List Wire)
    (ha : a.Nodup) (x z : Matrix)
    (hx : ∀ i ∈ a, RowSupported e (x i)) (hz : ∀ i ∈ a, RowSupported e (z i)) :
    ((List.range a.length).filter (fun i => (rows e a x)[i]! != (rows e a z)[i]!)).length ≤
      (RemainingBound.different x z).length := by
  rw [packed_mismatch_count e a x z hx hz]
  have hn : (a.filter (fun i => x i != z i)).Nodup := List.Pairwise.filter _ ha
  apply hn.length_le_of_subset
  intro i hi
  apply (RemainingBound.different_members x z i).mpr
  simpa only [bne_iff_ne] using (List.mem_filter.mp hi).2
theorem core_mismatch_bound (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : Program) (hc : Compatible s p) (real : run identity p = HGP13.target)
    (q a : List (IndexedGate (changing s) (fixedWires s)))
    (hq : q.map (fullGate (changing s) (fixedWires s)) = core s p) :
    ((List.range (count (ofSector s lookup))).filter (fun i =>
      (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (a.map label)).rows[i]! !=
        (want (ofSector s lookup))[i]!)).length ≤
      (RemainingBound.different (run identity (a.map (fullGate (changing s) (fixedWires s))))
        (run identity (q.map (fullGate (changing s) (fixedWires s))))).length := by
  have ht := BasicGuards.core_terminal s hs lookup p hc real q hq
  simp only [terminal,Bool.and_eq_true,beq_iff_eq] at ht
  obtain ⟨hd,_,hj⟩ := partition_properties s hs
  obtain ⟨hr,_,hf,_⟩ := initial_matches_full_matrix s hs lookup
  have hra := raw_rows_run (embed s) (changing s) (fixedWires s) hd hj
    (ofSector s lookup) (count_matches s lookup) a identity (initial (ofSector s lookup)) hr hf
  have hrq := raw_rows_run (embed s) (changing s) (fixedWires s) hd hj
    (ofSector s lookup) (count_matches s lookup) q identity (initial (ofSector s lookup)) hr hf
  rw [← ht.2,hra,hrq,count_matches]
  apply packed_mismatch_bound (embed s) (changing s) hd
  · intro i hi
    exact IndexedEffectiveness.retained_row_supported s hs a i (changing_retained s hs i hi)
  · intro i hi
    exact IndexedEffectiveness.retained_row_supported s hs q i (changing_retained s hs i hi)
end HGP13.UntouchedEncoding




