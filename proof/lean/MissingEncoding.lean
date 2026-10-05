import UntouchedEncoding

namespace HGP13.MissingEncoding
open SectorCoordinates CoreRowEncoding PackedRows

def packedMissing {n : Nat} (e : Fin n → Wire) (a b : List Wire) (x z : Matrix) : List Nat :=
  ((((List.range a.length).filter (fun i => (rows e a x)[i]! != (rows e a z)[i]!)).map
    (fun i => (rows e a x)[i]! ^^^ (rows e a z)[i]!)).filter
      (fun v => !(rows e a x ++ rows e a z ++ rows e b x).contains v)).eraseDups

theorem code_in_rows {n : Nat} (e : Fin n → Wire) (a : List Wire) (x : Matrix)
    (i : Wire) (hi : i ∈ a) : (pack e (x i)).toNat ∈ rows e a x :=
  List.mem_map.mpr ⟨i,hi,rfl⟩

theorem delta_supported_rows {n : Nat} (e : Fin n → Wire) (x z : Matrix) (i : Wire)
    (hx : RowSupported e (x i)) (hz : RowSupported e (z i)) :
    RowSupported e (x i ^^^ z i) := by
  intro j hj
  simp only [BitVec.getLsbD_xor,hx j hj,hz j hj,Bool.false_xor]

theorem available_code {n : Nat} (e : Fin n → Wire) (a b : List Wire) (x z : Matrix)
    (cover : ∀ k, e k ∈ a ++ b) (fixed : ∀ i ∈ b, z i = x i)
    (ox : ∀ j, (∀ k, e k ≠ j) → x j = identity j)
    (oz : ∀ j, (∀ k, e k ≠ j) → z j = identity j)
    (v : Row) (hv : RowSupported e v)
    (available : v ∈ RemainingBound.rows x ∨ v ∈ RemainingBound.rows z) :
    (pack e v).toNat ∈ rows e a x ++ rows e a z ++ rows e b x := by
  rcases available with available | available
  · obtain ⟨i,hi⟩ := (RemainingBound.rows_members x v).mp available
    obtain ⟨k,hk⟩ := (full_row_available_iff e x v hv ox).mp ⟨i,hi⟩
    rcases List.mem_append.mp (cover k) with ha | hb
    · apply List.mem_append_left
      apply List.mem_append_left
      rw [← hk]
      exact code_in_rows e a x _ ha
    · apply List.mem_append_right
      rw [← hk]
      exact code_in_rows e b x _ hb
  · obtain ⟨i,hi⟩ := (RemainingBound.rows_members z v).mp available
    obtain ⟨k,hk⟩ := (full_row_available_iff e z v hv oz).mp ⟨i,hi⟩
    rcases List.mem_append.mp (cover k) with ha | hb
    · apply List.mem_append_left
      apply List.mem_append_right
      rw [← hk]
      exact code_in_rows e a z _ ha
    · apply List.mem_append_right
      rw [← hk,fixed _ hb]
      exact code_in_rows e b x _ hb

theorem missing_reflects {n : Nat} (e : Fin n → Wire) (a b : List Wire) (x z : Matrix)
    (cover : ∀ k, e k ∈ a ++ b) (fixed : ∀ i ∈ b, z i = x i)
    (ox : ∀ j, (∀ k, e k ≠ j) → x j = identity j)
    (oz : ∀ j, (∀ k, e k ≠ j) → z j = identity j)
    (hx : ∀ i ∈ a, RowSupported e (x i)) (hz : ∀ i ∈ a, RowSupported e (z i))
    (v : Nat) (hv : v ∈ packedMissing e a b x z) :
    v ∈ (RemainingBound.missing x z).map (fun r => (pack e r).toNat) := by
  simp only [packedMissing,List.mem_eraseDups,List.mem_filter] at hv
  obtain ⟨hm,hn⟩ := hv
  obtain ⟨i,hi,he⟩ := List.mem_map.mp hm
  obtain ⟨hrange,hd⟩ := List.mem_filter.mp hi
  have hb : i < a.length := List.mem_range.mp hrange
  rw [rows_get e a x i hb,rows_get e a z i hb] at hd he
  have hdiff : x a[i] ≠ z a[i] := by
    intro h
    simp [h] at hd
  have he' : (pack e (x a[i] ^^^ z a[i])).toNat = v := by rw [pack_nat_xor]; exact he
  apply List.mem_map.mpr
  refine ⟨x a[i] ^^^ z a[i],?_,he'⟩
  apply (RemainingBound.missing_members x z _).mpr
  have hsup := delta_supported_rows e x z a[i] (hx _ (List.getElem_mem hb)) (hz _ (List.getElem_mem hb))
  have hnot : (pack e (x a[i] ^^^ z a[i])).toNat ∉ rows e a x ++ rows e a z ++ rows e b x := by
    rw [he']
    simpa using hn
  refine ⟨⟨a[i],hdiff,rfl⟩,?_,?_⟩
  · intro h
    exact hnot (available_code e a b x z cover fixed ox oz _ hsup (Or.inl h))
  · intro h
    exact hnot (available_code e a b x z cover fixed ox oz _ hsup (Or.inr h))

theorem packed_missing_bound {n : Nat} (e : Fin n → Wire) (a b : List Wire) (x z : Matrix)
    (cover : ∀ k, e k ∈ a ++ b) (fixed : ∀ i ∈ b, z i = x i)
    (ox : ∀ j, (∀ k, e k ≠ j) → x j = identity j)
    (oz : ∀ j, (∀ k, e k ≠ j) → z j = identity j)
    (hx : ∀ i ∈ a, RowSupported e (x i)) (hz : ∀ i ∈ a, RowSupported e (z i)) :
    (packedMissing e a b x z).length ≤ (RemainingBound.missing x z).length := by
  have hn : (packedMissing e a b x z).Nodup := CountHelpers.eraseDups_nodup _
  have h := hn.length_le_of_subset (fun v hv => missing_reflects e a b x z cover fixed ox oz hx hz v hv)
  simpa only [List.length_map] using h

open SectorCover SectorIndexing SharedSearch TransitionChecks

theorem indexed_outside (s : Sector) (hs : s ∈ sectors)
    (p : List (IndexedGate (changing s) (fixedWires s))) (j : Wire)
    (hj : ∀ k, embed s k ≠ j) :
    run identity (p.map (fullGate (changing s) (fixedWires s))) j = identity j := by
  apply Budget.run_untargeted
  intro hm
  obtain ⟨g,hg,he⟩ := List.mem_map.mp hm
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
  obtain ⟨_,⟨k,hk⟩⟩ := IndexedEffectiveness.gate_endpoints s hs a
  exact hj k (hk.trans he)

theorem fixed_pointwise (a b : List Wire) (disjoint : ∀ i ∈ a, ∀ j ∈ b, i ≠ j)
    (p : List (IndexedGate a b)) (j : Wire) (hj : j ∈ b) :
    run identity (p.map (fullGate a b)) j = identity j := by
  apply Budget.run_untargeted
  intro hm
  obtain ⟨g,hg,he⟩ := List.mem_map.mp hm
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hg
  exact disjoint _ (List.getElem_mem k.2.isLt) j hj he

def stateMissing (c : Config) (z : State) : List Nat :=
  ((((List.range (count c)).filter (fun i => z.rows[i]! != (want c)[i]!)).map
    (fun i => z.rows[i]! ^^^ (want c)[i]!)).filter
      (fun v => !(z.rows ++ want c ++ fixed c).contains v)).eraseDups

theorem core_missing_bound (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : Program) (hc : Compatible s p) (real : run identity p = HGP13.target)
    (q a : List (IndexedGate (changing s) (fixedWires s)))
    (hq : q.map (fullGate (changing s) (fixedWires s)) = core s p) :
    (stateMissing (ofSector s lookup)
      (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (a.map label))).length ≤
    (RemainingBound.missing (run identity (a.map (fullGate (changing s) (fixedWires s))))
      (run identity (q.map (fullGate (changing s) (fixedWires s))))).length := by
  obtain ⟨hd,_,hj⟩ := partition_properties s hs
  obtain ⟨hr,_,hf,_⟩ := initial_matches_full_matrix s hs lookup
  have hra := raw_rows_run (embed s) (changing s) (fixedWires s) hd hj
    (ofSector s lookup) (count_matches s lookup) a identity (initial (ofSector s lookup)) hr hf
  have hrq := raw_rows_run (embed s) (changing s) (fixedWires s) hd hj
    (ofSector s lookup) (count_matches s lookup) q identity (initial (ofSector s lookup)) hr hf
  have ht := BasicGuards.core_terminal s hs lookup p hc real q hq
  simp only [terminal,Bool.and_eq_true,beq_iff_eq] at ht
  have hw := ht.2.symm.trans hrq
  have hf' : fixed (ofSector s lookup) = rows (embed s) (fixedWires s)
      (run identity (a.map (fullGate (changing s) (fixedWires s)))) := by
    rw [KnownControls.fixed_run (embed s) (changing s) (fixedWires s) hj]
    exact hf
  unfold stateMissing
  rw [count_matches,hra,hw,hf']
  apply packed_missing_bound (embed s) (changing s) (fixedWires s)
  · intro k
    apply input_member
    exact (embed_image s _).mp ⟨k,rfl⟩
  · intro i hi
    rw [fixed_pointwise _ _ hj q i hi,fixed_pointwise _ _ hj a i hi]
  · exact indexed_outside s hs a
  · exact indexed_outside s hs q
  · intro i hi
    exact IndexedEffectiveness.retained_row_supported s hs a i (changing_retained s hs i hi)
  · intro i hi
    exact IndexedEffectiveness.retained_row_supported s hs q i (changing_retained s hs i hi)
def stateBound (c : Config) (z : State) : Nat :=
  let r := ((List.range (count c)).filter (fun i => z.rows[i]! != (want c)[i]!)).length
  let untouched := ((List.range c.sources.length).filter (fun i => !has z.changed i)).length
  max (r+2*untouched) (r+((stateMissing c z).length+1)/2)

theorem state_bound_semantic (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : Program) (hc : Compatible s p) (real : run identity p = HGP13.target)
    (q a : List (IndexedGate (changing s) (fixedWires s)))
    (hq : q.map (fullGate (changing s) (fixedWires s)) = core s p) :
    stateBound (ofSector s lookup)
      (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (a.map label)) ≤
    RemainingBound.remaining (run identity (a.map (fullGate (changing s) (fixedWires s))))
      (run identity (q.map (fullGate (changing s) (fixedWires s))))
      (RemainingBound.untouched s.active (a.map (fullGate (changing s) (fixedWires s)))) := by
  have hm := UntouchedEncoding.core_mismatch_bound s hs lookup p hc real q a hq
  have hd := core_missing_bound s hs lookup p hc real q a hq
  unfold stateBound
  rw [UntouchedEncoding.untouched_count s hs lookup a]
  simp only [RemainingBound.remaining]
  omega

theorem state_bound_suffix (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : Program) (hp : Legal p) (hc : Compatible s p) (real : run identity p = HGP13.target)
    (q a b : List (IndexedGate (changing s) (fixedWires s)))
    (hq : q.map (fullGate (changing s) (fixedWires s)) = core s p) (he : q = a ++ b) :
    stateBound (ofSector s lookup)
      (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (a.map label)) ≤ b.length := by
  have bound := state_bound_semantic s hs lookup p hc real q a hq
  have hlegal : Legal (q.map (fullGate (changing s) (fixedWires s))) := by
    rw [hq]
    intro g hg
    exact word_legal s p hp g (List.mem_filter.mp hg).1
  have final := RemainingBound.erased_run_goal (word s p) (keep s) (goal s)
    (control_retained s p hc) (word_realizes s p real)
  change run identity (core s p) = RemainingBound.coreGoal (keep s) (goal s) at final
  have hnd : s.active.Nodup :=
    (List.nodup_append.mp (List.nodup_append.mp (partition_properties s hs).1).1).1
  have hrem := RemainingBound.prefix_remaining_bound
    (a.map (fullGate (changing s) (fixedWires s))) (b.map (fullGate (changing s) (fixedWires s)))
    (run identity (q.map (fullGate (changing s) (fixedWires s)))) s.active
    (by rw [← List.map_append,← he]; exact hlegal)
    (by rw [← List.map_append,← he]) hnd (by
      intro i hi
      have hk : keep s i = true := changing_retained s hs i (by simp [changing,hi])
      have hsource := (layout_properties s hs).2.2.2.1 hi
      have hgoal : goal s i = identity i := by
        unfold goal
        split
        · exact TransposeTarget.sources_fixed i hsource
        · exact Budget.sources_fixed i hsource
      constructor
      · rw [hq,final]
        simp [RemainingBound.coreGoal,hk,hgoal]
      · obtain ⟨g,hg,hgi⟩ := active_is_used s p hc i hi
        have hit := RemainingBound.filtered_target_members (word s p) (keep s) i hk
          (List.mem_map.mpr ⟨g,hg,hgi⟩)
        change i ∈ (core s p).map Prod.snd at hit
        rw [← List.map_append,← he,hq]
        exact hit)
  have result := Nat.le_trans bound hrem
  simpa only [List.length_map] using result

theorem proposal_depth (c : Config) (depth : Nat) (z : State) (t j : Nat) :
    (propose c depth z t j).depthBad =
      decide (depth+1+stateBound c (advance c z (t,j)) > maxDepth c) := by
  simp only [propose,stateBound,stateMissing,advance,List.length_map]

theorem core_depth_guard (s : Sector) (hs : s ∈ sectors) (lookup : Nat → Nat → Bool)
    (p : Program) (hp : Legal p) (hc : Compatible s p) (real : run identity p = HGP13.target)
    (short : p.length ≤ 18) (q a b : List (IndexedGate (changing s) (fixedWires s)))
    (g : IndexedGate (changing s) (fixedWires s))
    (hq : q.map (fullGate (changing s) (fixedWires s)) = core s p) (he : q = a ++ g :: b) :
    (propose (ofSector s lookup) a.length
      (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (a.map label)) g.2.val g.1.val).depthBad = false := by
  have hsplit : q = (a ++ [g]) ++ b := by simpa only [List.append_assoc,List.singleton_append] using he
  have hb := state_bound_suffix s hs lookup p hp hc real q (a ++ [g]) b hq hsplit
  simp only [List.map_append,List.map_cons,List.map_nil,CounterBudget.raw_append,rawRun] at hb
  have hl : q.length = (core s p).length := by rw [← hq,List.length_map]
  have hdepth := core_depth_bound s hs p real short
  have hlen : q.length = a.length+1+b.length := by rw [he]; simp; omega
  have hd : maxDepth (ofSector s lookup) = 12+s.carriers.length := by simp [maxDepth,ofSector]
  rw [proposal_depth]
  apply decide_eq_false
  apply Nat.not_lt.mpr
  change a.length+1+stateBound (ofSector s lookup)
    (advance (ofSector s lookup) (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (a.map label)) (label g)) ≤ _
  rw [hd]
  omega
end HGP13.MissingEncoding




