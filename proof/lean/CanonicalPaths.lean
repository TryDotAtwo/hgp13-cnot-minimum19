import GoalSaturation

namespace HGP13.CanonicalPaths
open HGP13.GoalSaturation HGP13.Catalogues

def normalize (xs : List Value) : List Value :=
  (SharedSearch.sort (xs.map BitVec.toNat)).map (BitVec.ofNat 7)

theorem normalize_perm (xs : List Value) : List.Perm (normalize xs) xs :=
  PrefixBridge.sorted_value_perm xs

theorem normalize_congr (xs ys : List Value) (hp : List.Perm xs ys) :
    normalize xs = normalize ys := by
  unfold normalize
  rw [SortEncoding.sort_perm_eq _ _ (hp.map BitVec.toNat)]

theorem saturation_perm (base goals xs ys : List Value)
    (hp : List.Perm xs ys) :
    ∀ z, z ∈ saturation (base ++ xs) goals ↔
      z ∈ saturation (base ++ ys) goals := by
  have hab : base ++ xs ⊆ base ++ ys := by
    intro z hz
    exact (hp.append_left base).mem_iff.mp hz
  have hba : base ++ ys ⊆ base ++ xs := by
    intro z hz
    exact (hp.symm.append_left base).mem_iff.mp hz
  intro z
  exact ⟨fun hz => saturation_mono _ _ goals hab hz,
    fun hz => saturation_mono _ _ goals hba hz⟩

theorem derivable_perm (base goals xs ys : List Value)
    (hp : List.Perm xs ys) (z : Value) :
    derivable (saturation (base ++ xs) goals) z = true ↔
      derivable (saturation (base ++ ys) goals) z = true := by
  have heq := saturation_perm base goals xs ys hp
  exact ⟨derivable_mono _ _ z (fun v hv => (heq v).mp hv),
    derivable_mono _ _ z (fun v hv => (heq v).mpr hv)⟩

def states (base goals : List Value) : Nat → List (List Value)
  | 0 => [[]]
  | n+1 => ((states base goals n).flatMap fun xs =>
      (allValues.filter fun z =>
        z != 0 && !((saturation (base ++ xs) goals).contains z) &&
          derivable (saturation (base ++ xs) goals) z).map
        (fun z => normalize (xs ++ [z]))).eraseDups

theorem saturation_subset (available goals : List Value) :
    saturation available goals ⊆ available ++ goals := by
  intro z hz
  have h := (endState_members available (build goals.length goals available) z).mp hz
  rcases List.mem_append.mp h with ha | hp
  · exact List.mem_append_left _ ha
  · exact List.mem_append_right _ (build_subset _ _ _ hp)

theorem normalized_path_mem (base goals xs : List Value)
    (hp : ExtraPath base goals xs) (hn : xs.Nodup)
    (hs : ∀ z ∈ xs, z ≠ 0 ∧ z ∉ base ∧ z ∉ goals) :
    normalize xs ∈ states base goals xs.length := by
  induction hp with
  | nil => simp [states,normalize,SharedSearch.sort]
  | @snoc ys h z ready ih =>
    have hparts := List.nodup_append.mp hn
    have hny : ys.Nodup := hparts.1
    have hnz : z ∉ ys := by
      intro hz
      exact hparts.2.2 z hz z (List.mem_singleton_self z) rfl
    have hsy : ∀ v ∈ ys, v ≠ 0 ∧ v ∉ base ∧ v ∉ goals := by
      intro v hv
      exact hs v (List.mem_append_left _ hv)
    have hsz : z ≠ 0 ∧ z ∉ base ∧ z ∉ goals :=
      hs z (List.mem_append_right _ (List.mem_singleton_self z))
    have hnotSat : z ∉ saturation (base ++ normalize ys) goals := by
      intro hz
      have hz' := saturation_subset (base ++ normalize ys) goals hz
      rcases List.mem_append.mp hz' with hleft | hg
      · rcases List.mem_append.mp hleft with hb | hy
        · exact hsz.2.1 hb
        · exact hnz ((normalize_perm ys).mem_iff.mp hy)
      · exact hsz.2.2 hg
    rw [List.length_append, List.length_singleton]
    simp only [states,List.mem_eraseDups,List.mem_flatMap]
    refine ⟨normalize ys,ih hny hsy,?_⟩
    apply List.mem_map.mpr
    refine ⟨z,List.mem_filter.mpr ⟨mem_allValues z,?_⟩,?_⟩
    · have hd := (derivable_perm base goals ys (normalize ys)
        (normalize_perm ys).symm z).mp ready
      simp only [Bool.and_eq_true]
      exact ⟨⟨by simpa using hsz.1,by simp [hnotSat]⟩,hd⟩
    · have hpappend : List.Perm (normalize ys ++ [z]) (ys ++ [z]) :=
        (normalize_perm ys).append_right [z]
      exact normalize_congr _ _ hpappend

theorem catalogued_mem_states (goals extra : List Value) (k : Nat)
    (hc : Catalogued goals k extra) :
    normalize extra ∈ states FreeXor.maskBasis goals k := by
  obtain ⟨xs,hpath,hperm⟩ :=
    GoalSaturation.catalogued_extra_path goals extra k hc
  have hlen : xs.length = k := by
    rw [hperm.length_eq]
    exact hc.2.1
  have hn : xs.Nodup := hperm.nodup_iff.mpr hc.1
  have hs : ∀ z ∈ xs, z ≠ 0 ∧ z ∉ FreeXor.maskBasis ∧ z ∉ goals := by
    intro z hz
    exact hc.2.2.1 z (hperm.mem_iff.mp hz)
  rw [← normalize_congr xs extra hperm]
  exact hlen ▸ normalized_path_mem _ _ _ hpath hn hs

theorem catalogued_four_lookup (goals extra : List Value) (observed : List Nat)
    (lookup : Nat → Bool) (hc : Catalogued goals 4 extra)
    (ho : observed.Nodup) (hs : observed ⊆ extra.map BitVec.toNat)
    (hfinite : ∀ xs ∈ states FreeXor.maskBasis goals 4,
      ∀ m < 16, lookup (SharedSearch.encode (SortEncoding.subset
        (SharedSearch.sort (xs.map BitVec.toNat)) m)) = true) :
    lookup (SharedSearch.encode observed) = true := by
  have hmem := catalogued_mem_states goals extra 4 hc
  obtain ⟨m,hm,hkey⟩ := PrefixBridge.observed_catalogued_four goals extra observed hc ho hs
  have hsorted : SharedSearch.sort ((normalize extra).map BitVec.toNat) =
      SharedSearch.sort (extra.map BitVec.toNat) :=
    SortEncoding.sort_perm_eq _ _ ((normalize_perm extra).map BitVec.toNat)
  rw [hkey,← hsorted]
  exact hfinite (normalize extra) hmem m hm

theorem catalogued_three_lookup (goals extra : List Value) (observed : List Nat)
    (lookup : Nat → Bool) (hc : Catalogued goals 3 extra)
    (ho : observed.Nodup) (hs : observed ⊆ extra.map BitVec.toNat)
    (hfinite : ∀ xs ∈ states FreeXor.maskBasis goals 3,
      ∀ m < 8, lookup (SharedSearch.encode (SortEncoding.subset
        (SharedSearch.sort (xs.map BitVec.toNat)) m)) = true) :
    lookup (SharedSearch.encode observed) = true := by
  have hmem := catalogued_mem_states goals extra 3 hc
  obtain ⟨m,hm,hkey⟩ := PrefixBridge.observed_catalogued_three goals extra observed hc ho hs
  have hsorted : SharedSearch.sort ((normalize extra).map BitVec.toNat) =
      SharedSearch.sort (extra.map BitVec.toNat) :=
    SortEncoding.sort_perm_eq _ _ ((normalize_perm extra).map BitVec.toNat)
  rw [hkey,← hsorted]
  exact hfinite (normalize extra) hmem m hm

end HGP13.CanonicalPaths
