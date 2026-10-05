import PrefixBridge

namespace HGP13.GoalSaturation
open HGP13.Catalogues

theorem validMasks_mono (available more p : List Value)
    (hsub : available ⊆ more)
    (hv : FreeXor.validMasks available p = true) :
    FreeXor.validMasks more p = true := by
  induction p generalizing available more with
  | nil => rfl
  | cons z rest ih =>
    simp only [FreeXor.validMasks,Bool.and_eq_true] at hv ⊢
    obtain ⟨x,hx,hxy⟩ := List.any_eq_true.mp hv.1
    obtain ⟨y,hy,he⟩ := List.any_eq_true.mp hxy
    constructor
    · exact List.any_eq_true.mpr
        ⟨x,hsub hx,List.any_eq_true.mpr ⟨y,hsub hy,he⟩⟩
    · apply ih (z :: available) (z :: more)
      · intro v h
        rcases List.mem_cons.mp h with rfl | h
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub h)
      · exact hv.2

theorem derivable_mono (available more : List Value) (z : Value)
    (hsub : available ⊆ more)
    (hd : derivable available z = true) : derivable more z = true := by
  obtain ⟨x,hx,hxy⟩ := List.any_eq_true.mp hd
  obtain ⟨y,hy,he⟩ := List.any_eq_true.mp hxy
  exact List.any_eq_true.mpr
    ⟨x,hsub hx,List.any_eq_true.mpr ⟨y,hsub hy,he⟩⟩

theorem saturation_mono (available more goals : List Value)
    (hsub : available ⊆ more) :
    saturation available goals ⊆ saturation more goals := by
  let p := build goals.length goals available
  have hv : FreeXor.validMasks available p = true := build_valid _ _ _
  have hvMore : FreeXor.validMasks more p = true := validMasks_mono available more p hsub hv
  have restricted : p ⊆ goals := build_subset _ _ _
  have hall := every_program_in_saturation more goals p hvMore restricted
  intro z hz
  have h_old : z ∈ available ++ p := by
    exact (endState_members available p z).mp hz
  apply hall
  rcases List.mem_append.mp h_old with hm | hp
  · exact List.mem_append_left _ (hsub hm)
  · exact List.mem_append_right _ hp

theorem goal_step_stays (base extras goals current : List Value) (z : Value)
    (hcurrent : current ⊆ saturation (base ++ extras) goals)
    (hgoal : z ∈ goals) (hready : derivable current z = true) :
    z :: current ⊆ saturation (base ++ extras) goals := by
  have hz : z ∈ saturation (base ++ extras) goals :=
    saturation_closed (base ++ extras) goals z hgoal
      (derivable_mono current _ z hcurrent hready)
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hz
  · exact hcurrent hv

theorem extra_ready (base extras goals current : List Value) (z : Value)
    (hcurrent : current ⊆ saturation (base ++ extras) goals)
    (hready : derivable current z = true) :
    derivable (saturation (base ++ extras) goals) z = true :=
  derivable_mono current _ z hcurrent hready

theorem extra_step_expands (base extras goals current : List Value) (z : Value)
    (hcurrent : current ⊆ saturation (base ++ extras) goals) :
    z :: current ⊆ saturation ((base ++ extras) ++ [z]) goals := by
  have hmono : saturation (base ++ extras) goals ⊆
      saturation ((base ++ extras) ++ [z]) goals :=
    saturation_mono (base ++ extras) ((base ++ extras) ++ [z]) goals
      (fun v hv => List.mem_append_left _ hv)
  intro v hv
  rcases List.mem_cons.mp hv with he | hv
  · simpa only [he] using
      (saturation_initial ((base ++ extras) ++ [z]) goals
        (List.mem_append_right _ (List.mem_singleton_self z)))
  · exact hmono (hcurrent hv)

inductive ExtraPath (base goals : List Value) : List Value → Prop where
  | nil : ExtraPath base goals []
  | snoc {xs : List Value} (h : ExtraPath base goals xs) (z : Value)
      (ready : derivable (saturation (base ++ xs) goals) z = true) :
      ExtraPath base goals (xs ++ [z])

theorem reorder_current_step (current rest : List Value) (z : Value) :
    current ++ (z :: rest) ⊆ (z :: current) ++ rest := by
  intro v hv
  rcases List.mem_append.mp hv with hc | ht
  · exact List.mem_append_left _ (List.mem_cons_of_mem z hc)
  · rcases List.mem_cons.mp ht with he | ht
    · exact List.mem_append_left _ (List.mem_cons.mpr (Or.inl he))
    · exact List.mem_append_right _ ht

theorem valid_schedule_path_aux (base goals allowed current p xs : List Value)
    (hpath : ExtraPath base goals xs) (hxs : xs ⊆ allowed)
    (hcurrent : current ⊆ saturation (base ++ xs) goals)
    (hv : FreeXor.validMasks current p = true)
    (hr : p ⊆ goals ++ allowed) :
    ∃ ys, ys = xs ++ p.filter (fun z => !goals.contains z) ∧
      ExtraPath base goals ys ∧ ys ⊆ allowed ∧
      current ++ p ⊆ saturation (base ++ ys) goals := by
  induction p generalizing current xs with
  | nil =>
    exact ⟨xs,by simp,hpath,hxs,by simpa using hcurrent⟩
  | cons z rest ih =>
    simp only [FreeXor.validMasks,Bool.and_eq_true] at hv
    have hwhere : z ∈ goals ∨ z ∈ allowed :=
      List.mem_append.mp (hr (List.mem_cons_self))
    have hrest : rest ⊆ goals ++ allowed := by
      intro v hv
      exact hr (List.mem_cons_of_mem z hv)
    by_cases hg : z ∈ goals
    · have hc : z :: current ⊆ saturation (base ++ xs) goals :=
        goal_step_stays base xs goals current z hcurrent hg hv.1
      obtain ⟨ys,hyeq,hy,hyallowed,hycovered⟩ :=
        ih (z :: current) xs hpath hxs hc hv.2 hrest
      have hb : goals.contains z = true := List.contains_iff_mem.mpr hg
      refine ⟨ys,?_,hy,hyallowed,fun v hv =>
        hycovered (reorder_current_step current rest z hv)⟩
      simpa [List.filter, hg] using hyeq
    · have hz : z ∈ allowed := hwhere.resolve_left hg
      have hready := extra_ready base xs goals current z hcurrent hv.1
      have hnewpath : ExtraPath base goals (xs ++ [z]) :=
        ExtraPath.snoc hpath z hready
      have hnewallowed : xs ++ [z] ⊆ allowed := by
        intro v hv
        rcases List.mem_append.mp hv with hv | hv
        · exact hxs hv
        · exact (List.mem_singleton.mp hv) ▸ hz
      have hc : z :: current ⊆ saturation (base ++ (xs ++ [z])) goals := by
        simpa only [List.append_assoc] using
          extra_step_expands base xs goals current z hcurrent
      obtain ⟨ys,hyeq,hy,hyallowed,hycovered⟩ :=
        ih (z :: current) (xs ++ [z]) hnewpath hnewallowed hc hv.2 hrest
      have hb : goals.contains z = false := by
        cases hb : goals.contains z with
        | false => rfl
        | true => exact False.elim (hg (List.contains_iff_mem.mp hb))
      refine ⟨ys,?_,hy,hyallowed,fun v hv =>
        hycovered (reorder_current_step current rest z hv)⟩
      simpa [List.filter, hg,List.append_assoc] using hyeq

theorem valid_schedule_path (base goals allowed p : List Value)
    (hv : FreeXor.validMasks base p = true)
    (hr : p ⊆ goals ++ allowed) :
    ∃ xs, xs = p.filter (fun z => !goals.contains z) ∧
      ExtraPath base goals xs ∧ xs ⊆ allowed ∧
      base ++ p ⊆ saturation (base ++ xs) goals := by
  obtain ⟨xs,hx,hpath,hallowed,hcover⟩ :=
    valid_schedule_path_aux base goals allowed base p []
    (ExtraPath.nil) (by simp)
    (by intro z hz; exact saturation_initial (base ++ []) goals (by simpa using hz))
    hv hr
  exact ⟨xs,by simpa using hx,hpath,hallowed,hcover⟩

theorem fresh_avoids (available p : List Value)
    (hf : Fresh available p) : ∀ z ∈ p, z ∉ available := by
  induction p generalizing available with
  | nil => simp
  | cons x rest ih =>
    simp only [Fresh] at hf
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hf.1
    · exact fun h => ih (x :: available) hf.2 z hz (List.mem_cons_of_mem x h)

theorem fresh_nodup (available p : List Value)
    (hf : Fresh available p) : p.Nodup := by
  induction p generalizing available with
  | nil => simp
  | cons x rest ih =>
    simp only [Fresh] at hf
    refine List.nodup_cons.mpr ⟨?_,ih (x :: available) hf.2⟩
    intro hx
    exact fresh_avoids (x :: available) rest hf.2 x hx List.mem_cons_self

theorem nodup_perm_of_mem (xs ys : List Value) (hx : xs.Nodup) (hy : ys.Nodup)
    (hm : ∀ z, z ∈ xs ↔ z ∈ ys) : List.Perm xs ys := by
  apply List.perm_iff_count.mpr
  intro z
  rw [hx.count,hy.count]
  by_cases h : z ∈ xs
  · have hyz : z ∈ ys := (hm z).mp h
    simp [h,hyz]
  · have hyz : z ∉ ys := fun hyz => h ((hm z).mpr hyz)
    simp [h,hyz]

theorem catalogued_extra_path (goals extra : List Value) (k : Nat)
    (hc : Catalogued goals k extra) :
    ∃ xs, ExtraPath FreeXor.maskBasis goals xs ∧ List.Perm xs extra := by
  obtain ⟨hextra,_,hseparate,p,hv,hfresh,hrestricted,hcomplete⟩ :=
    (catalogue_characterization goals extra k).mp hc
  obtain ⟨xs,hxeq,hpath,_,_⟩ :=
    valid_schedule_path FreeXor.maskBasis goals extra p hv hrestricted
  refine ⟨xs,hpath,nodup_perm_of_mem xs extra ?_ hextra ?_⟩
  · rw [hxeq]
    exact List.Pairwise.filter _ (fresh_nodup _ _ hfresh)
  · intro z
    rw [hxeq]
    simp only [List.mem_filter]
    constructor
    · intro ⟨hz,hnot⟩
      rcases List.mem_append.mp (hrestricted hz) with hg | he
      · simp [hg] at hnot
      · exact he
    · intro he
      have hnot : z ∉ goals := (hseparate z he).2.2
      have hp : z ∈ p := by
        rcases List.mem_append.mp (hcomplete (List.mem_append_right _ he)) with hb | hp
        · exact False.elim ((hseparate z he).2.1 hb)
        · exact hp
      exact ⟨hp,by simp [hnot]⟩

def allValues : List Value := (List.range 128).map (BitVec.ofNat 7)

theorem mem_allValues (z : Value) : z ∈ allValues := by
  apply List.mem_map.mpr
  refine ⟨z.toNat, List.mem_range.mpr ?_, ?_⟩
  · exact z.isLt
  · simp

def paths (base goals : List Value) : Nat → List (List Value)
  | 0 => [[]]
  | n+1 => (paths base goals n).flatMap fun xs =>
      (allValues.filter fun z => derivable (saturation (base ++ xs) goals) z).map
        (fun z => xs ++ [z])

theorem extra_path_mem (base goals xs : List Value)
    (hp : ExtraPath base goals xs) : xs ∈ paths base goals xs.length := by
  induction hp with
  | nil => simp [paths]
  | @snoc ys h z ready ih =>
    rw [List.length_append, List.length_singleton]
    simp only [paths, List.mem_flatMap]
    refine ⟨ys,ih,?_⟩
    apply List.mem_map.mpr
    refine ⟨z,List.mem_filter.mpr ⟨mem_allValues z,?_⟩,rfl⟩
    exact ready

theorem catalogued_mem_paths (goals extra : List Value) (k : Nat)
    (hc : Catalogued goals k extra) :
    ∃ xs ∈ paths FreeXor.maskBasis goals k, List.Perm xs extra := by
  obtain ⟨xs,hpath,hperm⟩ := catalogued_extra_path goals extra k hc
  have hlen : xs.length = k := by
    rw [hperm.length_eq]
    exact hc.2.1
  exact ⟨xs,hlen ▸ extra_path_mem _ _ _ hpath,hperm⟩

theorem catalogued_four_lookup (goals extra : List Value) (observed : List Nat)
    (lookup : Nat → Bool) (hc : Catalogued goals 4 extra)
    (ho : observed.Nodup) (hs : observed ⊆ extra.map BitVec.toNat)
    (hfinite : ∀ xs ∈ paths FreeXor.maskBasis goals 4,
      ∀ m < 16, lookup (SharedSearch.encode (SortEncoding.subset
        (SharedSearch.sort (xs.map BitVec.toNat)) m)) = true) :
    lookup (SharedSearch.encode observed) = true := by
  obtain ⟨xs,hmem,hperm⟩ := catalogued_mem_paths goals extra 4 hc
  obtain ⟨m,hm,hkey⟩ := PrefixBridge.observed_catalogued_four goals extra observed hc ho hs
  have hsorted : SharedSearch.sort (xs.map BitVec.toNat) =
      SharedSearch.sort (extra.map BitVec.toNat) :=
    SortEncoding.sort_perm_eq _ _ (hperm.map BitVec.toNat)
  rw [hkey,← hsorted]
  exact hfinite xs hmem m hm

theorem catalogued_three_lookup (goals extra : List Value) (observed : List Nat)
    (lookup : Nat → Bool) (hc : Catalogued goals 3 extra)
    (ho : observed.Nodup) (hs : observed ⊆ extra.map BitVec.toNat)
    (hfinite : ∀ xs ∈ paths FreeXor.maskBasis goals 3,
      ∀ m < 8, lookup (SharedSearch.encode (SortEncoding.subset
        (SharedSearch.sort (xs.map BitVec.toNat)) m)) = true) :
    lookup (SharedSearch.encode observed) = true := by
  obtain ⟨xs,hmem,hperm⟩ := catalogued_mem_paths goals extra 3 hc
  obtain ⟨m,hm,hkey⟩ := PrefixBridge.observed_catalogued_three goals extra observed hc ho hs
  have hsorted : SharedSearch.sort (xs.map BitVec.toNat) =
      SharedSearch.sort (extra.map BitVec.toNat) :=
    SortEncoding.sort_perm_eq _ _ (hperm.map BitVec.toNat)
  rw [hkey,← hsorted]
  exact hfinite xs hmem m hm

end HGP13.GoalSaturation
