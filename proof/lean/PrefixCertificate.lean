import CanonicalPaths

namespace HGP13.PrefixCertificate
open HGP13.Catalogues HGP13.GoalSaturation HGP13.CanonicalPaths

def options (base goals xs : List Value) : List Value :=
  allValues.filter fun z =>
    z != 0 && !((saturation (base ++ xs) goals).contains z) &&
      derivable (saturation (base ++ xs) goals) z

def stepOK (base goals : List Value) (current next : List (List Value)) : Bool :=
  current.all fun xs =>
    (options base goals xs).all fun z => next.contains (normalize (xs ++ [z]))

theorem stepOK_member (base goals : List Value) (current next : List (List Value))
    (h : stepOK base goals current next = true)
    (xs : List Value) (hx : xs ∈ current)
    (z : Value) (hz : z ∈ options base goals xs) :
    normalize (xs ++ [z]) ∈ next := by
  have hxs := List.all_eq_true.mp h xs hx
  exact List.contains_iff_mem.mp (List.all_eq_true.mp hxs z hz)

theorem states_succ_member (base goals : List Value) (n : Nat)
    (ys : List Value) (hy : ys ∈ states base goals (n+1)) :
    ∃ xs ∈ states base goals n, ∃ z ∈ options base goals xs,
      ys = normalize (xs ++ [z]) := by
  change ys ∈ ((states base goals n).flatMap fun xs =>
    (options base goals xs).map (fun z => normalize (xs ++ [z]))).eraseDups at hy
  have hy' := List.mem_eraseDups.mp hy
  obtain ⟨xs,hxs,hy''⟩ := List.mem_flatMap.mp hy'
  obtain ⟨z,hz,heq⟩ := List.mem_map.mp hy''
  exact ⟨xs,hxs,z,hz,heq.symm⟩

theorem states_covered (base goals : List Value)
    (layers : Nat → List (List Value)) (k : Nat)
    (h0 : [] ∈ layers 0)
    (hstep : ∀ n < k, stepOK base goals (layers n) (layers (n+1)) = true) :
    ∀ n ≤ k, states base goals n ⊆ layers n := by
  intro n hn
  induction n with
  | zero =>
    intro xs hx
    simp only [states,List.mem_singleton] at hx
    exact hx ▸ h0
  | succ n ih =>
    intro ys hy
    obtain ⟨xs,hxs,z,hz,heq⟩ := states_succ_member base goals n ys hy
    subst ys
    apply stepOK_member base goals (layers n) (layers (n+1))
    · exact hstep n (by omega)
    · exact ih (by omega) hxs
    · exact hz

def finalThreeOK (goals : List Value) (lookup : Nat → Bool)
    (layer : List (List Value)) : Bool :=
  layer.all fun xs =>
    if accepts FreeXor.maskBasis (goals ++ xs) then
      (List.range 8).all fun m =>
        lookup (SharedSearch.encode (SortEncoding.subset
          (SharedSearch.sort (xs.map BitVec.toNat)) m))
    else true

def finalFourOK (goals : List Value) (lookup : Nat → Bool)
    (layer : List (List Value)) : Bool :=
  layer.all fun xs =>
    if accepts FreeXor.maskBasis (goals ++ xs) then
      (List.range 16).all fun m =>
        lookup (SharedSearch.encode (SortEncoding.subset
          (SharedSearch.sort (xs.map BitVec.toNat)) m))
    else true

structure Cert4 where
  l0 : List (List Value)
  l1 : List (List Value)
  l2 : List (List Value)
  l3 : List (List Value)
  l4 : List (List Value)

def layers (cert : Cert4) : Nat → List (List Value)
  | 0 => cert.l0
  | 1 => cert.l1
  | 2 => cert.l2
  | 3 => cert.l3
  | _ => cert.l4

def verifyFour (goals : List Value) (lookup : Nat → Bool) (cert : Cert4) : Bool :=
  cert.l0.contains [] &&
  stepOK FreeXor.maskBasis goals cert.l0 cert.l1 &&
  stepOK FreeXor.maskBasis goals cert.l1 cert.l2 &&
  stepOK FreeXor.maskBasis goals cert.l2 cert.l3 &&
  stepOK FreeXor.maskBasis goals cert.l3 cert.l4 &&
  finalFourOK goals lookup cert.l4

def verifyThree (goals : List Value) (lookup : Nat → Bool) (cert : Cert4) : Bool :=
  cert.l0.contains [] &&
  stepOK FreeXor.maskBasis goals cert.l0 cert.l1 &&
  stepOK FreeXor.maskBasis goals cert.l1 cert.l2 &&
  stepOK FreeXor.maskBasis goals cert.l2 cert.l3 &&
  finalThreeOK goals lookup cert.l3

theorem verifyFour_lookup (goals extra : List Value) (observed : List Nat)
    (lookup : Nat → Bool) (cert : Cert4)
    (hc : Catalogued goals 4 extra) (ho : observed.Nodup)
    (hs : observed ⊆ extra.map BitVec.toNat)
    (hv : verifyFour goals lookup cert = true) :
    lookup (SharedSearch.encode observed) = true := by
  simp only [verifyFour,Bool.and_eq_true] at hv
  obtain ⟨⟨⟨⟨⟨h0,h01⟩,h12⟩,h23⟩,h34⟩,hf⟩ := hv
  have h0' : [] ∈ layers cert 0 := List.contains_iff_mem.mp h0
  have hsteps : ∀ n < 4,
      stepOK FreeXor.maskBasis goals (layers cert n) (layers cert (n+1)) = true := by
    intro n hn
    cases n with
    | zero => exact h01
    | succ n =>
      cases n with
      | zero => exact h12
      | succ n =>
        cases n with
        | zero => exact h23
        | succ n =>
          cases n with
          | zero => exact h34
          | succ n => omega
  have hmem : normalize extra ∈ cert.l4 := by
    exact (states_covered FreeXor.maskBasis goals (layers cert) 4 h0' hsteps
      4 (Nat.le_refl 4)) (catalogued_mem_states goals extra 4 hc)
  have hacc := (PrefixBridge.catalogued_perm goals extra (normalize extra) 4
    (normalize_perm extra).symm hc).2.2.2
  have hfinal := List.all_eq_true.mp hf (normalize extra) hmem
  simp [hacc] at hfinal
  obtain ⟨m,hm,hkey⟩ := PrefixBridge.observed_catalogued_four goals extra observed hc ho hs
  have hsorted : SharedSearch.sort ((normalize extra).map BitVec.toNat) =
      SharedSearch.sort (extra.map BitVec.toNat) :=
    SortEncoding.sort_perm_eq _ _ ((normalize_perm extra).map BitVec.toNat)
  rw [hkey,← hsorted]
  exact hfinal m hm

theorem verifyThree_lookup (goals extra : List Value) (observed : List Nat)
    (lookup : Nat → Bool) (cert : Cert4)
    (hc : Catalogued goals 3 extra) (ho : observed.Nodup)
    (hs : observed ⊆ extra.map BitVec.toNat)
    (hv : verifyThree goals lookup cert = true) :
    lookup (SharedSearch.encode observed) = true := by
  simp only [verifyThree,Bool.and_eq_true] at hv
  obtain ⟨⟨⟨⟨h0,h01⟩,h12⟩,h23⟩,hf⟩ := hv
  have h0' : [] ∈ layers cert 0 := List.contains_iff_mem.mp h0
  have hsteps : ∀ n < 3,
      stepOK FreeXor.maskBasis goals (layers cert n) (layers cert (n+1)) = true := by
    intro n hn
    cases n with
    | zero => exact h01
    | succ n =>
      cases n with
      | zero => exact h12
      | succ n =>
        cases n with
        | zero => exact h23
        | succ n => omega
  have hmem : normalize extra ∈ cert.l3 := by
    exact (states_covered FreeXor.maskBasis goals (layers cert) 3 h0' hsteps
      3 (Nat.le_refl 3)) (catalogued_mem_states goals extra 3 hc)
  have hacc := (PrefixBridge.catalogued_perm goals extra (normalize extra) 3
    (normalize_perm extra).symm hc).2.2.2
  have hfinal := List.all_eq_true.mp hf (normalize extra) hmem
  simp [hacc] at hfinal
  obtain ⟨m,hm,hkey⟩ := PrefixBridge.observed_catalogued_three goals extra observed hc ho hs
  have hsorted : SharedSearch.sort ((normalize extra).map BitVec.toNat) =
      SharedSearch.sort (extra.map BitVec.toNat) :=
    SortEncoding.sort_perm_eq _ _ ((normalize_perm extra).map BitVec.toNat)
  rw [hkey,← hsorted]
  exact hfinal m hm

end HGP13.PrefixCertificate
