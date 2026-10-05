import CanonicalPaths

namespace HGP13.FastCanonicalPaths
open HGP13.CanonicalPaths HGP13.GoalSaturation HGP13.Catalogues

def dedupAdjacent {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | [x] => [x]
  | x :: y :: rest =>
      if x = y then dedupAdjacent (y :: rest)
      else x :: dedupAdjacent (y :: rest)

theorem mem_dedupAdjacent {α : Type} [DecidableEq α] (x : α) (xs : List α) :
    x ∈ dedupAdjacent xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [dedupAdjacent]
  | cons a tail ih =>
    cases tail with
    | nil => simp [dedupAdjacent]
    | cons b rest =>
      by_cases h : a = b
      · subst b
        simp [dedupAdjacent,ih]
      · simp [dedupAdjacent,h,ih]

def key (xs : List Value) : Nat :=
  SharedSearch.encode (xs.map BitVec.toNat)

def fastStates (base goals : List Value) : Nat → List (List Value)
  | 0 => [[]]
  | n+1 => dedupAdjacent <| ((fastStates base goals n).flatMap fun xs =>
      (allValues.filter fun z =>
        z != 0 && !((saturation (base ++ xs) goals).contains z) &&
          derivable (saturation (base ++ xs) goals) z).map
        (fun z => normalize (xs ++ [z]))).mergeSort
          (fun xs ys => key xs ≤ key ys)

theorem mem_fastStates_iff (base goals : List Value) (n : Nat) (xs : List Value) :
    xs ∈ fastStates base goals n ↔ xs ∈ states base goals n := by
  induction n generalizing xs with
  | zero => simp [fastStates,states]
  | succ n ih =>
    simp only [fastStates,states,mem_dedupAdjacent,List.mem_mergeSort,
      List.mem_eraseDups,List.mem_flatMap]
    constructor
    · rintro ⟨ys,hys,hz⟩
      exact ⟨ys,(ih ys).mp hys,hz⟩
    · rintro ⟨ys,hys,hz⟩
      exact ⟨ys,(ih ys).mpr hys,hz⟩

theorem catalogued_mem_fastStates (goals extra : List Value) (k : Nat)
    (hc : Catalogued goals k extra) :
    normalize extra ∈ fastStates FreeXor.maskBasis goals k :=
  (mem_fastStates_iff _ _ _ _).mpr (catalogued_mem_states goals extra k hc)

theorem catalogued_four_lookup (goals extra : List Value) (observed : List Nat)
    (lookup : Nat → Bool) (hc : Catalogued goals 4 extra)
    (ho : observed.Nodup) (hs : observed ⊆ extra.map BitVec.toNat)
    (hfinite : ∀ xs ∈ fastStates FreeXor.maskBasis goals 4,
      accepts FreeXor.maskBasis (goals ++ xs) = true →
      ∀ m < 16, lookup (SharedSearch.encode (SortEncoding.subset
        (SharedSearch.sort (xs.map BitVec.toNat)) m)) = true) :
    lookup (SharedSearch.encode observed) = true := by
  have hmem := catalogued_mem_fastStates goals extra 4 hc
  have hacc := (PrefixBridge.catalogued_perm goals extra (normalize extra) 4
    (normalize_perm extra).symm hc).2.2.2
  obtain ⟨m,hm,hkey⟩ := PrefixBridge.observed_catalogued_four goals extra observed hc ho hs
  have hsorted : SharedSearch.sort ((normalize extra).map BitVec.toNat) =
      SharedSearch.sort (extra.map BitVec.toNat) :=
    SortEncoding.sort_perm_eq _ _ ((normalize_perm extra).map BitVec.toNat)
  rw [hkey,← hsorted]
  exact hfinite (normalize extra) hmem hacc m hm

theorem catalogued_three_lookup (goals extra : List Value) (observed : List Nat)
    (lookup : Nat → Bool) (hc : Catalogued goals 3 extra)
    (ho : observed.Nodup) (hs : observed ⊆ extra.map BitVec.toNat)
    (hfinite : ∀ xs ∈ fastStates FreeXor.maskBasis goals 3,
      accepts FreeXor.maskBasis (goals ++ xs) = true →
      ∀ m < 8, lookup (SharedSearch.encode (SortEncoding.subset
        (SharedSearch.sort (xs.map BitVec.toNat)) m)) = true) :
    lookup (SharedSearch.encode observed) = true := by
  have hmem := catalogued_mem_fastStates goals extra 3 hc
  have hacc := (PrefixBridge.catalogued_perm goals extra (normalize extra) 3
    (normalize_perm extra).symm hc).2.2.2
  obtain ⟨m,hm,hkey⟩ := PrefixBridge.observed_catalogued_three goals extra observed hc ho hs
  have hsorted : SharedSearch.sort ((normalize extra).map BitVec.toNat) =
      SharedSearch.sort (extra.map BitVec.toNat) :=
    SortEncoding.sort_perm_eq _ _ ((normalize_perm extra).map BitVec.toNat)
  rw [hkey,← hsorted]
  exact hfinite (normalize extra) hmem hacc m hm

def checkFour (goals : List Value) (lookup : Nat → Bool) : Bool :=
  (fastStates FreeXor.maskBasis goals 4).all fun xs =>
    if accepts FreeXor.maskBasis (goals ++ xs) then
      (List.range 16).all fun m =>
        lookup (SharedSearch.encode (SortEncoding.subset
          (SharedSearch.sort (xs.map BitVec.toNat)) m))
    else true

def checkThree (goals : List Value) (lookup : Nat → Bool) : Bool :=
  (fastStates FreeXor.maskBasis goals 3).all fun xs =>
    if accepts FreeXor.maskBasis (goals ++ xs) then
      (List.range 8).all fun m =>
        lookup (SharedSearch.encode (SortEncoding.subset
          (SharedSearch.sort (xs.map BitVec.toNat)) m))
    else true

theorem checkFour_implies_lookup (goals extra : List Value)
    (observed : List Nat) (lookup : Nat → Bool)
    (hc : Catalogued goals 4 extra) (ho : observed.Nodup)
    (hs : observed ⊆ extra.map BitVec.toNat)
    (hcheck : checkFour goals lookup = true) :
    lookup (SharedSearch.encode observed) = true := by
  apply catalogued_four_lookup goals extra observed lookup hc ho hs
  intro xs hxs hacc m hm
  have hx := List.all_eq_true.mp hcheck xs hxs
  simp [hacc] at hx
  exact hx m hm

theorem checkThree_implies_lookup (goals extra : List Value)
    (observed : List Nat) (lookup : Nat → Bool)
    (hc : Catalogued goals 3 extra) (ho : observed.Nodup)
    (hs : observed ⊆ extra.map BitVec.toNat)
    (hcheck : checkThree goals lookup = true) :
    lookup (SharedSearch.encode observed) = true := by
  apply catalogued_three_lookup goals extra observed lookup hc ho hs
  intro xs hxs hacc m hm
  have hx := List.all_eq_true.mp hcheck xs hxs
  simp [hacc] at hx
  exact hx m hm

end HGP13.FastCanonicalPaths
