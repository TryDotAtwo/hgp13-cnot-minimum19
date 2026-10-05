import SharedSearch
import Init.Data.List.Perm

namespace HGP13.SortEncoding
open HGP13.SharedSearch

theorem mem_insert (x y : Nat) (xs : List Nat) :
    y ∈ SharedSearch.insert x xs ↔ y = x ∨ y ∈ xs := by
  induction xs with
  | nil => simp [SharedSearch.insert]
  | cons a r ih =>
    by_cases h : x ≤ a
    · simp [SharedSearch.insert,h]
    · simp [SharedSearch.insert,h,ih,or_left_comm]

theorem insert_perm (x : Nat) (xs : List Nat) : List.Perm (SharedSearch.insert x xs) (x :: xs) := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons a r ih =>
    by_cases h : x ≤ a
    · simp [SharedSearch.insert,h]
    · simpa [SharedSearch.insert,h] using (ih.cons a).trans (List.Perm.swap x a r)

theorem sort_perm (xs : List Nat) : List.Perm (sort xs) xs := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons a r ih =>
    exact (insert_perm a (sort r)).trans (ih.cons a)

theorem insert_pairwise (x : Nat) (xs : List Nat)
    (hs : xs.Pairwise (· ≤ ·)) : (SharedSearch.insert x xs).Pairwise (· ≤ ·) := by
  induction xs with
  | nil => simp [SharedSearch.insert]
  | cons a r ih =>
    obtain ⟨ha,hr⟩ := List.pairwise_cons.mp hs
    by_cases h : x ≤ a
    · simp only [SharedSearch.insert,h,ite_true,List.pairwise_cons]
      constructor
      · intro y hy
        rcases List.mem_cons.mp hy with he | hm
        · subst y; exact h
        · exact Nat.le_trans h (ha y hm)
      · exact ⟨ha,hr⟩
    · simp only [SharedSearch.insert,h,ite_false,List.pairwise_cons]
      constructor
      · intro y hy
        rcases (mem_insert x y r).mp hy with he | hm
        · subst y; omega
        · exact ha y hm
      · exact ih hr

theorem sort_pairwise (xs : List Nat) : (sort xs).Pairwise (· ≤ ·) := by
  induction xs with
  | nil => simp [sort]
  | cons a r ih => exact insert_pairwise a (sort r) ih

theorem sort_perm_eq (xs ys : List Nat) (hp : List.Perm xs ys) : sort xs = sort ys := by
  apply List.Perm.eq_of_pairwise (le := (· ≤ ·)) ?_ (sort_pairwise xs) (sort_pairwise ys)
    ((sort_perm xs).trans (hp.trans (sort_perm ys).symm))
  intro a b _ _ hab hba
  omega

theorem encode_perm (xs ys : List Nat) (hp : List.Perm xs ys) : encode xs = encode ys := by
  unfold encode
  rw [sort_perm_eq xs ys hp]

theorem nodup_perm_of_mem (xs ys : List Nat) (hx : xs.Nodup) (hy : ys.Nodup)
    (hm : ∀ z, z ∈ xs ↔ z ∈ ys) : List.Perm xs ys := by
  apply List.perm_iff_count.mpr
  intro z
  rw [hx.count,hy.count]
  by_cases h : z ∈ xs
  · have hyz : z ∈ ys := (hm z).mp h
    simp [h,hyz]
  · have hyz : z ∉ ys := fun hyz => h ((hm z).mpr hyz)
    simp [h,hyz]

theorem observed_filter_perm (observed full : List Nat) (ho : observed.Nodup)
    (hf : full.Nodup) (hs : observed ⊆ full) :
    List.Perm observed (full.filter fun z => observed.contains z) := by
  apply nodup_perm_of_mem observed _ ho (List.Pairwise.filter _ hf)
  intro z
  simp only [List.mem_filter,List.contains_iff_mem]
  constructor
  · intro hz
    exact ⟨hs hz,hz⟩
  · exact And.right

theorem observed_filter_encode (observed full : List Nat) (ho : observed.Nodup)
    (hf : full.Nodup) (hs : observed ⊆ full) :
    encode observed = encode (full.filter fun z => observed.contains z) :=
  encode_perm observed _ (observed_filter_perm observed full ho hf hs)

def subset (xs : List Nat) (m : Nat) : List Nat :=
  (xs.zipIdx.filter fun (_, i) => m.testBit i).map Prod.fst

theorem filter_three_mask (a b c : Nat) (f : Nat → Bool) :
    ∃ m : Nat, m < 8 ∧ [a,b,c].filter f = subset [a,b,c] m := by
  let m := (if f a then 1 else 0) + (if f b then 2 else 0) + (if f c then 4 else 0)
  refine ⟨m,?_,?_⟩
  · cases ha : f a <;> cases hb : f b <;> cases hc : f c <;>
      simp [m,ha,hb,hc]
  · cases ha : f a <;> cases hb : f b <;> cases hc : f c <;>
      simp_all [m,subset,Nat.testBit]

theorem filter_four_mask (a b c d : Nat) (f : Nat → Bool) :
    ∃ m : Nat, m < 16 ∧ [a,b,c,d].filter f = subset [a,b,c,d] m := by
  let m := (if f a then 1 else 0) + (if f b then 2 else 0) +
    (if f c then 4 else 0) + (if f d then 8 else 0)
  refine ⟨m,?_,?_⟩
  · cases ha : f a <;> cases hb : f b <;> cases hc : f c <;>
      cases hd : f d <;> simp [m,ha,hb,hc,hd]
  · cases ha : f a <;> cases hb : f b <;> cases hc : f c <;>
      cases hd : f d <;> simp_all [m,subset,Nat.testBit]

theorem observed_three_mask (observed : List Nat) (a b c : Nat)
    (ho : observed.Nodup) (hf : [a,b,c].Nodup)
    (hs : observed ⊆ [a,b,c]) :
    ∃ m : Nat, m < 8 ∧ encode observed = encode (subset [a,b,c] m) := by
  obtain ⟨m,hm,he⟩ := filter_three_mask a b c (fun z => observed.contains z)
  refine ⟨m,hm,?_⟩
  exact (observed_filter_encode observed [a,b,c] ho hf hs).trans (congrArg encode he)

theorem observed_four_mask (observed : List Nat) (a b c d : Nat)
    (ho : observed.Nodup) (hf : [a,b,c,d].Nodup)
    (hs : observed ⊆ [a,b,c,d]) :
    ∃ m : Nat, m < 16 ∧ encode observed = encode (subset [a,b,c,d] m) := by
  obtain ⟨m,hm,he⟩ := filter_four_mask a b c d (fun z => observed.contains z)
  refine ⟨m,hm,?_⟩
  exact (observed_filter_encode observed [a,b,c,d] ho hf hs).trans (congrArg encode he)

theorem observed_length_three_mask (observed full : List Nat)
    (ho : observed.Nodup) (hf : full.Nodup) (hs : observed ⊆ full)
    (hlen : full.length = 3) :
    ∃ m : Nat, m < 8 ∧ encode observed = encode (subset full m) := by
  cases full with
  | nil => simp at hlen
  | cons a r =>
    cases r with
    | nil => simp at hlen
    | cons b r =>
      cases r with
      | nil => simp at hlen
      | cons c r =>
        cases r with
        | nil => exact observed_three_mask observed a b c ho hf hs
        | cons d r => simp at hlen

theorem observed_length_four_mask (observed full : List Nat)
    (ho : observed.Nodup) (hf : full.Nodup) (hs : observed ⊆ full)
    (hlen : full.length = 4) :
    ∃ m : Nat, m < 16 ∧ encode observed = encode (subset full m) := by
  cases full with
  | nil => simp at hlen
  | cons a r =>
    cases r with
    | nil => simp at hlen
    | cons b r =>
      cases r with
      | nil => simp at hlen
      | cons c r =>
        cases r with
        | nil => simp at hlen
        | cons d r =>
          cases r with
          | nil => exact observed_four_mask observed a b c d ho hf hs
          | cons e r => simp at hlen

theorem observed_sorted_three_mask (observed full : List Nat)
    (ho : observed.Nodup) (hf : full.Nodup) (hs : observed ⊆ full)
    (hlen : full.length = 3) :
    ∃ m : Nat, m < 8 ∧ encode observed = encode (subset (sort full) m) := by
  have hp := sort_perm full
  exact observed_length_three_mask observed (sort full) ho
    (hp.nodup_iff.mpr hf) (fun z hz => hp.mem_iff.mpr (hs hz)) (hp.length_eq.trans hlen)

theorem observed_sorted_four_mask (observed full : List Nat)
    (ho : observed.Nodup) (hf : full.Nodup) (hs : observed ⊆ full)
    (hlen : full.length = 4) :
    ∃ m : Nat, m < 16 ∧ encode observed = encode (subset (sort full) m) := by
  have hp := sort_perm full
  exact observed_length_four_mask observed (sort full) ho
    (hp.nodup_iff.mpr hf) (fun z hz => hp.mem_iff.mpr (hs hz)) (hp.length_eq.trans hlen)

end HGP13.SortEncoding
