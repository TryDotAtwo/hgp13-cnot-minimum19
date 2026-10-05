import Std

/-!
Source obligation: free XOR complexity of F is exactly 10.
We use coordinates (V/H, H) = BitVec 4 x BitVec 3. An arbitrary
program of computed forms may retain and reuse every earlier value.
-/
namespace HGP13.FreeXor

abbrev Form := BitVec 4 × BitVec 3
def add (x y : Form) : Form := (x.1 ^^^ y.1, x.2 ^^^ y.2)
def zero : Form := (0,0)

def basis : List Form := [(1,0),(2,0),(4,0),(9,1),(10,2),(12,4),(8,0)]
def goals : List Form := [(0,1),(0,2),(3,0),(6,0),(0,3),(0,6),(0,4)]

def dot (w z : BitVec 3) : Bool :=
  (w.getLsbD 0 && z.getLsbD 0) ^^
  (w.getLsbD 1 && z.getLsbD 1) ^^
  (w.getLsbD 2 && z.getLsbD 2)

theorem dot_add : ∀ w x y : BitVec 3,
    dot w (x ^^^ y) = (dot w x ^^ dot w y) := by decide

theorem two_constraints : ∀ a b : BitVec 3,
    ∃ w : BitVec 3, w ≠ 0 ∧ dot w a = false ∧ dot w b = false := by decide

/-- A representative's H-component for each quotient class. -/
def rep (q : BitVec 4) : BitVec 3 :=
  if q = 9 then 1 else if q = 10 then 2 else if q = 12 then 4 else 0

def Good (w : BitVec 3) (x : Form) : Prop := x.1 ≠ 0 ∨ dot w x.2 = false
def Coherent (w : BitVec 3) (x : Form) : Prop :=
  x.1 ≠ 0 → dot w x.2 = dot w (rep x.1)

theorem basis_outside : ∀ x ∈ basis, x.1 ≠ 0 := by decide
theorem fixed_representatives : ∀ x ∈ basis ++ goals,
    x.1 ≠ 0 → x.2 = rep x.1 := by decide

theorem bad_target : ∀ w : BitVec 3, w ≠ 0 →
    ∃ x ∈ goals, ¬ Good w x := by unfold Good; decide

theorem bool_xor_false {a b : Bool} (h : (a ^^ b) = false) : a = b := by
  cases a <;> cases b <;> simp_all

theorem separator (x y : Form) : ∃ w : BitVec 3,
    w ≠ 0 ∧ Coherent w x ∧ Coherent w y := by
  obtain ⟨w, hw, hx, hy⟩ := two_constraints (x.2 ^^^ rep x.1) (y.2 ^^^ rep y.1)
  rw [dot_add] at hx hy
  exact ⟨w, hw, fun _ => bool_xor_false hx, fun _ => bool_xor_false hy⟩

theorem good_add {w : BitVec 3} {x y : Form}
    (hx : Good w x) (hy : Good w y)
    (cx : Coherent w x) (cy : Coherent w y) : Good w (add x y) := by
  by_cases hq : x.1 ^^^ y.1 = 0
  · have he : x.1 = y.1 := BitVec.xor_eq_zero_iff.mp hq
    apply Or.inr
    change dot w (x.2 ^^^ y.2) = false
    rw [dot_add]
    by_cases hz : x.1 = 0
    · have hz' : y.1 = 0 := he.symm.trans hz
      have hdx : dot w x.2 = false := hx.resolve_left (by simpa using hz)
      have hdy : dot w y.2 = false := hy.resolve_left (by simpa using hz')
      simp [hdx, hdy]
    · have hz' : y.1 ≠ 0 := by simpa [← he] using hz
      rw [cx hz, cy hz', he]
      simp
  · exact Or.inl hq

def validFrom (available : List Form) : List Form → Bool
  | [] => true
  | z :: p =>
    (available.any fun x => available.any fun y => add x y == z) &&
    validFrom (z :: available) p

theorem invariant {w : BitVec 3} (p available : List Form)
    (hv : validFrom available p = true)
    (hg : ∀ x ∈ available, Good w x)
    (hc : ∀ x ∈ available ++ p, Coherent w x) :
    ∀ x ∈ available ++ p, Good w x := by
  induction p generalizing available with
  | nil => simpa using hg
  | cons z p ih =>
    simp only [validFrom, Bool.and_eq_true] at hv
    obtain ⟨a, ha, hb⟩ := List.any_eq_true.mp hv.1
    obtain ⟨b, hb, hab⟩ := List.any_eq_true.mp hb
    have he : add a b = z := beq_iff_eq.mp hab
    have gz : Good w z := by
      rw [← he]
      exact good_add (hg a ha) (hg b hb)
        (hc a (by simp [ha])) (hc b (by simp [hb]))
    have hga : ∀ x ∈ z :: available, Good w x := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact gz
      · exact hg x hx
    have hca : ∀ x ∈ (z :: available) ++ p, Coherent w x := by
      intro x hx
      apply hc x
      simpa only [List.mem_append, List.mem_cons, or_assoc, or_left_comm, or_comm] using hx
    have out := ih (z :: available) hv.2 hga hca
    intro x hx
    apply out x
    simpa only [List.mem_append, List.mem_cons, or_assoc, or_left_comm, or_comm] using hx

theorem two_extras_impossible (p : List Form) (x y : Form)
    (hv : validFrom basis p = true)
    (allowed : ∀ z ∈ p, z ∈ goals ∨ z = x ∨ z = y)
    (reaches : ∀ z ∈ goals, z ∈ basis ++ p) : False := by
  obtain ⟨w, hw, cx, cy⟩ := separator x y
  have initial : ∀ z ∈ basis, Good w z := by
    intro z hz
    exact Or.inl (basis_outside z hz)
  have coher : ∀ z ∈ basis ++ p, Coherent w z := by
    intro z hz hq
    rcases List.mem_append.mp hz with hz | hz
    · rw [fixed_representatives z (by simp [hz]) hq]
    · rcases allowed z hz with hz | rfl | rfl
      · rw [fixed_representatives z (by simp [hz]) hq]
      · exact cx hq
      · exact cy hq
  obtain ⟨z, hz, bad⟩ := bad_target w hw
  exact bad (invariant p basis hv initial coher z (reaches z hz))

def extraSteps (p : List Form) : List Form := p.filter (fun z => !goals.contains z)

theorem filter_partition (p : List Form) :
    (p.filter goals.contains).length + (extraSteps p).length = p.length := by
  induction p with
  | nil => rfl
  | cons z p ih =>
    cases h : goals.contains z <;>
      simp only [extraSteps, List.filter_cons, h, Bool.not_false, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, List.length_cons] at * <;> omega

theorem two_cover (l : List Form) (h : l.length ≤ 2) :
    ∃ x y : Form, ∀ z ∈ l, z = x ∨ z = y := by
  cases l with
  | nil => exact ⟨zero,zero,by simp⟩
  | cons x l =>
    cases l with
    | nil => exact ⟨x,x,by simp⟩
    | cons y l =>
      cases l with
      | nil => exact ⟨x,y,by simp⟩
      | cons z l => simp only [List.length_cons] at h; omega

theorem goals_nodup : goals.Nodup := by decide
theorem goals_not_basis : ∀ z ∈ goals, z ∉ basis := by decide

/-- Source lower bound: every valid free XOR program computing all seven
    targets, with unrestricted retention/reuse, needs at least ten steps. -/
theorem lower_bound_ten (p : List Form) (hv : validFrom basis p = true)
    (reaches : ∀ z ∈ goals, z ∈ basis ++ p) : 10 ≤ p.length := by
  have sub : goals ⊆ p.filter goals.contains := by
    intro z hz
    apply List.mem_filter.mpr
    constructor
    · rcases List.mem_append.mp (reaches z hz) with hb | hp
      · exact False.elim (goals_not_basis z hz hb)
      · exact hp
    · simpa using hz
  have seven := goals_nodup.length_le_of_subset sub
  change 7 ≤ (p.filter goals.contains).length at seven
  have partition := filter_partition p
  by_cases h : 10 ≤ p.length
  · exact h
  · have small : (extraSteps p).length ≤ 2 := by omega
    obtain ⟨x,y,cover⟩ := two_cover (extraSteps p) small
    have allowed : ∀ z ∈ p, z ∈ goals ∨ z = x ∨ z = y := by
      intro z hz
      by_cases hg : z ∈ goals
      · exact Or.inl hg
      · apply Or.inr
        exact cover z (by simp [extraSteps, hz, hg])
    exact False.elim (two_extras_impossible p x y hv allowed reaches)

def witnessTen : List Form :=
  [(8,1),(8,2),(8,4),(0,1),(0,2),(0,4),(3,0),(6,0),(0,3),(0,6)]

theorem witness_ten_valid : validFrom basis witnessTen = true := by decide
theorem witness_ten_reaches : ∀ z ∈ goals, z ∈ basis ++ witnessTen := by decide
theorem witness_ten_length : witnessTen.length = 10 := by decide

theorem exact_free_minimum_ten :
    (∃ p : List Form, validFrom basis p = true ∧
      (∀ z ∈ goals, z ∈ basis ++ p) ∧ p.length = 10) ∧
    (∀ p : List Form, validFrom basis p = true →
      (∀ z ∈ goals, z ∈ basis ++ p) → 10 ≤ p.length) :=
  ⟨⟨witnessTen,witness_ten_valid,witness_ten_reaches,witness_ten_length⟩,lower_bound_ten⟩

theorem xor_shuffle {n : Nat} (a b c d : BitVec n) :
    (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  calc
    (a ^^^ b) ^^^ (c ^^^ d) = a ^^^ ((b ^^^ c) ^^^ d) := by
      simp only [BitVec.xor_assoc]
    _ = a ^^^ ((c ^^^ b) ^^^ d) := by rw [BitVec.xor_comm b c]
    _ = (a ^^^ c) ^^^ (b ^^^ d) := by simp only [BitVec.xor_assoc]

theorem add_shuffle (a b c d : Form) :
    add (add a b) (add c d) = add (add a c) (add b d) := by
  apply Prod.ext <;> exact xor_shuffle _ _ _ _

theorem choose_xor (v : Form) (a b : Bool) :
    (if a ^^ b then v else zero) =
      add (if a then v else zero) (if b then v else zero) := by
  cases v
  cases a <;> cases b <;> simp [add, zero]

def encodeAux : Nat → BitVec 7 → Form
  | 0, _ => zero
  | k+1, x => add (if x.getLsbD k then basis[k]! else zero) (encodeAux k x)

def encode (x : BitVec 7) : Form := encodeAux 7 x

theorem encodeAux_add (n : Nat) (x y : BitVec 7) :
    encodeAux n (x ^^^ y) = add (encodeAux n x) (encodeAux n y) := by
  induction n with
  | zero => simp [encodeAux, add, zero]
  | succ k ih =>
    simp only [encodeAux, BitVec.getLsbD_xor, choose_xor, ih]
    exact add_shuffle _ _ _ _

theorem encode_add (x y : BitVec 7) :
    encode (x ^^^ y) = add (encode x) (encode y) := encodeAux_add 7 x y

def maskBasis : List (BitVec 7) := [1,2,4,8,16,32,64]
def maskGoals : List (BitVec 7) := [73,82,3,6,27,54,100]

theorem encode_basis : maskBasis.map encode = basis := by decide
theorem encode_goals : maskGoals.map encode = goals := by decide

def validMasks (available : List (BitVec 7)) : List (BitVec 7) → Bool
  | [] => true
  | z :: p =>
    (available.any fun x => available.any fun y => (x ^^^ y) == z) &&
    validMasks (z :: available) p

theorem encode_valid (p available : List (BitVec 7))
    (h : validMasks available p = true) :
    validFrom (available.map encode) (p.map encode) = true := by
  induction p generalizing available with
  | nil => rfl
  | cons z p ih =>
    simp only [validMasks, Bool.and_eq_true] at h
    simp only [List.map_cons, validFrom, Bool.and_eq_true]
    constructor
    · obtain ⟨x,hx,hy⟩ := List.any_eq_true.mp h.1
      obtain ⟨y,hy,he⟩ := List.any_eq_true.mp hy
      apply List.any_eq_true.mpr
      refine ⟨encode x, List.mem_map.mpr ⟨x,hx,rfl⟩, ?_⟩
      apply List.any_eq_true.mpr
      refine ⟨encode y, List.mem_map.mpr ⟨y,hy,rfl⟩, ?_⟩
      apply beq_iff_eq.mpr
      rw [← encode_add, beq_iff_eq.mp he]
    · exact ih (z :: available) h.2

/-- The lower bound stated on the ORIGINAL seven-bit masks from the paper. -/
theorem original_masks_lower_bound_ten (p : List (BitVec 7))
    (hv : validMasks maskBasis p = true)
    (reaches : ∀ z ∈ maskGoals, z ∈ maskBasis ++ p) : 10 ≤ p.length := by
  have valid := encode_valid p maskBasis hv
  rw [encode_basis] at valid
  have hit : ∀ z ∈ goals, z ∈ basis ++ p.map encode := by
    intro z hz
    rw [← encode_goals] at hz
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hz
    rw [← encode_basis, ← List.map_append]
    exact List.mem_map.mpr ⟨r,reaches r hr,rfl⟩
  have bound := lower_bound_ten (p.map encode) valid hit
  simpa using bound

def maskWitnessTen : List (BitVec 7) := [9,18,36,73,82,100,3,6,27,54]
theorem mask_witness_valid : validMasks maskBasis maskWitnessTen = true := by decide
theorem mask_witness_reaches : ∀ z ∈ maskGoals, z ∈ maskBasis ++ maskWitnessTen := by decide
theorem mask_witness_length : maskWitnessTen.length = 10 := by decide

/-- Full formal counterpart of source Lemma 3.2, including attainability. -/
theorem original_masks_exact_minimum_ten :
    (∃ p : List (BitVec 7), validMasks maskBasis p = true ∧
      (∀ z ∈ maskGoals, z ∈ maskBasis ++ p) ∧ p.length = 10) ∧
    (∀ p : List (BitVec 7), validMasks maskBasis p = true →
      (∀ z ∈ maskGoals, z ∈ maskBasis ++ p) → 10 ≤ p.length) :=
  ⟨⟨maskWitnessTen,mask_witness_valid,mask_witness_reaches,mask_witness_length⟩,
    original_masks_lower_bound_ten⟩

theorem zero_good (w : BitVec 3) : Good w zero := by
  apply Or.inr
  simp [dot, zero]

/-- Stronger obstruction used for projected CNOT histories: zero is free,
    and any old basis/target value may be computed repeatedly. -/
theorem two_distinct_extras_impossible (p : List Form) (x y : Form)
    (hv : validFrom (zero :: basis) p = true)
    (allowed : ∀ z ∈ p, z ∈ basis ++ goals ∨ z = zero ∨ z = x ∨ z = y)
    (reaches : ∀ z ∈ goals, z ∈ (zero :: basis) ++ p) : False := by
  obtain ⟨w, hw, cx, cy⟩ := separator x y
  have initial : ∀ z ∈ zero :: basis, Good w z := by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact zero_good w
    · exact Or.inl (basis_outside z hz)
  have coher : ∀ z ∈ (zero :: basis) ++ p, Coherent w z := by
    intro z hz hq
    rcases List.mem_append.mp hz with hz | hz
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact False.elim (hq rfl)
      · rw [fixed_representatives z (by simp [hz]) hq]
    · rcases allowed z hz with hz | rfl | rfl | rfl
      · rw [fixed_representatives z hz hq]
      · exact False.elim (hq rfl)
      · exact cx hq
      · exact cy hq
  obtain ⟨z,hz,bad⟩ := bad_target w hw
  exact bad (invariant p (zero :: basis) hv initial coher z (reaches z hz))

def maskAuxiliaries (p : List (BitVec 7)) : List (BitVec 7) :=
  (p.filter (fun z => !(0 :: (maskBasis ++ maskGoals)).contains z)).eraseDups

theorem masks_two_cover (l : List (BitVec 7)) (h : l.length ≤ 2) :
    ∃ x y : BitVec 7, ∀ z ∈ l, z = x ∨ z = y := by
  cases l with
  | nil => exact ⟨0,0,by simp⟩
  | cons x l =>
    cases l with
    | nil => exact ⟨x,x,by simp⟩
    | cons y l =>
      cases l with
      | nil => exact ⟨x,y,by simp⟩
      | cons z l => simp only [List.length_cons] at h; omega

theorem encode_zero : encode 0 = zero := by decide

/-- At least three DISTINCT nonzero auxiliary projected forms are needed,
    even with free zero and unlimited repeated computations. -/
theorem original_masks_three_auxiliaries (p : List (BitVec 7))
    (hv : validMasks (0 :: maskBasis) p = true)
    (reaches : ∀ z ∈ maskGoals, z ∈ (0 :: maskBasis) ++ p) :
    3 ≤ (maskAuxiliaries p).length := by
  by_cases h : 3 ≤ (maskAuxiliaries p).length
  · exact h
  · have small : (maskAuxiliaries p).length ≤ 2 := by omega
    obtain ⟨x,y,cover⟩ := masks_two_cover (maskAuxiliaries p) small
    have valid := encode_valid p (0 :: maskBasis) hv
    rw [List.map_cons, encode_zero, encode_basis] at valid
    have hit : ∀ z ∈ goals, z ∈ (zero :: basis) ++ p.map encode := by
      intro z hz
      rw [← encode_goals] at hz
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hz
      have mem : encode r ∈ ((0 :: maskBasis) ++ p).map encode :=
        List.mem_map.mpr ⟨r,reaches r hr,rfl⟩
      rw [List.map_append, List.map_cons, encode_zero, encode_basis] at mem
      exact mem
    have allowed : ∀ z ∈ p.map encode,
        z ∈ basis ++ goals ∨ z = zero ∨ z = encode x ∨ z = encode y := by
      intro z hz
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hz
      by_cases fixed : r ∈ 0 :: (maskBasis ++ maskGoals)
      · rcases List.mem_cons.mp fixed with rfl | hf
        · exact Or.inr (Or.inl encode_zero)
        · apply Or.inl
          have hm : encode r ∈ (maskBasis ++ maskGoals).map encode :=
            List.mem_map.mpr ⟨r,hf,rfl⟩
          simpa [List.map_append, encode_basis, encode_goals] using hm
      · have nf : r ≠ 0 ∧ r ∉ maskBasis ∧ r ∉ maskGoals := by simpa using fixed
        have aux : r ∈ maskAuxiliaries p := by simpa [maskAuxiliaries, hr] using nf
        rcases cover r aux with rfl | rfl
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
    exact False.elim (two_distinct_extras_impossible (p.map encode)
      (encode x) (encode y) valid allowed hit)

end HGP13.FreeXor
