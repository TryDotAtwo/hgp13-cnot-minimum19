import FreeXor

/-! Concrete transpose obligation of source Lemma 3.3. This module does
not assert the general transposition principle. A finite closed-set
certificate excludes two auxiliary values; induction covers arbitrary
program lengths and reuse. -/
namespace HGP13.TransposeFree
open FreeXor

def goals : List (BitVec 7) := [21,62,104,17,50,96,67]
def initial : List (BitVec 7) := 0 :: maskBasis
def allowed (x y : BitVec 7) : List (BitVec 7) := initial ++ goals ++ [x,y]
def base : List (BitVec 7) := initial ++ goals
def hard : List (BitVec 7) := [50,62,67]
def neighbors (z : BitVec 7) : List (BitVec 7) :=
  (base.filter (fun a => a != 0 && a != z)).map (fun a => a ^^^ z)
def possible (x y z : BitVec 7) : Bool :=
  (neighbors z).contains x || (neighbors z).contains y || (x ^^^ y == z)
def potential (x y : BitVec 7) : Bool := hard.all (possible x y)

def hit50 (x : BitVec 7) : Bool := (31153782393984708643800420320546816 : BitVec 128).getLsbD x.toNat
def hit62 (x : BitVec 7) : Bool := (127605887615236335690469656672002379776 : BitVec 128).getLsbD x.toNat
def hit67 (x : BitVec 7) : Bool := (42545681092751596315379877151953125384 : BitVec 128).getLsbD x.toNat
def fastPotential (x y : BitVec 7) : Bool :=
  (hit50 x || hit50 y || x ^^^ y == 50) &&
  (hit62 x || hit62 y || x ^^^ y == 62) &&
  (hit67 x || hit67 y || x ^^^ y == 67)

theorem hit50_correct : ∀ x : BitVec 7, (neighbors 50).contains x = hit50 x := by decide
theorem hit62_correct : ∀ x : BitVec 7, (neighbors 62).contains x = hit62 x := by decide
theorem hit67_correct : ∀ x : BitVec 7, (neighbors 67).contains x = hit67 x := by decide

theorem fastPotential_correct (x y : BitVec 7) : potential x y = fastPotential x y := by
  simp only [potential,hard,List.all_cons,List.all_nil,Bool.and_true,possible,
    hit50_correct,hit62_correct,hit67_correct,fastPotential,Bool.and_assoc]

structure Cut where
  values : List (BitVec 7)
  missing : BitVec 7
  deriving Inhabited

def check (x y : BitVec 7) (c : Cut) : Bool :=
  initial.all c.values.contains &&
  c.values.all (fun a => c.values.all (fun b =>
    !(allowed x y).contains (a ^^^ b) || c.values.contains (a ^^^ b))) &&
  goals.contains c.missing && !c.values.contains c.missing

theorem cut_preserved (p available cut legalValues : List (BitVec 7))
    (hv : validMasks available p = true)
    (start : available ⊆ cut) (bounded : p ⊆ legalValues)
    (closed : ∀ a ∈ cut, ∀ b ∈ cut, a ^^^ b ∈ legalValues → a ^^^ b ∈ cut) :
    available ++ p ⊆ cut := by
  induction p generalizing available with
  | nil => simpa using start
  | cons z p ih =>
    simp only [validMasks, Bool.and_eq_true] at hv
    obtain ⟨a,ha,hb⟩ := List.any_eq_true.mp hv.1
    obtain ⟨b,hb,hab⟩ := List.any_eq_true.mp hb
    have he : a ^^^ b = z := beq_iff_eq.mp hab
    have hz : z ∈ cut := by
      rw [← he]
      exact closed a (start ha) b (start hb) (by rw [he]; exact bounded (by simp))
    have tail := ih (z :: available) hv.2
      (by intro a ha; rcases List.mem_cons.mp ha with rfl | ha; exact hz; exact start ha)
      (by intro a ha; exact bounded (List.mem_cons_of_mem z ha))
    intro a ha
    apply tail
    simpa only [List.mem_append, List.mem_cons, or_assoc, or_left_comm, or_comm] using ha

theorem checked_cut_excludes (x y : BitVec 7) (c : Cut)
    (hc : check x y c = true) (p : List (BitVec 7))
    (hv : validMasks initial p = true) (bounded : p ⊆ allowed x y)
    (reaches : goals ⊆ initial ++ p) : False := by
  simp only [check, Bool.and_eq_true] at hc
  have start : initial ⊆ c.values := by
    intro z hz
    exact List.contains_iff_mem.mp (List.all_eq_true.mp hc.1.1.1 z hz)
  have closed : ∀ a ∈ c.values, ∀ b ∈ c.values,
      a ^^^ b ∈ allowed x y → a ^^^ b ∈ c.values := by
    intro a ha b hb hab
    have hh := List.all_eq_true.mp (List.all_eq_true.mp hc.1.1.2 a ha) b hb
    have hit : (allowed x y).contains (a ^^^ b) = true := List.contains_iff_mem.mpr hab
    rw [hit] at hh
    exact List.contains_iff_mem.mp hh
  have missGoal : c.missing ∈ goals := List.contains_iff_mem.mp hc.1.2
  have hit := cut_preserved p initial c.values (allowed x y) hv start bounded closed
    (reaches missGoal)
  have yes : c.values.contains c.missing = true := List.contains_iff_mem.mpr hit
  rw [yes] at hc
  simp at hc

theorem first_parents (p available : List (BitVec 7)) (z : BitVec 7)
    (hv : validMasks available p = true) (absent : z ∉ available)
    (reached : z ∈ available ++ p) :
    ∃ a ∈ available ++ p, ∃ b ∈ available ++ p,
      a ≠ z ∧ b ≠ z ∧ a ^^^ b = z := by
  induction p generalizing available with
  | nil => exact False.elim (absent (by simpa using reached))
  | cons t p ih =>
    simp only [validMasks, Bool.and_eq_true] at hv
    by_cases ht : t = z
    · obtain ⟨a,ha,hb⟩ := List.any_eq_true.mp hv.1
      obtain ⟨b,hb,hab⟩ := List.any_eq_true.mp hb
      refine ⟨a,by simp [ha],b,by simp [hb],?_,?_,?_⟩
      · intro he; exact absent (he ▸ ha)
      · intro he; exact absent (he ▸ hb)
      · exact (beq_iff_eq.mp hab).trans ht
    · have az : z ∉ t :: available := by
        intro hz
        rcases List.mem_cons.mp hz with he | hz
        · exact ht he.symm
        · exact absent hz
      have rz : z ∈ (t :: available) ++ p := by
        simpa only [List.mem_append, List.mem_cons, or_assoc, or_left_comm, or_comm] using reached
      obtain ⟨a,ha,b,hb,haz,hbz,he⟩ := ih (t :: available) hv.2 az rz
      refine ⟨a,?_,b,?_,haz,hbz,he⟩
      · simpa only [List.mem_append, List.mem_cons, or_assoc, or_left_comm, or_comm] using ha
      · simpa only [List.mem_append, List.mem_cons, or_assoc, or_left_comm, or_comm] using hb

theorem xor_solve (a b z : BitVec 7) (he : a ^^^ b = z) : a = b ^^^ z := by
  rw [← he, BitVec.xor_comm a b, ← BitVec.xor_assoc]
  simp

theorem base_separation : hard.all (fun z => base.all (fun a =>
    if a != 0 && a != z then !base.contains (a ^^^ z) else true)) = true := by decide

theorem hard_not_initial : ∀ z ∈ hard, z ∉ initial := by decide
theorem hard_goals : hard ⊆ goals := by decide

theorem neighbor_of_base (a b z : BitVec 7) (hb : b ∈ base)
    (haz : a ≠ z) (hbz : b ≠ z) (he : a ^^^ b = z) : a ∈ neighbors z := by
  have hb0 : b ≠ 0 := by intro hh; simp [hh] at he; exact haz he
  have hb0' : b ≠ (0#7) := hb0
  apply List.mem_map.mpr
  exact ⟨b,List.mem_filter.mpr ⟨hb,by simp [hb0',hbz]⟩,(xor_solve a b z he).symm⟩

theorem no_base_parents (a b z : BitVec 7) (hz : z ∈ hard)
    (ha : a ∈ base) (hb : b ∈ base) (haz : a ≠ z) (hbz : b ≠ z)
    (he : a ^^^ b = z) : False := by
  have ha0 : a ≠ 0 := by intro hh; simp [hh] at he; exact hbz he
  have ha0' : a ≠ (0#7) := ha0
  have sep := List.all_eq_true.mp (List.all_eq_true.mp base_separation z hz) a ha
  have test : (a != 0 && a != z) = true := by simp [ha0',haz]
  rw [test] at sep
  have hb' : a ^^^ z ∈ base := by
    rw [← xor_solve b a z (by simpa [BitVec.xor_comm] using he)]
    exact hb
  have yes : base.contains (a ^^^ z) = true := List.contains_iff_mem.mpr hb'
  rw [yes] at sep
  simp at sep

theorem potential_required (p : List (BitVec 7)) (x y : BitVec 7)
    (hv : validMasks initial p = true) (bounded : p ⊆ allowed x y)
    (reaches : goals ⊆ initial ++ p) : potential x y = true := by
  apply List.all_eq_true.mpr
  intro z hz
  obtain ⟨a,ha,b,hb,haz,hbz,he⟩ := first_parents p initial z hv
    (hard_not_initial z hz) (reaches (hard_goals hz))
  have mem : ∀ t ∈ initial ++ p, t ∈ base ∨ t = x ∨ t = y := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact Or.inl (List.mem_append_left goals ht)
    · have hh := bounded ht
      simpa [allowed, base, or_assoc] using hh
  rcases mem a ha with ha | rfl | rfl <;> rcases mem b hb with hb | rfl | rfl
  · exact False.elim (no_base_parents a b z hz ha hb haz hbz he)
  · have hn := neighbor_of_base b a z ha hbz haz (by simpa [BitVec.xor_comm] using he)
    simp [possible, hn]
  · have hn := neighbor_of_base b a z ha hbz haz (by simpa [BitVec.xor_comm] using he)
    simp [possible, hn]
  · have hn := neighbor_of_base a b z hb haz hbz he
    simp [possible, hn]
  · have hz0 : z = 0 := by simpa using he.symm
    have hn := hard_not_initial z hz
    exact False.elim (hn (by simp [initial, hz0]))
  · simp [possible, he]
  · have hn := neighbor_of_base a b z hb haz hbz he
    simp [possible, hn]
  · simp [possible, BitVec.xor_comm b a, he]
  · have hz0 : z = 0 := by simpa using he.symm
    exact False.elim (hard_not_initial z hz (by simp [initial,hz0]))

end HGP13.TransposeFree
