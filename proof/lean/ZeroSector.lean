import TransposeTarget

/-! Source Lemma 5.1: the sector u=v=0 requires at least twenty gates.
The argument counts actual gates of the full labelled operator. -/
namespace HGP13.ZeroSector
open Budget

def controls : List Wire := [0,1,2,3,4,5,8]
def destinations : List Wire := [8,6,7,9,10,11,12]
def Alphabet (g : Gate) : Prop :=
  (g.1 ∈ sources ∧ (g.2 = 8 ∨ g.2 ∈ privateOutputs)) ∨
  (g.1 = 8 ∧ g.2 ∈ privateOutputs)
def Simple (p : Program) : Prop := ∀ g ∈ p, Alphabet g

theorem alphabet_characterization : ∀ g : Gate,
    g.1 ≠ g.2 → g.2 ∉ sources → g.1 ∉ privateOutputs → Alphabet g := by
  intro ⟨c,t⟩; revert c t
  unfold Alphabet
  decide
theorem alphabet_control : ∀ g : Gate, Alphabet g → g.1 ∈ controls := by
  intro ⟨c,t⟩; revert c t
  unfold Alphabet
  decide
theorem alphabet_target_not_source : ∀ g : Gate, Alphabet g → g.2 ∉ sources := by
  intro ⟨c,t⟩; revert c t
  unfold Alphabet
  decide
theorem alphabet_center_control : ∀ g : Gate, Alphabet g → g.2 = 8 → g.1 ∈ sources := by
  intro ⟨c,t⟩; revert c t
  unfold Alphabet
  decide
theorem alphabet_control_not_center : ∀ g : Gate,
    Alphabet g → g.1 ≠ 8 → g.1 ∈ sources := by
  intro ⟨c,t⟩; revert c t; unfold Alphabet; decide
theorem control_destination : ∀ g : Gate, Alphabet g → g.2 ∈ controls → g.2 = 8 := by
  intro ⟨c,t⟩; revert c t
  unfold Alphabet
  decide
theorem no_center_self : ¬ Alphabet (8,8) := by unfold Alphabet; decide

theorem simple_of_zero (p : Program) (hp : Legal p)
    (hu : (touchedSources p).length = 0)
    (hv : (TransposeTarget.usedOutputs p).length = 0) : Simple p := by
  intro g hg
  apply alphabet_characterization g (hp g hg)
  · intro hs
    have hm : g.2 ∈ touchedSources p := List.mem_filter.mpr
      ⟨hs,List.contains_iff_mem.mpr (List.mem_map.mpr ⟨g,hg,rfl⟩)⟩
    have hn := List.eq_nil_of_length_eq_zero hu
    rw [hn] at hm
    exact List.not_mem_nil hm
  · intro hs
    have hm : g.1 ∈ TransposeTarget.usedOutputs p := List.mem_filter.mpr
      ⟨hs,List.contains_iff_mem.mpr (List.mem_map.mpr ⟨g,hg,rfl⟩)⟩
    have hn := List.eq_nil_of_length_eq_zero hv
    rw [hn] at hm
    exact List.not_mem_nil hm

def hits (p : Program) (g : Gate) : Nat := (p.filter (fun h => h == g)).length
def odd (n : Nat) : Bool := n % 2 == 1

theorem hits_cons (p : Program) (g h : Gate) :
    hits (h :: p) g = (if h = g then 1 else 0) + hits p g := by
  by_cases he : h = g <;> simp [hits,he,Nat.add_comm]

theorem hits_zero_iff (p : Program) (g : Gate) : hits p g = 0 ↔ g ∉ p := by
  constructor
  · intro h hm
    have hh : g ∈ p.filter (fun a => a == g) := List.mem_filter.mpr ⟨hm,by simp⟩
    have hn := List.eq_nil_of_length_eq_zero h
    rw [hn] at hh
    exact List.not_mem_nil hh
  · intro hm
    apply List.length_eq_zero_iff.mpr
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    have hn : a ≠ g := by intro he; exact hm (he ▸ ha)
    simpa using hn

theorem odd_succ (n : Nat) : odd (n+1) = !odd n := by
  apply Bool.eq_iff_iff.mpr
  simp [odd]
  omega

theorem odd_hits_cons (p : Program) (g h : Gate) :
    odd (hits (h :: p) g) = (decide (h = g) ^^ odd (hits p g)) := by
  rw [hits_cons]
  by_cases he : h = g
  · simp only [he,↓reduceIte,decide_true,Bool.true_xor]
    simpa only [Nat.add_comm] using odd_succ (hits p g)
  · simp [he]

theorem odd_positive (n : Nat) (h : odd n = true) : 1 ≤ n := by
  by_cases hn : n = 0
  · simp [odd,hn] at h
  · omega

theorem even_zero_or_two (n : Nat) (h : odd n = false) : n = 0 ∨ 2 ≤ n := by
  by_cases hn : n = 0
  · exact Or.inl hn
  · apply Or.inr
    by_cases small : 2 ≤ n
    · exact small
    · have he : n = 1 := by omega
      simp [odd,he] at h

theorem run_bit_of_invariant (p : Program) (Inv : Matrix → Prop) (x : Matrix)
    (j k : Wire) (tag : Gate) (hx : Inv x)
    (preserves : ∀ g ∈ p, ∀ m, Inv m → Inv (step m g))
    (one : ∀ g ∈ p, ∀ m, Inv m →
      coefficient (step m g) j k = (coefficient m j k ^^ decide (g = tag))) :
    coefficient (run x p) j k = (coefficient x j k ^^ odd (hits p tag)) := by
  induction p generalizing x with
  | nil => simp [run,hits,odd]
  | cons g p ih =>
    rw [run_cons]
    rw [ih (step x g) (preserves g (by simp) x hx)
      (by intro a ha; exact preserves a (by simp [ha]))
      (by intro a ha; exact one a (by simp [ha]))]
    rw [one g (by simp) x hx,odd_hits_cons,Bool.xor_assoc]

theorem identity_coefficient (i k : Wire) : coefficient identity i k = decide (i = k) := by
  have h := congrFun (congrFun Transposition.coefficient_identity i) k
  exact h

def SourceColumn (k : Wire) (x : Matrix) : Prop :=
  ∀ i ∈ sources, coefficient x i k = decide (i = k)
def ControlColumn (k : Wire) (x : Matrix) : Prop :=
  ∀ i ∈ controls, coefficient x i k = decide (i = k)

theorem source_column_initial (k : Wire) : SourceColumn k identity := by
  intro i hi
  exact identity_coefficient i k
theorem control_column_initial (k : Wire) : ControlColumn k identity := by
  intro i hi
  exact identity_coefficient i k

theorem source_column_step (k : Wire) (x : Matrix) (g : Gate)
    (hx : SourceColumn k x) (hg : Alphabet g) : SourceColumn k (step x g) := by
  intro i hi
  have hn : i ≠ g.2 := by intro he; exact alphabet_target_not_source g hg (he ▸ hi)
  rw [step_coefficient,ite_eq_right hn]
  exact hx i hi

theorem source_only_one (j k : Wire) (x : Matrix) (g : Gate)
    (hx : SourceColumn k x) (hg : g.2 = j → g.1 ∈ sources) :
    coefficient (step x g) j k = (coefficient x j k ^^ decide (g = (k,j))) := by
  rcases g with ⟨c,t⟩
  by_cases ht : t = j
  · subst t
    rw [step_coefficient,ite_eq_left rfl,hx c (hg rfl)]
    simp
  · have hn : j ≠ t := Ne.symm ht
    rw [step_coefficient,ite_eq_right hn]
    simp [ht]

theorem control_one (j k : Wire) (x : Matrix) (g : Gate)
    (hx : ControlColumn k x) (hg : Alphabet g) :
    coefficient (step x g) j k = (coefficient x j k ^^ decide (g = (k,j))) := by
  rcases g with ⟨c,t⟩
  by_cases ht : t = j
  · subst t
    rw [step_coefficient,ite_eq_left rfl,hx c (alphabet_control _ hg)]
    simp
  · rw [step_coefficient,ite_eq_right (Ne.symm ht)]
    simp [ht]

theorem control_column_step (k : Wire) (x : Matrix) (g : Gate)
    (hx : ControlColumn k x) (hg : Alphabet g) (hn : g ≠ (k,8)) :
    ControlColumn k (step x g) := by
  intro i hi
  rw [control_one i k x g hx hg,hx i hi]
  have ne : g ≠ (k,i) := by
    intro he
    have ht : g.2 = i := congrArg Prod.snd he
    have hc : g.2 ∈ controls := ht ▸ hi
    have h8 := control_destination g hg hc
    have hi8 : i = 8 := ht.symm.trans h8
    exact hn (by simpa [hi8] using he)
  simp [ne]

theorem source_only_bit (p : Program) (hp : Simple p) (j k : Wire)
    (hc : ∀ g ∈ p, g.2 = j → g.1 ∈ sources) :
    coefficient (run identity p) j k = (decide (j = k) ^^ odd (hits p (k,j))) := by
  have hh := run_bit_of_invariant p (SourceColumn k) identity j k (k,j)
    (source_column_initial k)
    (by intro g hg x hx; exact source_column_step k x g hx (hp g hg))
    (by intro g hg x hx; exact source_only_one j k x g hx (hc g hg))
  simpa only [identity_coefficient] using hh

theorem unvisited_bit (p : Program) (hp : Simple p) (j k : Wire)
    (hn : hits p (k,8) = 0) :
    coefficient (run identity p) j k = (decide (j = k) ^^ odd (hits p (k,j))) := by
  have absent := (hits_zero_iff p (k,8)).mp hn
  have hh := run_bit_of_invariant p (ControlColumn k) identity j k (k,j)
    (control_column_initial k)
    (by intro g hg x hx; apply control_column_step k x g hx (hp g hg)
        intro he; exact absent (he ▸ hg))
    (by intro g hg x hx; exact control_one j k x g hx (hp g hg))
  simpa only [identity_coefficient] using hh

theorem no_center_self_hits (p : Program) (hp : Simple p) : hits p (8,8) = 0 := by
  apply (hits_zero_iff _ _).mpr
  intro hg
  exact no_center_self (hp _ hg)

theorem direct_only_bit (p : Program) (hp : Simple p) (j k : Wire)
    (hn : hits p (8,j) = 0) :
    coefficient (run identity p) j k = (decide (j = k) ^^ odd (hits p (k,j))) := by
  apply source_only_bit p hp j k
  intro g hg ht
  apply alphabet_control_not_center g (hp g hg)
  intro hc
  have he : g = (8,j) := Prod.ext hc ht
  exact (hits_zero_iff p (8,j)).mp hn (he ▸ hg)

def evenSources : List Wire := [0,1,3,4]
def evenOutputs : List Wire := [9,10,11,12]

theorem even_center_data : ∀ k ∈ evenSources,
    8 ≠ k ∧ coefficient target 8 k = false := by decide
theorem even_output_data : ∀ j ∈ evenOutputs,
    j ≠ 8 ∧ coefficient target j 8 = false := by decide
theorem private_source_distinct : ∀ j ∈ privateOutputs, ∀ k ∈ sources, j ≠ k := by decide

def counter (p : Program) (c t : Wire) : Nat := hits p (c,t)

structure Bounds (c : Wire → Wire → Nat) : Prop where
  centerEven : ∀ k ∈ evenSources, c k 8 = 0 ∨ 2 ≤ c k 8
  centerC : 1 ≤ c 2 8
  centerF : 1 ≤ c 5 8
  tFirst : 1 ≤ c 8 6
  tSecond : 1 ≤ c 8 7
  tEven : ∀ j ∈ evenOutputs, c 8 j = 0 ∨ 2 ≤ c 8 j
  required : ∀ j ∈ privateOutputs, ∀ k ∈ sources,
    coefficient target j k = true → (c k 8 = 0 ∨ c 8 j = 0) → 1 ≤ c k j

theorem actual_bounds (p : Program) (hp : Simple p) (real : run identity p = target) :
    Bounds (counter p) := by
  have center := fun k => source_only_bit p hp 8 k
    (fun g hg => alphabet_center_control g (hp g hg))
  have tbit := fun j => unvisited_bit p hp j 8 (no_center_self_hits p hp)
  constructor
  · intro k hk
    have hh := center k
    rw [real,(even_center_data k hk).2] at hh
    have ne := (even_center_data k hk).1
    simp only [ne,decide_false,Bool.false_xor] at hh
    exact even_zero_or_two _ hh.symm
  · have hh := center 2
    rw [real] at hh
    have bit : coefficient target 8 2 = true := by decide
    have ne : (8 : Wire) ≠ 2 := by decide
    simp only [bit,ne,decide_false,Bool.false_xor] at hh
    exact odd_positive _ hh.symm
  · have hh := center 5
    rw [real] at hh
    have bit : coefficient target 8 5 = true := by decide
    have ne : (8 : Wire) ≠ 5 := by decide
    simp only [bit,ne,decide_false,Bool.false_xor] at hh
    exact odd_positive _ hh.symm
  · have hh := tbit 6
    rw [real] at hh
    have bit : coefficient target 6 8 = true := by decide
    have ne : (6 : Wire) ≠ 8 := by decide
    simp only [bit,ne,decide_false,Bool.false_xor] at hh
    exact odd_positive _ hh.symm
  · have hh := tbit 7
    rw [real] at hh
    have bit : coefficient target 7 8 = true := by decide
    have ne : (7 : Wire) ≠ 8 := by decide
    simp only [bit,ne,decide_false,Bool.false_xor] at hh
    exact odd_positive _ hh.symm
  · intro j hj
    have hh := tbit j
    rw [real,(even_output_data j hj).2] at hh
    have ne := (even_output_data j hj).1
    simp only [ne,decide_false,Bool.false_xor] at hh
    exact even_zero_or_two _ hh.symm
  · intro j hj k hk bit absent
    have hh : coefficient (run identity p) j k =
        (decide (j = k) ^^ odd (hits p (k,j))) := by
      rcases absent with hn | hn
      · exact unvisited_bit p hp j k hn
      · exact direct_only_bit p hp j k hn
    rw [real,bit] at hh
    have ne := private_source_distinct j hj k hk
    simp only [ne,decide_false,Bool.false_xor] at hh
    exact odd_positive _ hh.symm

def visit (c : Wire → Wire → Nat) (k : Wire) : Nat := if c k 8 = 0 then 0 else 1
def visitedAD (c : Wire → Wire → Nat) : Nat := visit c 0 + visit c 3
def visitedBE (c : Wire → Wire → Nat) : Nat := visit c 1 + visit c 4
def rowCost (c : Wire → Wire → Nat) (j : Wire) : Nat :=
  c 0 j + c 1 j + c 2 j + c 3 j + c 4 j + c 5 j + c 8 j

theorem visit_le_one (c : Wire → Wire → Nat) (k : Wire) : visit c k ≤ 1 := by
  unfold visit
  split <;> omega

theorem center_visit (c : Wire → Wire → Nat) (h : Bounds c) (k : Wire)
    (hk : k ∈ evenSources) : 2 * visit c k ≤ c k 8 := by
  have hh := h.centerEven k hk
  unfold visit
  split <;> omega

theorem direct_or_visit (c : Wire → Wire → Nat) (h : Bounds c) (j k : Wire)
    (hj : j ∈ privateOutputs) (hk : k ∈ sources) (bit : coefficient target j k = true) :
    1 ≤ c k j + visit c k := by
  by_cases zero : c k 8 = 0
  · have hh := h.required j hj k hk bit (Or.inl zero)
    simp only [visit,zero,↓reduceIte,Nat.add_zero]
    exact hh
  · simp [visit,zero]

theorem central_cost (c : Wire → Wire → Nat) (h : Bounds c) :
    2 + 2 * (visitedAD c + visitedBE c) ≤ rowCost c 8 := by
  have h0 := center_visit c h 0 (by decide)
  have h1 := center_visit c h 1 (by decide)
  have h3 := center_visit c h 3 (by decide)
  have h4 := center_visit c h 4 (by decide)
  have h2 := h.centerC
  have h5 := h.centerF
  unfold rowCost visitedAD visitedBE
  omega

theorem first_output_cost (c : Wire → Wire → Nat) (h : Bounds c) :
    3 ≤ rowCost c 6 + visitedAD c := by
  have h0 := direct_or_visit c h 6 0 (by decide) (by decide) (by decide)
  have h3 := direct_or_visit c h 6 3 (by decide) (by decide) (by decide)
  have ht := h.tFirst
  unfold rowCost visitedAD
  omega

theorem second_output_cost (c : Wire → Wire → Nat) (h : Bounds c) :
    3 ≤ rowCost c 7 + visitedBE c := by
  have h1 := direct_or_visit c h 7 1 (by decide) (by decide) (by decide)
  have h4 := direct_or_visit c h 7 4 (by decide) (by decide) (by decide)
  have ht := h.tSecond
  unfold rowCost visitedBE
  omega

theorem third_output_cost (c : Wire → Wire → Nat) (h : Bounds c) : 2 ≤ rowCost c 9 := by
  by_cases zero : c 8 9 = 0
  · have h0 := h.required 9 (by decide) 0 (by decide) (by decide) (Or.inr zero)
    have h1 := h.required 9 (by decide) 1 (by decide) (by decide) (Or.inr zero)
    unfold rowCost
    omega
  · have ht := h.tEven 9 (by decide)
    unfold rowCost
    omega

theorem fourth_output_cost (c : Wire → Wire → Nat) (h : Bounds c) : 2 ≤ rowCost c 10 := by
  by_cases zero : c 8 10 = 0
  · have h1 := h.required 10 (by decide) 1 (by decide) (by decide) (Or.inr zero)
    have h2 := h.required 10 (by decide) 2 (by decide) (by decide) (Or.inr zero)
    unfold rowCost
    omega
  · have ht := h.tEven 10 (by decide)
    unfold rowCost
    omega

theorem fifth_output_cost (c : Wire → Wire → Nat) (h : Bounds c) :
    4 ≤ rowCost c 11 ∨ 6 ≤ rowCost c 11 + visitedAD c + visitedBE c := by
  by_cases zero : c 8 11 = 0
  · apply Or.inl
    have h0 := h.required 11 (by decide) 0 (by decide) (by decide) (Or.inr zero)
    have h1 := h.required 11 (by decide) 1 (by decide) (by decide) (Or.inr zero)
    have h3 := h.required 11 (by decide) 3 (by decide) (by decide) (Or.inr zero)
    have h4 := h.required 11 (by decide) 4 (by decide) (by decide) (Or.inr zero)
    unfold rowCost
    omega
  · apply Or.inr
    have ht := h.tEven 11 (by decide)
    have h0 := direct_or_visit c h 11 0 (by decide) (by decide) (by decide)
    have h1 := direct_or_visit c h 11 1 (by decide) (by decide) (by decide)
    have h3 := direct_or_visit c h 11 3 (by decide) (by decide) (by decide)
    have h4 := direct_or_visit c h 11 4 (by decide) (by decide) (by decide)
    unfold rowCost visitedAD visitedBE
    omega

theorem sixth_output_cost (c : Wire → Wire → Nat) (h : Bounds c) :
    4 ≤ rowCost c 12 + visitedBE c := by
  by_cases zero : c 8 12 = 0
  · have h1 := h.required 12 (by decide) 1 (by decide) (by decide) (Or.inr zero)
    have h2 := h.required 12 (by decide) 2 (by decide) (by decide) (Or.inr zero)
    have h4 := h.required 12 (by decide) 4 (by decide) (by decide) (Or.inr zero)
    have h5 := h.required 12 (by decide) 5 (by decide) (by decide) (Or.inr zero)
    unfold rowCost
    omega
  · have ht := h.tEven 12 (by decide)
    have h1 := direct_or_visit c h 12 1 (by decide) (by decide) (by decide)
    have h4 := direct_or_visit c h 12 4 (by decide) (by decide) (by decide)
    unfold rowCost visitedBE
    omega

theorem numeric_lower_bound (c : Wire → Wire → Nat) (h : Bounds c) :
    20 ≤ rowCost c 8 + rowCost c 6 + rowCost c 7 + rowCost c 9 +
      rowCost c 10 + rowCost c 11 + rowCost c 12 := by
  have hc := central_cost c h
  have h1 := first_output_cost c h
  have h2 := second_output_cost c h
  have h3 := third_output_cost c h
  have h4 := fourth_output_cost c h
  have h5 := fifth_output_cost c h
  have h6 := sixth_output_cost c h
  have hu : visitedBE c ≤ 2 := by
    have ha := visit_le_one c 1
    have hb := visit_le_one c 4
    unfold visitedBE
    omega
  omega

def allGates : List Gate := destinations.flatMap (fun t => controls.map (fun c => (c,t)))
def sumHits (gs : List Gate) (p : Program) : Nat := (gs.map (hits p)).sum

theorem hits_split (p : Program) (g h : Gate) : hits (h :: p) g = hits [h] g + hits p g := by
  rw [hits_cons,hits_cons]
  simp [hits]

theorem sum_hits_cons (gs : List Gate) (p : Program) (g : Gate) :
    sumHits gs (g :: p) = sumHits gs p + sumHits gs [g] := by
  induction gs with
  | nil => rfl
  | cons a gs ih =>
    simp only [sumHits,List.map_cons,List.sum_cons] at ih ⊢
    rw [hits_split,ih]
    omega

theorem one_gate_cost : ∀ g : Gate, Alphabet g → sumHits allGates [g] = 1 := by
  intro ⟨c,t⟩; revert c t
  unfold Alphabet
  decide

theorem sum_hits_length (p : Program) (hp : Simple p) : sumHits allGates p = p.length := by
  induction p with
  | nil => rfl
  | cons g p ih =>
    rw [sum_hits_cons,ih (by intro a ha; exact hp a (by simp [ha])),
      one_gate_cost g (hp g (by simp)),List.length_cons]

theorem total_counts (p : Program) : sumHits allGates p =
    rowCost (counter p) 8 + rowCost (counter p) 6 + rowCost (counter p) 7 +
    rowCost (counter p) 9 + rowCost (counter p) 10 + rowCost (counter p) 11 + rowCost (counter p) 12 := by
  simp only [sumHits,allGates,destinations,controls,List.flatMap_cons,List.flatMap_nil,
    List.map_cons,List.map_nil,List.map_append,List.sum_append,List.sum_cons,List.sum_nil,
    rowCost,counter]
  omega

/-- Source Lemma 5.1, for arbitrary legal full-matrix programs. -/
theorem zero_sector_lower_bound (p : Program) (hp : Legal p) (real : run identity p = target)
    (hu : (touchedSources p).length = 0)
    (hv : (TransposeTarget.usedOutputs p).length = 0) : 20 ≤ p.length := by
  have hs := simple_of_zero p hp hu hv
  have hh := numeric_lower_bound (counter p) (actual_bounds p hs real)
  rw [← total_counts p,sum_hits_length p hs] at hh
  exact hh

end HGP13.ZeroSector
