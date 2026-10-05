import HGP13

namespace HGP13.Transposition

abbrev BinaryMatrix := Wire → Wire → Bool
def rowStep (m : BinaryMatrix) (g : Gate) : BinaryMatrix :=
  fun i j => if i = g.2 then m i j ^^ m g.1 j else m i j
def columnStep (m : BinaryMatrix) (g : Gate) : BinaryMatrix :=
  fun i j => if j = g.2 then m i j ^^ m i g.1 else m i j
def trans (m : BinaryMatrix) : BinaryMatrix := fun i j => m j i
def unit : BinaryMatrix := fun i j => decide (i = j)
def execute (m : BinaryMatrix) (p : Program) := p.foldl rowStep m
def swap (g : Gate) : Gate := (g.2,g.1)
def dual (p : Program) : Program := (p.map swap).reverse

theorem xor_four : ∀ a b c d : Bool, ((a ^^ b) ^^ (c ^^ d)) = ((a ^^ c) ^^ (b ^^ d)) := by decide

theorem row_column_commute (m : BinaryMatrix) (g h : Gate) :
    rowStep (columnStep m h) g = columnStep (rowStep m g) h := by
  funext i j
  by_cases hi : i = g.2 <;> by_cases hj : j = h.2 <;>
    simp only [rowStep, columnStep, hi, hj, ↓reduceIte]
  exact xor_four _ _ _ _

theorem execute_column (m : BinaryMatrix) (p : Program) (g : Gate) :
    execute (columnStep m g) p = columnStep (execute m p) g := by
  induction p generalizing m with
  | nil => rfl
  | cons h p ih =>
    change execute (rowStep (columnStep m g) h) p = _
    rw [row_column_commute, ih]
    rfl

theorem unit_step (g : Gate) : rowStep unit g = columnStep unit (swap g) := by
  funext i j
  by_cases hi : i = g.2 <;> by_cases hj : j = g.1 <;>
    simp [rowStep, columnStep, unit, swap, hi, hj, eq_comm]

theorem execute_cons (g : Gate) (p : Program) :
    execute unit (g :: p) = columnStep (execute unit p) (swap g) := by
  change execute (rowStep unit g) p = _
  rw [unit_step, execute_column]

theorem trans_column (m : BinaryMatrix) (g : Gate) :
    trans (columnStep m g) = rowStep (trans m) g := rfl

theorem trans_unit : trans unit = unit := by
  funext i j
  simp [trans, unit, eq_comm]

theorem execute_dual (p : Program) : execute unit (dual p) = trans (execute unit p) := by
  induction p with
  | nil => exact trans_unit.symm
  | cons g p ih =>
    simp only [dual, List.map_cons, List.reverse_cons, execute, List.foldl_append]
    change rowStep (execute unit (dual p)) (swap g) = trans (execute unit (g :: p))
    rw [ih, execute_cons, trans_column]

theorem coefficient_run (x : Matrix) (p : Program) :
    coefficient (run x p) = execute (coefficient x) p := by
  induction p generalizing x with
  | nil => rfl
  | cons g p ih =>
    rw [run_cons, ih]
    have hs : coefficient (step x g) = rowStep (coefficient x) g := by
      funext i j
      exact step_coefficient x g i j
    rw [hs]
    rfl

theorem coefficient_identity : coefficient identity = unit := by
  have hh : ∀ i j : Wire, coefficient identity i j = unit i j := by decide
  funext i j
  exact hh i j

theorem full_program_transpose (p : Program) (i j : Wire) :
    coefficient (run identity (dual p)) i j = coefficient (run identity p) j i := by
  rw [coefficient_run, coefficient_run, coefficient_identity, execute_dual]
  rfl

theorem dual_length (p : Program) : (dual p).length = p.length := by simp [dual]

theorem dual_legal (p : Program) (h : Legal p) : Legal (dual p) := by
  intro g hg
  have hg' : g ∈ p.map swap := List.mem_reverse.mp hg
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg'
  exact Ne.symm (h a ha)

/-- Fixed involution interchanging the six source and private-output labels. -/
def perm (i : Wire) : Wire := ([6,7,9,10,11,12,0,1,8,2,3,4,5] : List Wire)[i.val]!
def renameGate (g : Gate) : Gate := (perm g.1,perm g.2)
def rename (p : Program) : Program := p.map renameGate
def relabel (m : BinaryMatrix) : BinaryMatrix := fun i j => m (perm i) (perm j)
def oriented (p : Program) : Program := rename (dual p)

theorem perm_involution : ∀ i : Wire, perm (perm i) = i := by decide
theorem perm_injective {i j : Wire} (h : perm i = perm j) : i = j := by
  have hh := congrArg perm h
  simpa only [perm_involution] using hh
theorem perm_eq (i j : Wire) : perm i = j ↔ i = perm j := by
  constructor
  · intro h; have hh := congrArg perm h; simpa only [perm_involution] using hh
  · intro h; rw [h,perm_involution]

theorem relabel_step (m : BinaryMatrix) (g : Gate) :
    rowStep (relabel m) (renameGate g) = relabel (rowStep m g) := by
  funext i j
  simp only [rowStep,relabel,renameGate,perm_eq,perm_involution]

theorem relabel_unit : relabel unit = unit := by
  funext i j
  simp only [relabel,unit]
  congr 1
  exact propext ⟨perm_injective,congrArg perm⟩

theorem execute_rename (p : Program) (m : BinaryMatrix) :
    execute (relabel m) (rename p) = relabel (execute m p) := by
  induction p generalizing m with
  | nil => rfl
  | cons g p ih =>
    change execute (rowStep (relabel m) (renameGate g)) (rename p) = _
    rw [relabel_step,ih]
    rfl

theorem full_program_oriented (p : Program) (i j : Wire) :
    coefficient (run identity (oriented p)) i j =
      coefficient (run identity p) (perm j) (perm i) := by
  rw [coefficient_run,coefficient_run,coefficient_identity]
  change execute unit (rename (dual p)) i j = _
  rw [← relabel_unit,execute_rename,relabel_unit,execute_dual]
  rfl

theorem oriented_length (p : Program) : (oriented p).length = p.length := by
  simp [oriented,rename,dual]

theorem oriented_legal (p : Program) (h : Legal p) : Legal (oriented p) := by
  intro g hg
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
  intro he
  exact dual_legal p h a ha (perm_injective he)

end HGP13.Transposition
