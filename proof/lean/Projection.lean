import HGP13
import FreeXor

/-!
Connection between arbitrary full 13-row CNOT histories and the free
seven-bit XOR problem. Private inputs are NOT assumed to be zero.
-/
namespace HGP13.Projection
open HGP13.FreeXor

def projectAux : Nat → Row → BitVec 7
  | 0, _ => 0
  | k+1, x =>
    (if x.getLsbD (if k = 6 then 8 else k) then BitVec.ofNat 7 (2^k) else 0) ^^^
    projectAux k x

/-- Keep coefficients 0..5 and 8 in that order; discard the private bits
    only in the proof's projection, not in the full circuit semantics. -/
def project (x : Row) : BitVec 7 := projectAux 7 x

theorem choose_xor_bits {n : Nat} (v : BitVec n) (a b : Bool) :
    (if a ^^ b then v else 0) =
      (if a then v else 0) ^^^ (if b then v else 0) := by
  cases a <;> cases b <;> simp

theorem projectAux_add (n : Nat) (x y : Row) :
    projectAux n (x ^^^ y) = projectAux n x ^^^ projectAux n y := by
  induction n with
  | zero => simp [projectAux]
  | succ k ih =>
    simp only [projectAux, BitVec.getLsbD_xor, choose_xor_bits, ih]
    exact xor_shuffle _ _ _ _

theorem project_add (x y : Row) : project (x ^^^ y) = project x ^^^ project y :=
  projectAux_add 7 x y

theorem initial_supported : ∀ i : Wire, project (identity i) ∈ 0 :: maskBasis := by decide

def outputWires : List Wire := [6,7,9,10,11,12,8]
theorem target_projection : outputWires.map (fun i => project (target i)) = maskGoals := by decide

def trace (x : Matrix) : Program → List (BitVec 7)
  | [] => []
  | g :: p => project (step x g g.2) :: trace (step x g) p

theorem trace_length (p : Program) (x : Matrix) : (trace x p).length = p.length := by
  induction p generalizing x with
  | nil => rfl
  | cons g p ih => simp [trace, ih]

theorem step_supported (x : Matrix) (g : Gate) (available : List (BitVec 7))
    (h : ∀ i, project (x i) ∈ available) :
    ∀ i, project (step x g i) ∈ project (step x g g.2) :: available := by
  intro i
  by_cases hi : i = g.2
  · subst i; exact List.mem_cons_self
  · apply List.mem_cons_of_mem
    simpa [step, hi] using h i

theorem trace_valid (p : Program) (x : Matrix) (available : List (BitVec 7))
    (h : ∀ i, project (x i) ∈ available) :
    validMasks available (trace x p) = true := by
  induction p generalizing x available with
  | nil => rfl
  | cons g p ih =>
    simp only [trace, validMasks, Bool.and_eq_true]
    constructor
    · apply List.any_eq_true.mpr
      refine ⟨project (x g.2), h g.2, ?_⟩
      apply List.any_eq_true.mpr
      refine ⟨project (x g.1), h g.1, ?_⟩
      apply beq_iff_eq.mpr
      simp [step, project_add]
    · exact ih (step x g) _ (step_supported x g available h)

theorem final_rows_supported (p : Program) (x : Matrix) (available : List (BitVec 7))
    (h : ∀ i, project (x i) ∈ available) :
    ∀ i, project (run x p i) ∈ available ++ trace x p := by
  induction p generalizing x available with
  | nil => simpa [run, trace] using h
  | cons g p ih =>
    have hh := ih (step x g) _ (step_supported x g available h)
    intro i
    have mem := hh i
    simpa only [run_cons, trace, List.mem_append, List.mem_cons,
      or_assoc, or_left_comm, or_comm] using mem

theorem trace_reaches_targets (p : Program) (h : run identity p = target) :
    ∀ z ∈ maskGoals, z ∈ (0 :: maskBasis) ++ trace identity p := by
  intro z hz
  rw [← target_projection] at hz
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz
  rw [← h]
  exact final_rows_supported p identity _ initial_supported i

/-- Source budget lemma's auxiliary-count obligation, for the original
    full matrix and arbitrary full programs, not a restricted sector. -/
theorem every_realization_needs_three_auxiliaries (p : Program)
    (h : run identity p = target) :
    3 ≤ (maskAuxiliaries (trace identity p)).length :=
  original_masks_three_auxiliaries (trace identity p)
    (trace_valid p identity _ initial_supported) (trace_reaches_targets p h)

end HGP13.Projection
