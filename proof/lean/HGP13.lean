import Std

/-!
Fixed, labelled 13-coordinate CNOT semantics. No ancillary coordinates,
input restrictions, output permutations, or zero-cost basis changes.
Only the declarations listed in STATUS.md are claimed as verified.
-/
namespace HGP13

abbrev Wire := Fin 13
abbrev Row := BitVec 13
abbrev Matrix := Wire → Row
abbrev Gate := Wire × Wire
abbrev Program := List Gate

def Legal (p : Program) : Prop := ∀ g ∈ p, g.1 ≠ g.2

def step (x : Matrix) (g : Gate) : Matrix :=
  fun i => if i = g.2 then x i ^^^ x g.1 else x i

def run (x : Matrix) (p : Program) : Matrix := p.foldl step x

def identity : Matrix := fun i => BitVec.ofNat 13 (2 ^ i.val)

def targetRows : List Row :=
  [1, 2, 4, 8, 16, 32, 329, 402, 292, 515, 1030, 2075, 4150]

def target : Matrix := fun i => targetRows[i.val]!

def witness : Program :=
  [(0,9), (1,9), (1,10), (2,10), (2,12), (5,12),
   (3,0), (0,11), (4,1), (1,11), (1,12), (1,7), (0,6),
   (8,7), (8,6), (2,8), (5,8), (4,1), (3,0)]

/-- Coefficients of the full binary linear operator, low bit first. -/
def coefficient (x : Matrix) (i j : Wire) : Bool := (x i).getLsbD j.val

theorem step_coefficient (x : Matrix) (g : Gate) (i j : Wire) :
    coefficient (step x g) i j =
      if i = g.2 then coefficient x i j ^^ coefficient x g.1 j
      else coefficient x i j := by
  simp only [coefficient, step]
  split <;> simp

theorem step_other (x : Matrix) (g : Gate) (i : Wire) (h : i ≠ g.2) :
    step x g i = x i := by simp [step, h]

theorem step_involutive (x : Matrix) (g : Gate) (h : g.1 ≠ g.2) :
    step (step x g) g = x := by
  funext i
  by_cases hi : i = g.2
  · subst i
    simp [step, h, BitVec.xor_assoc]
  · simp [step, hi]

theorem run_nil (x : Matrix) : run x [] = x := rfl

theorem run_cons (x : Matrix) (g : Gate) (p : Program) :
    run x (g :: p) = run (step x g) p := rfl

theorem run_append (x : Matrix) (p q : Program) :
    run x (p ++ q) = run (run x p) q := by
  exact List.foldl_append

theorem legal_tail {g : Gate} {p : Program} (h : Legal (g :: p)) : Legal p := by
  intro a ha
  exact h a (List.mem_cons_of_mem g ha)

theorem run_reverse (p : Program) (h : Legal p) (x : Matrix) :
    run (run x p) p.reverse = x := by
  induction p generalizing x with
  | nil => rfl
  | cons g p ih =>
    have hg : g.1 ≠ g.2 := h g (by simp)
    rw [List.reverse_cons, run_append]
    change run (run (run (step x g) p) p.reverse) [g] = x
    rw [ih (legal_tail h)]
    exact step_involutive x g hg

set_option maxRecDepth 20000 in
theorem witness_legal : Legal witness := by unfold Legal witness; decide

theorem witness_length : witness.length = 19 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem witness_realizes : run identity witness = target := by
  have h : ∀ i : Wire, run identity witness i = target i := by decide
  funext i
  exact h i

theorem target_reversible : run target witness.reverse = identity := by
  rw [← witness_realizes]
  exact run_reverse witness witness_legal identity

def ExactMinimum (m : Matrix) (k : Nat) : Prop :=
  (∃ p : Program, Legal p ∧ p.length = k ∧ run identity p = m) ∧
  (∀ p : Program, Legal p → run identity p = m → k ≤ p.length)

theorem upper_bound_19 :
    ∃ p : Program, Legal p ∧ p.length = 19 ∧ run identity p = target :=
  ⟨witness, witness_legal, witness_length, witness_realizes⟩

/-- This is the outstanding source claim, a proposition, NOT an axiom or theorem. -/
def NoShortProgram : Prop :=
  ∀ p : Program, Legal p → p.length ≤ 18 → run identity p ≠ target

/-- A conditional assembly lemma; its hypothesis remains an open obligation. -/
theorem exact_minimum_of_no_short (h : NoShortProgram) : ExactMinimum target 19 := by
  refine ⟨upper_bound_19, ?_⟩
  intro p hp he
  have hn : ¬ p.length ≤ 18 := fun hl => h p hp hl he
  omega

end HGP13
