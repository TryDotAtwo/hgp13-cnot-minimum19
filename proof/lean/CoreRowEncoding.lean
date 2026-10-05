import TransitionChecks

namespace HGP13.CoreRowEncoding
open PackedRows
open SharedSearch TransitionChecks

def rows {n : Nat} (e : Fin n → Wire) (wires : List Wire) (x : Matrix) : List Nat :=
  wires.map (fun w => (pack e (x w)).toNat)

theorem rows_append {n : Nat} (e : Fin n → Wire) (a b : List Wire) (x : Matrix) :
    rows e (a ++ b) x = rows e a x ++ rows e b x := by simp [rows]

theorem rows_get {n : Nat} (e : Fin n → Wire) (wires : List Wire) (x : Matrix)
    (i : Nat) (hi : i < wires.length) :
    (rows e wires x)[i]! = (pack e (x wires[i])).toNat := by
  simp [rows,hi]

theorem rows_step {n : Nat} (e : Fin n → Wire) (wires : List Wire)
    (distinct : wires.Nodup) (x : Matrix) (control : Wire) (t : Fin wires.length) :
    rows e wires (step x (control,wires[t.val])) =
      (rows e wires x).set t.val
        ((pack e (x wires[t.val])).toNat ^^^ (pack e (x control)).toNat) := by
  apply List.ext_getElem
  · simp [rows]
  · intro i hi hj
    have hindex : i < wires.length := by simpa [rows] using hi
    simp only [rows,List.getElem_map,List.getElem_set]
    by_cases he : t.val = i
    · subst i
      simp [step,pack_nat_xor]
    · have hw : wires[i] ≠ wires[t.val] := by
        intro h
        have hi' := (List.Nodup.getElem_inj distinct).mp h
        omega
      simp [step,hw,he]

theorem append_get (a b : List Nat) (i : Nat) :
    (a ++ b)[i]! = if i < a.length then a[i]! else b[i-a.length]! := by
  by_cases h : i < a.length <;>
    simp [List.getElem!_eq_getElem?_getD,List.getElem?_append,h]

theorem control_read {n : Nat} (e : Fin n → Wire) (a b : List Wire) (x : Matrix)
    (c : Config) (s : State) (j : Fin (a.length+b.length))
    (hcount : count c = a.length) (hrows : s.rows = rows e a x)
    (hfixed : fixed c = rows e b x) :
    (if j.val < count c then s.rows[j.val]! else (fixed c)[j.val-count c]!) =
      (pack e (x ((a ++ b)[j.val]'(by simpa using j.isLt)))).toNat := by
  rw [hcount,hrows,hfixed]
  have h := rows_get e (a ++ b) x j.val (by simpa using j.isLt)
  rw [rows_append,append_get] at h
  simpa only [rows,List.length_map] using h

theorem advance_rows {n : Nat} (e : Fin n → Wire) (a b : List Wire)
    (distinct : a.Nodup) (x : Matrix) (c : Config) (s : State)
    (t : Fin a.length) (j : Fin (a.length+b.length))
    (hcount : count c = a.length) (hrows : s.rows = rows e a x)
    (hfixed : fixed c = rows e b x) :
    (advance c s (t.val,j.val)).rows =
      rows e a (step x ((a ++ b)[j.val]'(by simpa using j.isLt),a[t.val])) := by
  change s.rows.set t.val (s.rows[t.val]! ^^^
    (if j.val < count c then s.rows[j.val]! else (fixed c)[j.val-count c]!)) = _
  rw [control_read e a b x c s j hcount hrows hfixed,hrows,rows_get e a x t.val t.isLt]
  exact (rows_step e a distinct x _ t).symm

theorem fixed_rows_step {n : Nat} (e : Fin n → Wire) (a b : List Wire)
    (disjoint : ∀ i ∈ a, ∀ j ∈ b, i ≠ j) (x : Matrix) (control : Wire)
    (t : Fin a.length) :
    rows e b (step x (control,a[t.val])) = rows e b x := by
  unfold rows
  apply List.map_congr_left
  intro j hj
  have hne : j ≠ a[t.val] := Ne.symm (disjoint _ (List.getElem_mem t.isLt) j hj)
  rw [step_other x (control,a[t.val]) j hne]

abbrev IndexedGate (a b : List Wire) := Fin (a.length+b.length) × Fin a.length

def fullGate (a b : List Wire) (g : IndexedGate a b) : Gate :=
  ((a ++ b)[g.1.val]'(by simpa using g.1.isLt),a[g.2.val])

def label {a b : List Wire} (g : IndexedGate a b) : Nat × Nat := (g.2.val,g.1.val)

theorem raw_rows_run {n : Nat} (e : Fin n → Wire) (a b : List Wire)
    (distinct : a.Nodup) (disjoint : ∀ i ∈ a, ∀ j ∈ b, i ≠ j)
    (c : Config) (hcount : count c = a.length)
    (p : List (IndexedGate a b)) (x : Matrix) (s : State)
    (hrows : s.rows = rows e a x) (hfixed : fixed c = rows e b x) :
    (rawRun c s (p.map label)).rows = rows e a (run x (p.map (fullGate a b))) := by
  induction p generalizing x s with
  | nil => simpa [rawRun,run] using hrows
  | cons g p ih =>
    simp only [List.map_cons,rawRun,run_cons]
    apply ih (step x (fullGate a b g)) (advance c s (label g))
    · exact advance_rows e a b distinct x c s g.2 g.1 hcount hrows hfixed
    · simp only [fullGate]
      rw [fixed_rows_step e a b disjoint]
      exact hfixed

theorem advance_history {n : Nat} (e : Fin n → Wire) (a b : List Wire)
    (x : Matrix) (c : Config) (s : State)
    (t : Fin a.length) (j : Fin (a.length+b.length))
    (hcount : count c = a.length) (hrows : s.rows = rows e a x)
    (hfixed : fixed c = rows e b x) :
    (advance c s (t.val,j.val)).history = remember s.history
      (pack e (step x (fullGate a b (j,t)) a[t.val])).toNat := by
  change remember s.history (s.rows[t.val]! ^^^
    (if j.val < count c then s.rows[j.val]! else (fixed c)[j.val-count c]!)) = _
  rw [control_read e a b x c s j hcount hrows hfixed,hrows,rows_get e a x t.val t.isLt]
  simp [fullGate,step,pack_nat_xor]

theorem raw_history_run {n : Nat} (e : Fin n → Wire) (a b : List Wire)
    (distinct : a.Nodup) (disjoint : ∀ i ∈ a, ∀ j ∈ b, i ≠ j)
    (c : Config) (hcount : count c = a.length)
    (p : List (IndexedGate a b)) (x : Matrix) (s : State)
    (hrows : s.rows = rows e a x) (hfixed : fixed c = rows e b x) :
    (rawRun c s (p.map label)).history =
      traceHistory e x (p.map (fullGate a b)) s.history := by
  induction p generalizing x s with
  | nil => rfl
  | cons g p ih =>
    have hr := advance_rows e a b distinct x c s g.2 g.1 hcount hrows hfixed
    have hf : fixed c = rows e b (step x (fullGate a b g)) := by
      simp only [fullGate]
      rw [fixed_rows_step e a b disjoint]
      exact hfixed
    simp only [List.map_cons,rawRun,traceHistory]
    rw [ih (step x (fullGate a b g)) (advance c s (label g)) hr hf]
    simp only [label]
    rw [advance_history e a b x c s g.2 g.1 hcount hrows hfixed]
    rfl

end HGP13.CoreRowEncoding
