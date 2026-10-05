import PackedRows

namespace HGP13.NonzeroRows
open Transposition

theorem zero_column_run (x : Matrix) (p : Program) (j : Wire)
    (h : ∀ i, coefficient x i j = false) :
    ∀ i, coefficient (run x p) i j = false := by
  induction p generalizing x with
  | nil => exact h
  | cons g p ih =>
    apply ih (step x g)
    intro i
    rw [step_coefficient,h i,h g.1]
    split <;> rfl

theorem legal_rows_nonzero (p : Program) (hp : Legal p) (i : Wire) :
    run identity p i ≠ 0 := by
  intro hz
  have hc : ∀ j, coefficient (run identity (dual p)) j i = false := by
    intro j
    rw [full_program_transpose]
    simp [coefficient,hz]
  have hf := zero_column_run (run identity (dual p)) (dual p).reverse i hc i
  rw [run_reverse (dual p) (dual_legal p hp) identity] at hf
  rw [coefficient_identity] at hf
  simp [unit] at hf

theorem step_changes_target (x : Matrix) (g : Gate) (hc : x g.1 ≠ 0) :
    step x g g.2 ≠ x g.2 := by
  intro h
  simp only [step,↓reduceIte] at h
  have he : x g.1 ^^^ x g.2 = (0#13) ^^^ x g.2 := by
    simpa [BitVec.xor_comm] using h
  exact hc ((BitVec.xor_left_inj (x g.2)).mp he)

theorem legal_next_changes (p : Program) (hp : Legal p) (g : Gate) :
    step (run identity p) g g.2 ≠ run identity p g.2 :=
  step_changes_target _ g (legal_rows_nonzero p hp g.1)

theorem legal_step_nonzero (p : Program) (hp : Legal p) (g : Gate) (hg : g.1 ≠ g.2)
    (i : Wire) : step (run identity p) g i ≠ 0 := by
  have hlegal : Legal (p ++ [g]) := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hp a ha
    · have he : a = g := by simpa using ha
      simpa only [he] using hg
  have hn := legal_rows_nonzero (p ++ [g]) hlegal i
  simpa only [run_append,run_cons,run_nil] using hn

theorem packed_row_nonzero {n : Nat} (e : Fin n → Wire) (p : Program)
    (hp : Legal p) (i : Wire)
    (hs : SectorCoordinates.RowSupported e (run identity p i)) :
    (PackedRows.pack e (run identity p i)).toNat ≠ 0 := by
  intro h
  have he : PackedRows.pack e (run identity p i) = 0 := BitVec.eq_of_toNat_eq h
  exact legal_rows_nonzero p hp i ((PackedRows.pack_zero_iff e _ hs).mp he)

theorem packed_next_changes {n : Nat} (e : Fin n → Wire) (p : Program)
    (hp : Legal p) (g : Gate)
    (hs : SectorCoordinates.RowSupported e (run identity p g.2))
    (ht : SectorCoordinates.RowSupported e (step (run identity p) g g.2)) :
    (PackedRows.pack e (step (run identity p) g g.2)).toNat ≠
      (PackedRows.pack e (run identity p g.2)).toNat := by
  intro h
  have he := BitVec.eq_of_toNat_eq h
  exact legal_next_changes p hp g ((PackedRows.pack_faithful e _ _ ht hs).mp he)
end HGP13.NonzeroRows





