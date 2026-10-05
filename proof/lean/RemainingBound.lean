import PassiveCost
import Transposition

namespace HGP13.RemainingBound
open PassiveCost

def wires : List Wire := List.finRange 13

def rows (x : Matrix) : List Row := wires.map x

def different (x z : Matrix) : List Wire := wires.filter (fun i => x i != z i)

def missing (x z : Matrix) : List Row :=
  (((different x z).map (fun i => x i ^^^ z i)).filter
    (fun v => !(rows x ++ rows z).contains v)).eraseDups

theorem wires_nodup : wires.Nodup := by decide

theorem different_nodup (x z : Matrix) : (different x z).Nodup := List.Pairwise.filter _ wires_nodup

theorem different_members (x z : Matrix) (i : Wire) : i ∈ different x z ↔ x i ≠ z i := by
  simp [different,wires]

theorem rows_members (x : Matrix) (w : Row) : w ∈ rows x ↔ ∃ i, x i = w := by
  simp [rows,wires]

theorem missing_members (x z : Matrix) (v : Row) :
    v ∈ missing x z ↔ (∃ i, x i ≠ z i ∧ x i ^^^ z i = v) ∧ v ∉ rows x ∧ v ∉ rows z := by
  simp [missing,different_members]

theorem missing_nodup (x z : Matrix) : (missing x z).Nodup := CountHelpers.eraseDups_nodup _

/-- Only the changed target's old delta and the new row can disappear
from the missing-delta set in one step. -/
theorem missing_step_subset (x z : Matrix) (g : Gate) :
    missing x z ⊆ missing (step x g) z ++ [x g.2 ^^^ z g.2,step x g g.2] := by
  intro v hv
  obtain ⟨⟨i,hi,he⟩,hx,hz⟩ := (missing_members x z v).mp hv
  by_cases hit : i = g.2
  · apply List.mem_append_right
    simp [← he,hit]
  · by_cases hn : v ∈ rows (step x g)
    · obtain ⟨j,hj⟩ := (rows_members (step x g) v).mp hn
      have jt : j = g.2 := by
        by_cases jt : j = g.2
        · exact jt
        · exact False.elim (hx ((rows_members x v).mpr ⟨j,by simpa [step,jt] using hj⟩))
      apply List.mem_append_right
      simp [← hj,jt]
    · apply List.mem_append_left
      apply (missing_members (step x g) z v).mpr
      exact ⟨⟨i,by simpa [step,hit] using hi,by simpa [step,hit] using he⟩,hn,hz⟩

theorem missing_step_bound (x z : Matrix) (g : Gate) :
    (missing x z).length ≤ (missing (step x g) z).length + 2 := by
  have h := (missing_nodup x z).length_le_of_subset (missing_step_subset x z g)
  simpa using h

/-- If the gate fixes its target, neither exceptional value was missing:
the old delta was the control, and the new row belongs to the goal. -/
theorem missing_fix_subset (x z : Matrix) (g : Gate) (fixed : step x g g.2 = z g.2) :
    missing x z ⊆ missing (step x g) z := by
  intro v hv
  have hs := missing_step_subset x z g hv
  rcases List.mem_append.mp hs with hs | hs
  · exact hs
  · have hm := (missing_members x z v).mp hv
    have delta : x g.2 ^^^ z g.2 = x g.1 := by
      rw [← fixed]
      simp only [step,ite_true]
      exact xor_cancel_left _ _
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with he | he
    · exact False.elim (hm.2.1 ((rows_members x v).mpr ⟨g.1,(he.trans delta).symm⟩))
    · exact False.elim (hm.2.2 ((rows_members z v).mpr ⟨g.2,(he.trans fixed).symm⟩))

theorem sum_one_change (xs : List Wire) (j : Wire) (f h : Wire → Nat)
    (nd : xs.Nodup) (mem : j ∈ xs) (same : ∀ i, i ≠ j → f i = h i) :
    (xs.map f).sum + h j = (xs.map h).sum + f j := by
  induction xs with
  | nil => simp at mem
  | cons i xs ih =>
    obtain ⟨ni,nt⟩ := List.nodup_cons.mp nd
    by_cases he : i = j
    · subst i
      have tails : xs.map f = xs.map h := by
        apply List.map_congr_left
        intro i hi
        exact same i (by intro he; subst i; exact ni hi)
      simp only [List.map_cons,List.sum_cons,tails]
      omega
    · have jm : j ∈ xs := (List.mem_cons.mp mem).resolve_left (Ne.symm he)
      have hh := ih nt jm
      simp only [List.map_cons,List.sum_cons,same i he]
      omega

theorem filter_length_indicator (xs : List Wire) (x z : Matrix) :
    (xs.filter (fun i => x i != z i)).length =
      (xs.map (fun i => if x i = z i then 0 else 1)).sum := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    by_cases he : x i = z i <;> simp [he,ih,Nat.add_comm]

theorem different_step_count (x z : Matrix) (g : Gate) :
    (different x z).length + (if step x g g.2 = z g.2 then 0 else 1) =
      (different (step x g) z).length + (if x g.2 = z g.2 then 0 else 1) := by
  unfold different
  rw [filter_length_indicator,filter_length_indicator]
  apply sum_one_change wires g.2 (fun i => if x i = z i then 0 else 1)
    (fun i => if step x g i = z i then 0 else 1) wires_nodup (by simp [wires])
  intro i hi
  simp [step,hi]

/-- Twice the row-distance plus the missing-delta count drops by at most
two per CNOT. No matrix enumeration is involved. -/
theorem potential_step (x z : Matrix) (g : Gate) :
    2 * (different x z).length + (missing x z).length ≤
      2 + 2 * (different (step x g) z).length + (missing (step x g) z).length := by
  have counts := different_step_count x z g
  by_cases fixed : step x g g.2 = z g.2
  · have hm := (missing_nodup x z).length_le_of_subset (missing_fix_subset x z g fixed)
    simp only [fixed,ite_true] at counts
    split at counts <;> omega
  · have hm := missing_step_bound x z g
    simp only [fixed,ite_false] at counts
    split at counts <;> omega

theorem potential_path (p : Program) (x z : Matrix) (h : run x p = z) :
    2 * (different x z).length + (missing x z).length ≤ 2 * p.length := by
  induction p generalizing x with
  | nil =>
    have he : x = z := h
    subst x
    simp [different,missing,wires,List.finRange]
  | cons g p ih =>
    have hs := potential_step x z g
    have ht := ih (step x g) h
    simp only [List.length_cons]
    omega

/-- Source Lemma 10.1 for full 13-coordinate rows. -/
theorem missing_delta_lower_bound (p : Program) (x z : Matrix) (h : run x p = z) :
    (different x z).length + ((missing x z).length + 1) / 2 ≤ p.length := by
  have hp := potential_path p x z h
  omega


theorem zero_column_preserved (p : Program) (x : Matrix) (j : Wire)
    (zero : ∀ i, coefficient x i j = false) : ∀ i, coefficient (run x p) i j = false := by
  induction p generalizing x with
  | nil => exact zero
  | cons g p ih =>
    apply ih (step x g)
    intro i
    rw [step_coefficient]
    simp [zero]

/-- Reachable matrices have no zero rows: a zero row would transpose to a
zero column, preserved even by the inverse word, contradicting identity. -/
theorem reachable_rows_nonzero (p : Program) (legal : Legal p) (j : Wire) : run identity p j ≠ 0 := by
  intro hz
  have col : ∀ i, coefficient (run identity (Transposition.dual p)) i j = false := by
    intro i
    rw [Transposition.full_program_transpose]
    change (run identity p j).getLsbD i.val = false
    rw [hz]
    simp
  have preserved := zero_column_preserved (Transposition.dual p).reverse
    (run identity (Transposition.dual p)) j col
  rw [run_reverse (Transposition.dual p) (Transposition.dual_legal p legal) identity] at preserved
  have impossible := preserved j
  rw [Transposition.coefficient_identity] at impossible
  simp [Transposition.unit] at impossible

def Reachable (x : Matrix) : Prop := ∃ p, Legal p ∧ run identity p = x

def ControlsNonzero (x : Matrix) (p : Program) : Prop :=
  ∀ a g b, p = a ++ g :: b → run x a g.1 ≠ 0

theorem reachable_run (x : Matrix) (p : Program) (hx : Reachable x) (legal : Legal p) :
    Reachable (run x p) := by
  obtain ⟨q,hq,he⟩ := hx
  refine ⟨q ++ p,?_,?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hq g hg
    · exact legal g hg
  · rw [run_append,he]

theorem reachable_controls_nonzero (x : Matrix) (p : Program) (hx : Reachable x) (legal : Legal p) :
    ControlsNonzero x p := by
  intro a g b he
  have ha : Legal a := fun k hk => legal k (by rw [he]; exact List.mem_append_left _ hk)
  obtain ⟨q,hq,hv⟩ := reachable_run x a hx ha
  rw [← hv]
  exact reachable_rows_nonzero q hq g.1

theorem targetCount_positive (p : Program) (j : Wire) (mem : j ∈ p.map Prod.snd) :
    1 ≤ targetCount j p := by
  obtain ⟨g,hg,he⟩ := List.mem_map.mp mem
  have hf : g ∈ p.filter (fun g => g.2 == j) := List.mem_filter.mpr ⟨hg,by simp [he]⟩
  have hp := List.length_pos_of_mem hf
  exact hp

theorem changed_row_count (p : Program) (x : Matrix) (j : Wire) (changed : run x p j ≠ x j) :
    1 ≤ targetCount j p := by
  by_cases hm : j ∈ p.map Prod.snd
  · exact targetCount_positive p j hm
  · exact False.elim (changed (Budget.run_untargeted p x j hm))

theorem restored_touched_twice (p : Program) (x : Matrix) (j : Wire)
    (nonzero : ControlsNonzero x p) (restored : run x p j = x j) (mem : j ∈ p.map Prod.snd) :
    2 ≤ targetCount j p := by
  induction p generalizing x with
  | nil => simp at mem
  | cons g p ih =>
    have tailNZ : ControlsNonzero (step x g) p := by
      intro a k b he
      exact nonzero (g :: a) k b (by simp [he])
    by_cases ht : g.2 = j
    · by_cases hp : j ∈ p.map Prod.snd
      · have positive := targetCount_positive p j hp
        rw [targetCount_cons]
        simp only [ht,ite_true]
        omega
      · have row : step x g j = x j := (Budget.run_untargeted p (step x g) j hp).symm.trans restored
        have eq : x j ^^^ x g.1 = x j := by simpa [step,ht] using row
        have bad : x g.1 = 0 := by simpa using (xor_solve (x j) (x g.1) (x j)).mp eq
        exact False.elim (nonzero [] g p rfl bad)
    · have old : step x g j = x j := step_other x g j (Ne.symm ht)
      have hp : j ∈ p.map Prod.snd := by simpa [Ne.symm ht] using mem
      have bound := ih (step x g) tailNZ (restored.trans old.symm) hp
      rw [targetCount_cons]
      simpa [ht] using bound

theorem sum_twos (js : List Wire) : (js.map (fun _ => (2 : Nat))).sum = 2 * js.length := by
  induction js with
  | nil => rfl
  | cons j js ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih]; omega

/-- Required returns are disjoint from currently incorrect rows, hence
both costs can be added. -/
theorem required_returns_lower_bound (p : Program) (x z : Matrix) (a : List Wire)
    (h : run x p = z) (nonzero : ControlsNonzero x p) (distinct : a.Nodup)
    (required : ∀ i ∈ a, x i = z i ∧ i ∈ p.map Prod.snd) :
    (different x z).length + 2 * a.length ≤ p.length := by
  have nd : (different x z ++ a).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨different_nodup x z,distinct,?_⟩
    intro i hi j hj he
    subst j
    exact (different_members x z i).mp hi (required i hj).1
  have hd := sum_map_le (different x z) (fun _ => 1) (fun i => targetCount i p)
    (by intro i hi; apply changed_row_count p x i; rw [h]; exact Ne.symm ((different_members x z i).mp hi))
  have ha := sum_map_le a (fun _ => 2) (fun i => targetCount i p)
    (by
      intro i hi
      exact restored_touched_twice p x i nonzero
        (by rw [h]; exact (required i hi).1.symm) (required i hi).2)
  rw [sum_ones] at hd
  rw [sum_twos] at ha
  have count := targets_count_total (different x z ++ a) p nd
  have limit := List.length_filter_le (fun g : Gate => (different x z ++ a).contains g.2) p
  simp only [List.map_append,List.sum_append] at count
  omega

def remaining (x z : Matrix) (a : List Wire) : Nat :=
  max ((different x z).length + 2 * a.length)
    ((different x z).length + ((missing x z).length + 1) / 2)

/-- Sound maximum of the two bounds; they are not added together. -/
theorem remaining_lower_bound (p : Program) (x z : Matrix) (a : List Wire)
    (hx : Reachable x) (legal : Legal p) (h : run x p = z) (distinct : a.Nodup)
    (required : ∀ i ∈ a, x i = z i ∧ i ∈ p.map Prod.snd) : remaining x z a ≤ p.length := by
  have first := required_returns_lower_bound p x z a h (reachable_controls_nonzero x p hx legal) distinct required
  have second := missing_delta_lower_bound p x z h
  unfold remaining
  omega

theorem remaining_prune_sound (p : Program) (x z : Matrix) (a : List Wire) (spent budget : Nat)
    (hx : Reachable x) (legal : Legal p) (h : run x p = z) (distinct : a.Nodup)
    (required : ∀ i ∈ a, x i = z i ∧ i ∈ p.map Prod.snd)
    (pruned : budget < spent + remaining x z a) : budget < spent + p.length := by
  have hb := remaining_lower_bound p x z a hx legal h distinct required
  omega


def untouched (chosen : List Wire) (p : Program) : List Wire :=
  chosen.filter (fun i => !(p.map Prod.snd).contains i)

theorem untouched_members (chosen : List Wire) (p : Program) (i : Wire) :
    i ∈ untouched chosen p ↔ i ∈ chosen ∧ i ∉ p.map Prod.snd := by
  simp [untouched]

/-- Actual prefix form: every selected source that has not yet been a
target still needs its first change and final restoration. -/
theorem prefix_remaining_bound (q r : Program) (z : Matrix) (chosen : List Wire)
    (legal : Legal (q ++ r)) (h : run identity (q ++ r) = z) (nd : chosen.Nodup)
    (selected : ∀ i ∈ chosen, z i = identity i ∧ i ∈ (q ++ r).map Prod.snd) :
    remaining (run identity q) z (untouched chosen q) ≤ r.length := by
  have lq : Legal q := fun g hg => legal g (List.mem_append_left _ hg)
  have lr : Legal r := fun g hg => legal g (List.mem_append_right _ hg)
  apply remaining_lower_bound r (run identity q) z (untouched chosen q)
    ⟨q,lq,rfl⟩ lr (by simpa only [run_append] using h) (List.Pairwise.filter _ nd)
  intro i hi
  obtain ⟨hc,hn⟩ := (untouched_members chosen q i).mp hi
  obtain ⟨fixed,touched⟩ := selected i hc
  refine ⟨(Budget.run_untargeted q identity i hn).trans fixed.symm,?_⟩
  simp only [List.map_append,List.mem_append] at touched
  exact touched.resolve_left hn

def coreGoal (keep : Wire → Bool) (z : Matrix) : Matrix :=
  fun i => if keep i then z i else identity i

theorem legal_filter (p : Program) (f : Gate → Bool) (hp : Legal p) : Legal (p.filter f) :=
  fun g hg => hp g (List.mem_filter.mp hg).1

theorem filtered_target_members (p : Program) (keep : Wire → Bool) (i : Wire) (kept : keep i = true)
    (touched : i ∈ p.map Prod.snd) : i ∈ (p.filter (fun g => keep g.2)).map Prod.snd := by
  obtain ⟨g,hg,he⟩ := List.mem_map.mp touched
  exact List.mem_map.mpr ⟨g,List.mem_filter.mpr ⟨hg,by rw [he]; exact kept⟩,he⟩

theorem erased_run_goal (p : Program) (keep : Wire → Bool) (z : Matrix)
    (controls : ∀ g ∈ p, keep g.1 = true) (h : run identity p = z) :
    run identity (p.filter (fun g => keep g.2)) = coreGoal keep z := by
  have agree := erase_passive_preserves_core keep p controls identity identity (fun _ _ => rfl)
  funext i
  cases hi : keep i with
  | true =>
    have hh := agree i hi
    rw [h] at hh
    simpa [coreGoal,hi] using hh.symm
  | false =>
    have untouched : i ∉ (p.filter (fun g => keep g.2)).map Prod.snd := by
      intro hm
      obtain ⟨g,hg,he⟩ := List.mem_map.mp hm
      have ht := (List.mem_filter.mp hg).2
      rw [he,hi] at ht
      contradiction
    simpa [coreGoal,hi] using Budget.run_untargeted (p.filter (fun g => keep g.2)) identity i untouched

/-- The remaining bound applies to the actual erased core suffix. The goal
retains all full kept rows and the unchanged passive basis rows. -/
theorem core_prefix_remaining_bound (q r : Program) (keep : Wire → Bool) (z : Matrix)
    (chosen : List Wire) (legal : Legal (q ++ r)) (h : run identity (q ++ r) = z)
    (controls : ∀ g ∈ q ++ r, keep g.1 = true) (nd : chosen.Nodup)
    (selected : ∀ i ∈ chosen, keep i = true ∧ z i = identity i ∧ i ∈ (q ++ r).map Prod.snd) :
    remaining (run identity (q.filter (fun g => keep g.2))) (coreGoal keep z)
      (untouched chosen (q.filter (fun g => keep g.2))) ≤ (r.filter (fun g => keep g.2)).length := by
  have lh := legal_filter (q ++ r) (fun g => keep g.2) legal
  have goal := erased_run_goal (q ++ r) keep z controls h
  rw [List.filter_append] at lh goal
  apply prefix_remaining_bound _ _ (coreGoal keep z) chosen lh goal nd
  intro i hi
  obtain ⟨hk,hf,ht⟩ := selected i hi
  refine ⟨by simpa [coreGoal,hk] using hf,?_⟩
  have hm := filtered_target_members (q ++ r) keep i hk ht
  simpa only [List.filter_append] using hm

end HGP13.RemainingBound
