import MandatoryCount

namespace HGP13.ReturnTracking
open SharedSearch TransitionChecks PackedRows MandatoryCount

def SourceTracked (c : Config) (s : State) (i : Nat) : Prop :=
  (has s.changed i = false → s.rows[i]! = 2^(c.sources[i]!)) ∧
  (has s.changed i = true → s.rows[i]! = 2^(c.sources[i]!) → has s.returned i = true)

theorem changed_bit (c : Config) (s : State) (g : Nat × Nat) (i : Nat)
    (hi : i < c.sources.length) :
    has (advance c s g).changed i = (has s.changed i || decide (g.1 = i)) := by
  change has (if g.1 < c.sources.length then remember s.changed g.1 else s.changed) i = _
  by_cases ht : g.1 = i
  · simp [ht,hi,has_remember]
  · by_cases hg : g.1 < c.sources.length <;> simp [hg,ht,has_remember]

theorem tracked_step (c : Config) (s : State) (g : Nat × Nat) (i : Nat)
    (hi : i < c.sources.length) (hl : i < s.rows.length)
    (effective : value c s g ≠ s.rows[g.1]!) (tracked : SourceTracked c s i) :
    SourceTracked c (advance c s g) i := by
  constructor
  · intro h
    rw [changed_bit c s g i hi] at h
    have ho : has s.changed i = false := by
      cases hb : has s.changed i <;> simp_all
    have hn : g.1 ≠ i := by intro he; simp [he] at h
    rw [advance_row_read c s g i hl,if_neg hn]
    exact tracked.1 ho
  · intro hc hr
    rw [advance_row_read c s g i hl] at hr
    by_cases ht : g.1 = i
    · simp only [if_pos ht] at hr
      by_cases ho : has s.changed i = true
      · have he : returnEvent c s g = true := by
          simpa only [returnEvent,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,ht] using
            And.intro (And.intro hi hr) ho
        rw [advance_returned,he]
        simp [ht]
      · have hz : has s.changed i = false := Bool.eq_false_iff.mpr ho
        have old := tracked.1 hz
        apply False.elim
        apply effective
        simpa only [ht] using hr.trans old.symm
    · have ho : has s.changed i = true := by
        simpa only [changed_bit c s g i hi,ht,decide_false,Bool.or_false] using hc
      have old := tracked.2 ho (by simpa only [if_neg ht] using hr)
      rw [advance_returned,old]
      rfl

def Effective (c : Config) (s : State) : List (Nat × Nat) → Prop
  | [] => True
  | g :: p => value c s g ≠ s.rows[g.1]! ∧ Effective c (advance c s g) p

theorem tracked_run (c : Config) (s : State) (p : List (Nat × Nat)) (i : Nat)
    (hi : i < c.sources.length) (hl : i < s.rows.length)
    (effective : Effective c s p) (tracked : SourceTracked c s i) :
    SourceTracked c (rawRun c s p) i := by
  induction p generalizing s with
  | nil => exact tracked
  | cons g p ih =>
    apply ih (advance c s g)
    · simpa only [advance_row_length] using hl
    · exact effective.2
    · exact tracked_step c s g i hi hl effective.1 tracked

theorem initial_tracked (c : Config) (i : Nat) (hi : i < c.sources.length) :
    SourceTracked c (initial c) i := by
  constructor
  · intro _
    simp [initial,hi,List.getElem?_append]
  · intro h
    simp [initial,has] at h

theorem target_forces_returned (c : Config) (p : List (Nat × Nat)) (i : Nat)
    (hi : i < c.sources.length) (effective : Effective c (initial c) p)
    (hit : ∃ g ∈ p, g.1 = i) (target : (rawRun c (initial c) p).rows = want c) :
    has (rawRun c (initial c) p).returned i = true := by
  have hl : i < (initial c).rows.length := by simp [initial]; omega
  have tracked := tracked_run c (initial c) p i hi hl effective (initial_tracked c i hi)
  have changed : has (rawRun c (initial c) p).changed i = true := by
    apply (raw_changed c (initial c) p i).mpr
    right
    obtain ⟨g,hg,he⟩ := hit
    exact ⟨g,hg,he,hi⟩
  apply tracked.2 changed
  rw [target]
  simp [want,hi,List.getElem?_append]
end HGP13.ReturnTracking


