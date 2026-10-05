import KnownControls

namespace HGP13.MandatoryCount
open SharedSearch TransitionChecks CounterBudget PackedRows

def freshReturn (c : Config) (s : State) (g : Nat × Nat) : Bool :=
  returnEvent c s g && !has s.returned g.1

def freshCopy (c : Config) (s : State) (g : Nat × Nat) : Bool :=
  copyEvent c s g && !has s.copied (g.1-c.sources.length-1)

theorem fresh_bit (h v i : Nat) (event : Bool) :
    (has h i || (event && decide (v = i))) =
      (has h i || ((event && !has h v) && decide (v = i))) := by
  by_cases he : v = i
  · subst i
    cases event <;> cases has h v <;> rfl
  · simp [he]

theorem advance_fresh_return (c : Config) (s : State) (g : Nat × Nat) (i : Nat) :
    has (advance c s g).returned i =
      (has s.returned i || (freshReturn c s g && decide (g.1 = i))) := by
  rw [advance_returned,fresh_bit]
  rfl

theorem advance_fresh_copy (c : Config) (s : State) (g : Nat × Nat) (i : Nat) :
    has (advance c s g).copied i =
      (has s.copied i || (freshCopy c s g && decide (g.1-c.sources.length-1 = i))) := by
  rw [advance_copied,fresh_bit]
  rfl

theorem events_length (c : Config) (event : State → (Nat × Nat) → Bool)
    (index : (Nat × Nat) → Nat) (s : State) (p : List (Nat × Nat)) :
    (events c event index s p).length = eventCount c event s p := by
  induction p generalizing s with
  | nil => rfl
  | cons g p ih =>
    simp only [events,eventCount]
    split <;> simp_all <;> omega

theorem mask_count_bound (c : Config) (event : State → (Nat × Nat) → Bool)
    (index : (Nat × Nat) → Nat) (mask : State → Nat)
    (step : ∀ s g i, has (mask (advance c s g)) i =
      (has (mask s) i || (event s g && decide (index g = i))))
    (s : State) (p : List (Nat × Nat)) (bits : List Nat) (distinct : bits.Nodup)
    (before : ∀ i ∈ bits, has (mask s) i = false)
    (after : ∀ i ∈ bits, has (mask (rawRun c s p)) i = true) :
    bits.length ≤ eventCount c event s p := by
  rw [← events_length c event index s p]
  apply distinct.length_le_of_subset
  intro i hi
  have h := (raw_event_mask c event index mask step s p i).mp (after i hi)
  rcases h with h | h
  · rw [before i hi] at h
    contradiction
  · exact h

theorem event_kinds_disjoint (c : Config) (s : State) (g : Nat × Nat) :
    ¬ (freshReturn c s g = true ∧ freshCopy c s g = true) := by
  intro h
  simp only [freshReturn,freshCopy,returnEvent,copyEvent,
    Bool.and_eq_true,decide_eq_true_eq] at h
  have ha := h.1.1.1.1
  have hb := h.2.1.1.1
  omega

theorem mandatory_split (c : Config) (s : State) (p : List (Nat × Nat)) :
    eventCount c (mandatoryEvent c) s p =
      eventCount c (freshReturn c) s p + eventCount c (freshCopy c) s p := by
  induction p generalizing s with
  | nil => rfl
  | cons g p ih =>
    have hd := event_kinds_disjoint c s g
    have he : mandatoryEvent c s g = (freshReturn c s g || freshCopy c s g) := rfl
    simp only [eventCount,ih,he]
    by_cases hr : freshReturn c s g = true
    · have hc : freshCopy c s g = false := Bool.eq_false_iff.mpr (fun h => hd ⟨hr,h⟩)
      simp [hr,hc]; omega
    · have hr' : freshReturn c s g = false := Bool.eq_false_iff.mpr hr
      simp [hr']; omega

theorem mandatory_endpoint_bound (c : Config) (s : State) (p : List (Nat × Nat))
    (returned copied : List Nat) (hr : returned.Nodup) (hc : copied.Nodup)
    (r0 : ∀ i ∈ returned, has s.returned i = false)
    (c0 : ∀ i ∈ copied, has s.copied i = false)
    (r1 : ∀ i ∈ returned, has (rawRun c s p).returned i = true)
    (c1 : ∀ i ∈ copied, has (rawRun c s p).copied i = true) :
    returned.length + copied.length ≤ eventCount c (mandatoryEvent c) s p := by
  have ha := mask_count_bound c (freshReturn c) Prod.fst State.returned
    (advance_fresh_return c) s p returned hr r0 r1
  have hb := mask_count_bound c (freshCopy c) (fun g => g.1-c.sources.length-1) State.copied
    (advance_fresh_copy c) s p copied hc c0 c1
  rw [mandatory_split]
  omega

theorem advance_row_length (c : Config) (s : State) (g : Nat × Nat) :
    (advance c s g).rows.length = s.rows.length := by
  change (s.rows.set g.1 (value c s g)).length = _
  simp

theorem advance_row_read (c : Config) (s : State) (g : Nat × Nat)
    (i : Nat) (hi : i < s.rows.length) :
    (advance c s g).rows[i]! = if g.1 = i then value c s g else s.rows[i]! := by
  change (s.rows.set g.1 (value c s g))[i]! = _
  simp [hi,List.getElem_set]

theorem copy_tracked_step (c : Config) (s : State) (g : Nat × Nat)
    (i : Nat) (hi : i < s.rows.length) (hc : c.sources.length < i)
    (tracked : s.rows[i]! &&& 127 ≠ 0 → has s.copied (i-c.sources.length-1) = true) :
    (advance c s g).rows[i]! &&& 127 ≠ 0 →
      has (advance c s g).copied (i-c.sources.length-1) = true := by
  intro hn
  rw [advance_row_read c s g i hi] at hn
  by_cases ht : g.1 = i
  · by_cases hz : s.rows[i]! &&& 127 = 0
    · have he : copyEvent c s g = true := by
        simp only [if_pos ht] at hn
        simpa only [copyEvent,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,bne_iff_ne,ht] using And.intro (And.intro hc hz) hn
      rw [advance_copied,he]
      simp [ht]
    · rw [advance_copied,tracked hz]
      rfl
  · have he := tracked (by simpa only [if_neg ht] using hn)
    rw [advance_copied,he]
    rfl

theorem copy_tracked_run (c : Config) (s : State) (p : List (Nat × Nat))
    (i : Nat) (hi : i < s.rows.length) (hc : c.sources.length < i)
    (tracked : s.rows[i]! &&& 127 ≠ 0 → has s.copied (i-c.sources.length-1) = true) :
    (rawRun c s p).rows[i]! &&& 127 ≠ 0 →
      has (rawRun c s p).copied (i-c.sources.length-1) = true := by
  induction p generalizing s with
  | nil => exact tracked
  | cons g p ih =>
    apply ih (advance c s g)
    · simpa only [advance_row_length] using hi
    · exact copy_tracked_step c s g i hi hc tracked

theorem copied_of_zero_to_nonzero (c : Config) (s : State) (p : List (Nat × Nat))
    (i : Nat) (hi : i < s.rows.length) (hc : c.sources.length < i)
    (before : s.rows[i]! &&& 127 = 0)
    (after : (rawRun c s p).rows[i]! &&& 127 ≠ 0) :
    has (rawRun c s p).copied (i-c.sources.length-1) = true :=
  copy_tracked_run c s p i hi hc (fun h => False.elim (h before)) after
def CarrierShape (s : SectorCover.Sector) : Prop :=
  let c := ofSector s (fun _ _ => true)
  (initial c).rows.length = count c ∧
    ∀ i : Fin (count c), c.sources.length < i.val →
      (initial c).rows[i.val]! &&& 127 = 0 ∧ (want c)[i.val]! &&& 127 ≠ 0

instance (s : SectorCover.Sector) : Decidable (CarrierShape s) := by
  unfold CarrierShape
  infer_instance

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem carrier_shapes_checked :
    SectorCover.sectors.all (fun s => decide (CarrierShape s)) = true := by decide

theorem carrier_shape (s : SectorCover.Sector) (hs : s ∈ SectorCover.sectors) :
    CarrierShape s :=
  of_decide_eq_true (List.all_eq_true.mp carrier_shapes_checked s hs)

theorem target_forces_copied (sector : SectorCover.Sector)
    (hs : sector ∈ SectorCover.sectors) (lookup : Nat → Nat → Bool)
    (p : List (Nat × Nat))
    (target : (rawRun (ofSector sector lookup) (initial (ofSector sector lookup)) p).rows =
      want (ofSector sector lookup)) (k : Nat)
    (hk : k < (ofSector sector lookup).relays.length) :
    has (rawRun (ofSector sector lookup) (initial (ofSector sector lookup)) p).copied k = true := by
  let c := ofSector sector lookup
  let i := c.sources.length+1+k
  change k < c.relays.length at hk
  have shape : (initial c).rows.length = count c ∧
      ∀ j : Fin (count c), c.sources.length < j.val →
        (initial c).rows[j.val]! &&& 127 = 0 ∧ (want c)[j.val]! &&& 127 ≠ 0 :=
    carrier_shape sector hs
  have hi : i < count c := by change c.sources.length+1+k < c.sources.length+1+c.relays.length; omega
  have hc : c.sources.length < i := by dsimp [i]; omega
  have hb := shape.2 ⟨i,hi⟩ hc
  have hl : i < (initial c).rows.length := by rw [shape.1]; exact hi
  have he : i-c.sources.length-1 = k := by dsimp [i]; omega
  have ha : (rawRun c (initial c) p).rows[i]! &&& 127 ≠ 0 := by rw [target]; exact hb.2
  have result := copied_of_zero_to_nonzero c (initial c) p i hl hc hb.1 ha
  simpa only [he] using result
theorem covered_core_copied (sector : SectorCover.Sector)
    (hs : sector ∈ SectorCover.sectors) (lookup : Nat → Nat → Bool)
    (p : Program) (hc : SectorCover.Compatible sector p) (real : run identity p = HGP13.target) :
    ∃ q : List (CoreRowEncoding.IndexedGate (SectorCoordinates.changing sector)
        (SectorIndexing.fixedWires sector)),
      q.map (CoreRowEncoding.fullGate (SectorCoordinates.changing sector)
        (SectorIndexing.fixedWires sector)) = SectorCoordinates.core sector p ∧
      q.length = (SectorCoordinates.core sector p).length ∧
      ∀ k < sector.carriers.length,
        has (rawRun (ofSector sector lookup) (initial (ofSector sector lookup))
          (q.map CoreRowEncoding.label)).copied k = true := by
  obtain ⟨q,hq,hl,ht⟩ := SectorIndexing.core_raw_target sector hs p hc real lookup
  refine ⟨q,hq,hl,?_⟩
  intro k hk
  apply target_forces_copied sector hs lookup (q.map CoreRowEncoding.label) ht k
  simpa only [ofSector,List.length_map] using hk
end HGP13.MandatoryCount






