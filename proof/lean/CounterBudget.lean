import SectorIndexing

namespace HGP13.CounterBudget
open SharedSearch TransitionChecks

def eventCount (c : Config) (event : State → (Nat × Nat) → Bool)
    (s : State) : List (Nat × Nat) → Nat
  | [] => 0
  | g :: p => (if event s g then 1 else 0) + eventCount c event (advance c s g) p

def repeatedMandatory (c : Config) (s : State) (g : Nat × Nat) : Bool :=
  repeatEvent c s g && mandatoryEvent c s g

theorem raw_append (c : Config) (s : State) (p q : List (Nat × Nat)) :
    rawRun c s (p ++ q) = rawRun c (rawRun c s p) q := by
  induction p generalizing s with
  | nil => rfl
  | cons g p ih => simpa only [List.cons_append,rawRun] using ih (advance c s g)

theorem count_append (c : Config) (event : State → (Nat × Nat) → Bool)
    (s : State) (p q : List (Nat × Nat)) :
    eventCount c event s (p ++ q) =
      eventCount c event s p + eventCount c event (rawRun c s p) q := by
  induction p generalizing s with
  | nil => simp [eventCount,rawRun]
  | cons g p ih =>
    simp only [List.cons_append,eventCount,rawRun,ih]
    omega

theorem extra_is_count (c : Config) (s : State) (p : List (Nat × Nat)) :
    extraCount c s p = eventCount c (extraEvent c) s p := by
  induction p generalizing s with
  | nil => rfl
  | cons g p ih => simp only [extraCount,eventCount,ih]

theorem repeat_partition (c : Config) (s : State) (p : List (Nat × Nat)) :
    eventCount c (repeatEvent c) s p = extraCount c s p +
      eventCount c (repeatedMandatory c) s p := by
  induction p generalizing s with
  | nil => rfl
  | cons g p ih =>
    simp only [eventCount,extraCount,ih]
    cases hr : repeatEvent c s g <;> cases hm : mandatoryEvent c s g <;>
      simp [extraEvent,repeatedMandatory,hr,hm] <;> omega

theorem extra_prefix (c : Config) (s : State) (p q : List (Nat × Nat)) :
    (rawRun c s p).extra ≤ (rawRun c s (p ++ q)).extra := by
  rw [raw_append]
  have he := raw_extra c (rawRun c s p) q
  omega

theorem extra_of_repeat_bound (c : Config) (s : State) (p : List (Nat × Nat))
    (e : Nat) (h : eventCount c (repeatEvent c) s p ≤
      e + eventCount c (repeatedMandatory c) s p) :
    (rawRun c s p).extra ≤ s.extra + e := by
  have hp := repeat_partition c s p
  rw [raw_extra]
  omega

theorem prefix_extra_of_repeat_bound (c : Config) (s : State)
    (p q : List (Nat × Nat)) (e : Nat)
    (h : eventCount c (repeatEvent c) s (p ++ q) ≤
      e + eventCount c (repeatedMandatory c) s (p ++ q)) :
    (rawRun c s p).extra ≤ s.extra + e :=
  Nat.le_trans (extra_prefix c s p q) (extra_of_repeat_bound c s (p ++ q) e h)

theorem extra_guard_of_endpoint_bound (c : Config) (depth : Nat) (s : State)
    (p q : List (Nat × Nat)) (g : Nat × Nat)
    (h : (rawRun c s (p ++ g :: q)).extra ≤ 2-c.sources.length) :
    (propose c (depth+p.length) (rawRun c s p) g.1 g.2).extraBad = false := by
  have hb := extra_prefix c s (p ++ [g]) q
  rw [List.append_assoc] at hb
  have he : (rawRun c s (p ++ [g])).extra ≤ 2-c.sources.length := Nat.le_trans hb h
  rw [raw_append] at he
  change (advance c (rawRun c s p) g).extra ≤ 2-c.sources.length at he
  change decide ((propose c (depth+p.length) (rawRun c s p) g.1 g.2).state.extra >
    2-c.sources.length) = false
  rw [proposal_state_depth]
  exact decide_eq_false (Nat.not_lt.mpr he)

theorem basis_seen_checked :
    ∀ i : Fin 7, base.contains ((2^i.val) &&& 127) = true := by decide

theorem return_is_repeat (c : Config) (s : State) (g : Nat × Nat)
    (hc : ∀ i ∈ c.sources, i < 7) (h : returnEvent c s g = true) :
    repeatEvent c s g = true := by
  simp only [returnEvent,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at h
  obtain ⟨⟨ht,hv⟩,_⟩ := h
  have hm : c.sources[g.1]! ∈ c.sources := by
    simpa [ht] using (List.getElem_mem (l := c.sources) ht)
  have hb := basis_seen_checked ⟨c.sources[g.1]!,hc _ hm⟩
  simp only [repeatEvent,hv,hb,Bool.true_or]

def MandatorySeen (c : Config) (s : State) : List (Nat × Nat) → Prop
  | [] => True
  | g :: p => (mandatoryEvent c s g = true → repeatEvent c s g = true) ∧
      MandatorySeen c (advance c s g) p

theorem mandatory_count (c : Config) (s : State) (p : List (Nat × Nat))
    (h : MandatorySeen c s p) :
    eventCount c (repeatedMandatory c) s p = eventCount c (mandatoryEvent c) s p := by
  induction p generalizing s with
  | nil => rfl
  | cons g p ih =>
    obtain ⟨hg,hp⟩ := h
    simp only [eventCount,ih _ hp,repeatedMandatory]
    by_cases hm : mandatoryEvent c s g = true
    · simp [hm,hg hm]
    · have hf : mandatoryEvent c s g = false := Bool.eq_false_iff.mpr hm
      simp [hf]

theorem repeat_partition_mandatory (c : Config) (s : State) (p : List (Nat × Nat))
    (h : MandatorySeen c s p) :
    eventCount c (repeatEvent c) s p = extraCount c s p +
      eventCount c (mandatoryEvent c) s p := by
  rw [repeat_partition,mandatory_count c s p h]
theorem sector_sources_small (s : SectorCover.Sector) (hs : s ∈ SectorCover.sectors)
    (lookup : Nat → Nat → Bool) :
    ∀ i ∈ (ofSector s lookup).sources, i < 7 := by
  intro i hi
  change i ∈ s.active.map Fin.val at hi
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  have hb : ∀ k ∈ Budget.sources, k.val < 7 := by decide
  exact hb j ((SectorCoordinates.layout_properties s hs).2.2.2.1 hj)

theorem sector_return_is_repeat (sector : SectorCover.Sector)
    (hs : sector ∈ SectorCover.sectors) (lookup : Nat → Nat → Bool)
    (s : State) (g : Nat × Nat) (h : returnEvent (ofSector sector lookup) s g = true) :
    repeatEvent (ofSector sector lookup) s g = true :=
  return_is_repeat _ s g (sector_sources_small sector hs lookup) h

/-- The remaining semantic premises concern counted events, not an assumed extra bound. -/
theorem extra_le_full_budget (c : Config) (s : State) (p : List (Nat × Nat))
    (u q e fullRepeats : Nat) (hq : q ≤ 6) (seen : MandatorySeen c s p)
    (mandatory : u+q ≤ eventCount c (mandatoryEvent c) s p)
    (injection : eventCount c (repeatEvent c) s p + (6-q) ≤ fullRepeats)
    (budget : fullRepeats ≤ 6+u+e) :
    (rawRun c s p).extra ≤ s.extra+e := by
  have partition := repeat_partition_mandatory c s p seen
  rw [raw_extra]
  omega
theorem xor_mask (a b mask : Nat) :
    (a ^^^ b) &&& mask = (a &&& mask) ^^^ (b &&& mask) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and,Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases mask.testBit i <;> rfl

theorem copy_is_repeat (c : Config) (s : State) (g : Nat × Nat)
    (h : copyEvent c s g = true)
    (known : (base.contains ((if g.2 < count c then s.rows[g.2]!
        else (fixed c)[g.2-count c]!) &&& 127) ||
      PackedRows.has (projected s.history) ((if g.2 < count c then s.rows[g.2]!
        else (fixed c)[g.2-count c]!) &&& 127)) = true) :
    repeatEvent c s g = true := by
  simp only [copyEvent,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at h
  have hz := h.1.2
  simpa only [repeatEvent,value,xor_mask,hz,Nat.zero_xor] using known
end HGP13.CounterBudget






