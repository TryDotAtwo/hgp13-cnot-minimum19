import Graph234Layer1
namespace HGP13.SectorGraph234
open SharedSearch
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
def s0_0 : State := ⟨[1,4,64,128], 340282366920938463481821351509772796182, 0, 0, 0, 0⟩
theorem s0_0_edges : next config 0 s0_0 = [s1_18, s1_14, s1_15, s1_16, s1_17, s1_13, s1_12, s1_7, s1_9, s1_8, s1_10, s1_11, s1_0, s1_2, s1_6, s1_1, s1_3, s1_4, s1_5] := by decide
theorem s0_0_safe : Safe 13 0 s0_0 := by
  apply safe_succ 12 0 s0_0 [s1_18, s1_14, s1_15, s1_16, s1_17, s1_13, s1_12, s1_7, s1_9, s1_8, s1_10, s1_11, s1_0, s1_2, s1_6, s1_1, s1_3, s1_4, s1_5] (by decide) s0_0_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s1_18_safe
  · subst z; exact s1_14_safe
  · subst z; exact s1_15_safe
  · subst z; exact s1_16_safe
  · subst z; exact s1_17_safe
  · subst z; exact s1_13_safe
  · subst z; exact s1_12_safe
  · subst z; exact s1_7_safe
  · subst z; exact s1_9_safe
  · subst z; exact s1_8_safe
  · subst z; exact s1_10_safe
  · subst z; exact s1_11_safe
  · subst z; exact s1_0_safe
  · subst z; exact s1_2_safe
  · subst z; exact s1_6_safe
  · subst z; exact s1_1_safe
  · subst z; exact s1_3_safe
  · subst z; exact s1_4_safe
  · subst z; exact s1_5_safe
theorem initial_eq : initial config = s0_0 := by decide
theorem initial_safe : Safe 13 0 (initial config) := by rw [initial_eq]; exact s0_0_safe
theorem reachable_terminal_key {k z} (h : Reach 0 (initial config) k z) (hk : k ≤ 13)
    (ht : terminal config z = true) : (k,z.history) ∈ keys := by
  have hc := safe_reach h 13 hk initial_safe
  simpa using hc ht
end HGP13.SectorGraph234
