import TransitionChecks

namespace HGP13.DepthFrontier
open SharedSearch TransitionChecks

/-- Exact breadth-first layers of the depth-dependent shared search.
    Removing duplicate complete states does not change membership. -/
def frontier (c : Config) (depth : Nat) (start : State) : Nat → List State
  | 0 => [start]
  | k+1 => ((frontier c depth start k).flatMap (next c (depth+k))).eraseDups

theorem mem_frontier_succ (c : Config) (depth : Nat) (start : State)
    (k : Nat) (z : State) :
    z ∈ frontier c depth start (k+1) ↔
      ∃ s ∈ frontier c depth start k, z ∈ next c (depth+k) s := by
  simp [frontier, List.mem_eraseDups, List.mem_flatMap]

/-- Reachability with transitions taken at their actual layer depths. -/
inductive Reach (c : Config) (depth : Nat) (start : State) : Nat → State → Prop where
  | refl : Reach c depth start 0 start
  | step {k s z} : Reach c depth start k s →
      z ∈ next c (depth+k) s → Reach c depth start (k+1) z

theorem reach_iff_frontier (c : Config) (depth : Nat) (start : State)
    (k : Nat) (z : State) :
    Reach c depth start k z ↔ z ∈ frontier c depth start k := by
  constructor
  · intro h
    induction h with
    | refl => simp [frontier]
    | @step k s z hs hz ih =>
      exact (mem_frontier_succ c depth start k z).mpr ⟨s, ih, hz⟩
  · intro h
    induction k generalizing z with
    | zero =>
      simp only [frontier, List.mem_singleton] at h
      subst z
      exact Reach.refl
    | succ k ih =>
      obtain ⟨s, hs, hz⟩ := (mem_frontier_succ c depth start k z).mp h
      exact Reach.step (ih s hs) hz

theorem reach_prepend {c : Config} {depth : Nat} {start t z : State}
    {k : Nat} (edge : t ∈ next c depth start)
    (h : Reach c (depth+1) t k z) : Reach c depth start (k+1) z := by
  induction h with
  | refl => exact Reach.step Reach.refl (by simpa using edge)
  | @step k s z hs hz ih =>
    have hstep : z ∈ next c (depth+(k+1)) s := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hz
    exact Reach.step ih hstep

theorem path_reach {c : Config} {depth : Nat} {start z : State}
    {word : List (Nat × Nat)} (h : Path c depth start word z) :
    Reach c depth start word.length z := by
  induction h with
  | nil depth s => exact Reach.refl
  | @cons depth s g p t z hm hp ih =>
    have hadm := ((TransitionChecks.move_eq_some_iff c depth s t g.1 g.2).mp hm).1
    have hb := TransitionChecks.admissible_indices c depth s g.1 g.2 hadm
    have hedge : t ∈ next c depth s :=
      (SharedSearch.next_iff c depth s t).mpr ⟨g.1, hb.1, g.2, hb.2.1, hm⟩
    exact reach_prepend hedge ih

theorem path_mem_frontier {c : Config} {depth : Nat} {start z : State}
    {word : List (Nat × Nat)} (h : Path c depth start word z) :
    z ∈ frontier c depth start word.length :=
  (reach_iff_frontier c depth start word.length z).mp (path_reach h)

end HGP13.DepthFrontier
