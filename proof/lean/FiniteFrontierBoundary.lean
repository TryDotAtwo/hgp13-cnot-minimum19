import AbstractFiniteExclusion
import DepthFrontier
import StateHistoryCost

namespace HGP13.FiniteFrontierBoundary
open SectorCover SectorCoordinates SectorIndexing CoreRowEncoding
open SharedSearch TransitionChecks

/-- Exact mathematical terminal cost attached to a complete search state. -/
def stateCost (s : Sector) (k : Nat) (z : SharedSearch.State) : Nat :=
  k + ((passive s).map (fun j =>
    (PassiveCost.cost (StateHistoryCost.decode s z.history)
      (identity j ^^^ goal s j)).getD 999)).sum

/-- A finite, depth-indexed exclusion condition directly on abstract BFS
    layers. The concrete C++ execution is not assumed to satisfy it here. -/
def NoCheapFrontier (s : Sector) (lookup : Nat → Nat → Bool) : Prop :=
  let c := ofSector s lookup
  ∀ k z, k ≤ maxDepth c →
    z ∈ DepthFrontier.frontier c 0 (initial c) k →
    terminal c z = true → 18 < stateCost s k z

theorem no_cheap_terminal_of_frontier (s : Sector) (hs : s ∈ sectors)
    (lookup : Nat → Nat → Bool)
    (hf : NoCheapFrontier s lookup) :
    AbstractFiniteExclusion.NoCheapTerminal s lookup := by
  intro q hlen hpath hterminal
  let c := ofSector s lookup
  let z := rawRun c (initial c) (q.map label)
  have hmem : z ∈ DepthFrontier.frontier c 0 (initial c) q.length := by
    simpa only [List.length_map] using
      (DepthFrontier.path_mem_frontier hpath)
  have hcap : q.length ≤ maxDepth c := by
    simpa [c, SharedSearch.maxDepth, SharedSearch.ofSector] using hlen
  have hcost := hf q.length z hcap hmem hterminal
  have hmap :
      ((passive s).map (fun j =>
        (PassiveCost.cost (PassiveInsertion.historyRows (keep s) identity
          (q.map (fullGate (changing s) (fixedWires s))))
          (identity j ^^^ goal s j)).getD 999)).sum =
      ((passive s).map (fun j =>
        (PassiveCost.cost (StateHistoryCost.decode s z.history)
          (identity j ^^^ goal s j)).getD 999)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro j hj
    rw [StateHistoryCost.indexed_cost_eq_decoded s hs lookup q
      (identity j ^^^ goal s j)]
  change 18 < q.length +
    ((passive s).map (fun j =>
      (PassiveCost.cost (PassiveInsertion.historyRows (keep s) identity
        (q.map (fullGate (changing s) (fixedWires s))))
        (identity j ^^^ goal s j)).getD 999)).sum
  rw [hmap]
  exact hcost

end HGP13.FiniteFrontierBoundary
