import FiniteFrontierBoundary
import OriginalPrefixesLite
import Sector359Agreement

namespace HGP13.ConcreteFiniteBoundary

/-- The two literal prefix tables shipped with the verifier package. -/
def lookup (s : SectorCover.Sector) (capacity key : Nat) : Bool :=
  if s.transposed then Sector359Agreement.lookup359 capacity key
  else OriginalPrefixesLite.lookup capacity key

/-- The external finite premise is stated directly on complete abstract
    breadth-first layers and their state-based exact terminal cost. It is
    not asserted by Lean or inferred from an unauthenticated C++ log. -/
def ExternalFiniteResult : Prop :=
  ∀ s ∈ SectorCover.sectors,
    FullWordPath.PrefixComplete s (lookup s) ∧
    FiniteFrontierBoundary.NoCheapFrontier s (lookup s)

theorem exact_minimum_of_external_finite_result
    (h : ExternalFiniteResult) : HGP13.ExactMinimum HGP13.target 19 := by
  have hf : AbstractFiniteExclusion.FiniteFacts lookup := by
    intro s hs
    obtain ⟨hpc,hfrontier⟩ := h s hs
    exact ⟨hpc,FiniteFrontierBoundary.no_cheap_terminal_of_frontier
      s hs (lookup s) hfrontier⟩
  exact AbstractFiniteExclusion.exact_minimum_of_finite_facts lookup hf

end HGP13.ConcreteFiniteBoundary
