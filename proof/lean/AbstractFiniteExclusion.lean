import FullWordPath
import PassiveInsertion

namespace HGP13.AbstractFiniteExclusion

open SectorCover SectorCoordinates SectorIndexing CoreRowEncoding
open SharedSearch TransitionChecks

/-- The finite statement to be supplied by an external complete search.
    It speaks about the abstract Lean transition relation and the exact
    passive cost of full 13-bit historical rows. No C++ claim is assumed
    in the general mathematical implication below. -/
def NoCheapTerminal (s : Sector) (lookup : Nat → Nat → Bool) : Prop :=
  ∀ q : List (IndexedGate (changing s) (fixedWires s)),
    q.length ≤ 12 + s.carriers.length →
    Path (ofSector s lookup) 0 (initial (ofSector s lookup)) (q.map label)
      (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (q.map label)) →
    terminal (ofSector s lookup)
      (rawRun (ofSector s lookup) (initial (ofSector s lookup)) (q.map label)) = true →
    18 < q.length +
      ((passive s).map (fun j =>
        (PassiveCost.cost
          (PassiveInsertion.historyRows (keep s) identity
            (q.map (fullGate (changing s) (fixedWires s))))
          (identity j ^^^ goal s j)).getD 999)).sum

theorem no_short_in_sector (s : Sector) (hs : s ∈ sectors)
    (lookup : Nat → Nat → Bool)
    (hpc : FullWordPath.PrefixComplete s lookup)
    (hfinite : NoCheapTerminal s lookup)
    (p : Program) (hp : Legal p) (hc : Compatible s p)
    (real : run identity p = HGP13.target)
    (short : p.length ≤ 18) : False := by
  obtain ⟨q,hq,hlen,hpath,hterminal⟩ :=
    FullWordPath.short_word_accepted_path s hs lookup hpc p hp hc real short
  let d := PassiveInsertion.historyRows (keep s) identity
    (q.map (fullGate (changing s) (fixedWires s)))
  let n : Wire → Nat := fun j =>
    (PassiveCost.cost d (identity j ^^^ goal s j)).getD 999
  have hcost : ∀ j ∈ passive s,
      PassiveCost.cost d (identity j ^^^ goal s j) = some (n j) := by
    intro j hj
    have controls : ∀ g ∈ word s p, keep s g.1 = true :=
      control_retained s p hc
    have erased : (word s p).filter (fun g => keep s g.2) =
        q.map (fullGate (changing s) (fixedWires s)) := by
      exact hq.symm
    have cover := PassiveInsertion.erased_history_covers (keep s)
      (word s p) (q.map (fullGate (changing s) (fixedWires s)))
      controls erased
    obtain ⟨k,hk,_⟩ := PassiveCost.actual_target_cost_bound
      (word s p) identity j (keep s) d controls cover
    rw [word_realizes s p real] at hk
    have hh : PassiveCost.cost d (identity j ^^^ goal s j) = some k := by
      simpa [SectorCoordinates.goal] using hk
    simp [n, hh]
  have hpassive := passive_properties s hs
  have controls : ∀ g ∈ word s p, keep s g.1 = true :=
    control_retained s p hc
  have erased : (word s p).filter (fun g => keep s g.2) =
      q.map (fullGate (changing s) (fixedWires s)) := hq.symm
  have cover := PassiveInsertion.erased_history_covers (keep s)
    (word s p) (q.map (fullGate (changing s) (fixedWires s)))
    controls erased
  have hlower := PassiveCost.total_cost_lower_bound (keep s) (passive s)
    (word s p) d (goal s) n controls cover hpassive.1
    hpassive.2.2.1 (word_realizes s p real) hcost
  rw [erased] at hlower
  simp only [List.length_map] at hlower
  rw [word_length] at hlower
  have hstrong := hfinite q hlen hpath hterminal
  dsimp [NoCheapTerminal] at hfinite
  change 18 < q.length + ((passive s).map n).sum at hstrong
  omega

/-- Exact finite obligations left to an external computation. The first
    component checks concrete catalogue pruning; the second excludes cheap
    terminals of the abstract search with exact full-row passive cost. -/
def FiniteFacts (lookup : Sector → Nat → Nat → Bool) : Prop :=
  ∀ s ∈ sectors,
    FullWordPath.PrefixComplete s (lookup s) ∧ NoCheapTerminal s (lookup s)

theorem no_short_of_finite_facts (lookup : Sector → Nat → Nat → Bool)
    (hf : FiniteFacts lookup) : HGP13.NoShortProgram := by
  intro p hp short real
  obtain ⟨s,hs,hc⟩ := SectorCover.every_short_word_covered p hp real short
  obtain ⟨hpc,hfinite⟩ := hf s hs
  exact no_short_in_sector s hs (lookup s) hpc hfinite p hp hc real short

theorem exact_minimum_of_finite_facts (lookup : Sector → Nat → Nat → Bool)
    (hf : FiniteFacts lookup) : HGP13.ExactMinimum HGP13.target 19 := by
  exact HGP13.exact_minimum_of_no_short (no_short_of_finite_facts lookup hf)

end HGP13.AbstractFiniteExclusion
