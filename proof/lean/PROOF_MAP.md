# Formal lower-bound proof map

This development does not yet prove `HGP13.ExactMinimum HGP13.target 19`.
The checked statements below concern the actual numeric masks and arbitrary
full-matrix programs, not a hypothesis asserting the desired lower bound.

## Completed chain

1. `FreeXor.original_masks_exact_minimum_ten` proves that the seven targets
   `[73,82,3,6,27,54,100]`, starting from the seven unit vectors, require
   exactly ten free XOR additions. Previously computed values may be retained
   and reused without restriction.
2. The lower-bound argument splits the seven-dimensional space into
   coordinates of dimensions four and three. For any two proposed auxiliary
   values, a nonzero linear functional on the three-dimensional component
   annihilates both representative discrepancies. An induction proves that
   every computed value with zero four-dimensional component lies in the
   functional's kernel. At least one required target lies outside it.
   Thus two auxiliary values cannot suffice. Small finite linear identities
   are checked by kernel reduction; arbitrary program length is handled by
   induction, not by enumerating CNOT programs.
3. `FreeXor.original_masks_three_auxiliaries` strengthens the conclusion to
   three distinct auxiliary values even when zero is initially available
   and computed values may repeat.
4. `Projection.every_realization_needs_three_auxiliaries` projects each full
   row onto coordinates 0–5 and 8 and proves that every CNOT execution yields
   a valid free XOR trace. The initial zero is a mathematical projection of
   identity rows, not a physical ancilla or an input initialized to zero.
5. `Budget.fresh_count` proves at least ten first appearances: seven target
   projections and three distinct auxiliaries. `Budget.repeated_count`
   proves at least `6+u` repeated appearances: one first nonzero update on
   each of the six private outputs and one final restoration for each
   touched source. These are different target coordinates.
6. `Budget.length_ge_sixteen_plus_u` partitions all gate events into these
   two classes and proves `16+u ≤ p.length`. Here `u` counts distinct
   coordinates in 0–5 that occur as gate targets. The corollary
   `Budget.short_program_touches_at_most_two_sources` proves `u ≤ 2` for
   any realization of length at most 18.

7. `Transposition.full_program_transpose` and `full_program_oriented`
   prove the coefficientwise correspondence for arbitrary full words.
   `TransposeTarget` proves the concrete target and parameter correspondence.
8. `TransposeFree.potential_required` restricts possible auxiliary pairs by
   the first occurrences of three mandatory masks. `TransposeCertificate`
   checks all 198 remaining ordered-pair cuts and proves coverage over all
   seven-bit values. `TransposeBudget.original_exact_free_minimum_ten`
   proves the concrete transpose XOR minimum without assuming the general
   rectangular transposition theorem. Induction, not a program-length cutoff,
   connects the cuts to arbitrary free XOR programs.
9. `TransposeBudget.length_ge_sixteen_plus_v` proves the second full-word
   bound. `ExactBudget.exact_budget` and
   `TransposeBudget.exact_oriented_budget` prove the exact budget and its
   saturation consequences in both orientations.
10. `ZeroSector.zero_sector_lower_bound` proves the complete source
    Lemma 5.1. A generic invariant connects coefficient changes to the parity
    of individual gate multiplicities. The proof obtains central switching
    costs and six output costs, then uses an exact partition of the gate
    alphabet to conclude length at least twenty for `u=v=0`.
11. `SectorCover.full_sector_cover` proves the parameter coverage from
    Section 6. The explicit list has 363 distinct records; the selected
    orientation retains legality, length and the full operator. The active
    set is exact, whereas the output-control set may be padded.

## Still open

The abstract catalogue extension, clean-carrier persistence, passive minimum
and legal insertion, and remaining-cost bounds are now kernel verified.
Coordinate restriction, packed rows, and projected history are also verified,
including the literal initial and target values for all 363 sectors.

Still open are completeness of the concrete catalogue tables, full-word
correspondence with the actual pruned search transitions and counters,
the terminal total-cost bridge, and kernel-checked exclusion of every required
sector. The sector-284 certificate excludes paths in its specified finite
graph; its connection to all full CNOT words is not yet proved.
The general rectangular free-XOR
transposition theorem is also open, but its needed concrete consequence
has been proved independently. See `../STATUS.md` and `../claim_map.json`.
The C++ run is separate evidence and is not imported as a Lean axiom.

## Verification

`Audit.lean` requests transitive axiom reports for the proved declarations.
`../verify_lean.py` builds with the pinned Lean version, rejects proof holes
and native-reduction shortcuts, and binds the audit to source hashes in
`../evidence/lean_verification.json`. Standard `propext`, `Classical.choice`,
and `Quot.sound` are allowed.
