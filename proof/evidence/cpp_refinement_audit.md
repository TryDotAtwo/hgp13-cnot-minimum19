# C++ / Lean search correspondence: static audit, 27 September 2026

Scope: pinned `hgp13_verify.cpp` SHA-256
`2174f445df534455c30e9ae7b54b8dfff4fdbdce3ff4eaf6b7d7e557fa3f8e4c`
against `SharedSearch.lean`, `TransitionChecks.lean`,
`AbstractFiniteExclusion.lean`, and `ConcreteFiniteBoundary.lean`.
This is a source review and data audit, **not a formal C++ refinement proof**.
The line-by-line bounds, loop invariants, concurrency review, and one
UBSan diagnostic are in `evidence/cpp_algorithm_audit.md`.

The case-sequence exports can be regenerated without a full search:
compile `scripts/sector_cases.cpp` with `g++ -O2 -std=c++17` and run it,
then run `scripts/SectorCasesExport.lean` with Lean 4.34.0 and the compiled
Lean project on `LEAN_PATH`. Both output files in `evidence/` have the same
SHA-256 shown below; `scripts/audit_full_run.py` checks byte equality.

| Item | C++ source | Lean definition/theorem | Audit observation |
|---|---|---|---|
| Case order and depth | `make_cases`, `compute`: 363 cases, `12+ny` | `SectorCover.sectors`, `SharedSearch.maxDepth` | Both enumerate 225+90+36+6+6 parameter records. Separate C++ and Lean exports of all 363 concrete orientation/source/relay tuples are byte-identical (`ae5942bfa77d4a416a843cce5d5478b3fcedff7be896e9dbcaa71b4b9fac334d`). The saved log has all IDs. This checks the tuple sequence, not the C++/Lean transition semantics. |
| Initial rows and goals | `compute`: `fixed`, `want`, `passive`, `initial` | `SharedSearch.fixed/want/passive/initial`, `initial_agreement` | Literal formulas agree: mutable sources, central row, relay rows; all 7+q initial basis forms enter history. Lean checks its own literals for every sector. |
| State identity | `State::operator==` | `SharedSearch.State`, `IndexedHistoryBits.indexed_history_bit_iff` | Both retain rows, eight-word/full-bit history, changed, returned, copied and extra. Lean proves that each abstract history bit on an indexed path exactly reflects occurrence of its supported full row. C++ hashes may collide, but `unordered_set` resolves equality through all fields; hash is not used as proof of equality. |
| Transition | `compute`: target/control loops and row XOR | `SharedSearch.next/move`; `TransitionChecks.move_eq_checked` | Both enumerate all mutable targets and mutable/fixed controls, reject equal indices and zero XOR, then update the same state fields. This remains a static code comparison, not a machine-checked equivalence of implementations. |
| First transition states | `scripts/make_first_layer_diagnostic.py` instruments the pinned `compute` just after its first `current.swap(next)` | `scripts/FirstLayerStatesExport.lean` runs `SharedSearch.next` with the concrete lookups | The full deduplicated first-layer state sets agree for every sector: 8,610 state records, with rows, all eight history words, and four counters compared. Their 363 sizes also agree with `layers[1]` in the saved C++ run. This checks one transition, not later search layers. |
| All layers, sectors 234 and 359 | `scripts/make_sector234_layers_diagnostic.py` instruments the pinned `compute` at the head of every layer | `SectorGraph234` and `SectorGraph359` check the corresponding candidate graphs with `SharedSearch.next` | `scripts/audit_sector234_layers.py` finds equality of all 6,668 and 2,208 full state records, respectively, across 13 and 10 layers including empty final layers. These are bounded two-sector diagnostics, not a proof of C++ semantics or of the other sectors. |
| Catalogue | `generate_catalogues`, `encode`, `compute` prefix test | `Catalogues`, `IdealPrefixLookup`, literal trees | Static loop and combinatorial review in `cpp_algorithm_audit.md` checks enumeration of the 113 allowed forms, feasible triples/quadruples, and their subsets. A fresh short exporter of the pinned source and an independent exhaustive enumerator with simultaneous closure rounds yield byte-identical four key sets; `audit_full_run.py` compares them with the literal Lean trees. These checks are external evidence; neither the C++ generator/lookup semantics nor concrete `PrefixComplete` is proved in Lean. |
| Pruning | `compute`: `extra`, `capacity`, clean-core/passive guards, `bound` | `SharedSearch.move`, `TransitionChecks.propose`; full-word guard lemmas | Branch predicates and their order agree in the reviewed source. Lean proves that no legal short full word is pruned, assuming the concrete table's `PrefixComplete`. The C++ branch implementation itself is not formally verified. |
| Terminal cost | `changed`/`want` test; `xor_cost`; `best` | `SharedSearch.terminal`, `PassiveCost.cost`, `PackedCostRefinement.cost_pack_eq`, `SectorPackedCost.indexed_history_cost_pack_eq`, `StateHistoryCost.indexed_cost_eq_decoded`, `FiniteFrontierBoundary.stateCost` | Lean proves that the full-row and packed-mask 0/1 recurrences have identical costs for every indexed sector path and passive target. It also proves that the exact full-row cost is determined by decoding the terminal state's history bits. C++ checks terminal at every processed depth and computes packed passive costs. The C++ in-place array update remains source-audited, without a formal C++ array-refinement proof. `999` represents unreachable cost; fewer than 512 distinct 7–9-bit forms exist, so a finite exact cost cannot reach 999. |
| Search completion | `current`/`next` sets; `depth <= maxdepth`; final `require` | `DepthFrontier.reach_iff_frontier`, `DepthFrontier.path_mem_frontier`, `NoCheapTerminal` finite premise | Lean proves that the deduplicated abstract layer contains exactly the reachable complete states and every accepted path appears at its depth. C++ processes every generated state and deduplicates complete states according to the static audit. The transcript shows `best>18` for all cases; the proof that it establishes Lean's quantified finite premise still depends on the unformalized C++ correspondence. |

`scripts/audit_full_run.py` checks the preserved source digest, exact 363
case IDs, family metadata, each layer sum, all four family summaries,
306922994 labels, 90516 terminals, absence of a `best<=18` record,
agreement of three saved transcripts at the case-record level, and all four
literal prefix-tree key sets against `scale_pilot/catalogue_keys.txt`.
The packaged `scripts/catalogue_keys.cpp` includes the pinned verifier
source, calls only `generate_catalogues`, and emits the four sorted key
sets. Recompiling and running this exporter in the existing offline
`cnot-beam-torch:cu128` container produced SHA-256
`1ab90d4d09b35f4ec5c7cf30bff692718ba90e807039e05c1885b5da50ad25c3`,
exactly the packaged key-export digest. This short catalogue regeneration
did not rerun the 363-sector search.
`scripts/independent_catalogue_check.cpp` does not include the verifier
source. It enumerates every triple and quadruple of the 113 admissible
seven-bit forms and saturates pending goals and auxiliaries in simultaneous
rounds. Its counts are 298/21687 and 298/21823, and its four sorted key
lists are byte-identical to the pinned-source export. The reproducible
audit is `scripts/audit_independent_catalogues.py`; report and raw output
are in `evidence/independent_catalogue_*`. This independently checks the
finite catalogue data but is still an external program, not a Lean proof
of the concrete enumeration or executable lookup semantics.
`scripts/make_first_layer_diagnostic.py` refuses a different source SHA and
requires unique textual insertion points. It generates a diagnostic source
(SHA-256 `52ae2936638f677afa676ccbfed11aa58992f0cd7f86e71df8ce55eddd906844`)
that stops after one transition and emits complete states. The derived
program cannot print the full-verification marker. `audit_full_run.py`
compares its output with the separate Lean export as sets, checks all 363
per-case sizes, and rejects duplicate records. This instrumentation is
explicitly diagnostic; it does not change the pinned source or old log.
The sector-234 and sector-359 diagnostic sources have SHA-256
`faf1ba6fa9dbd93d2471662f98c45754c4196a69615d2d94c1fdb1f84074efbd`
and `bce14188add23ce1343ef699fc427dccf3833ffd172f9f3920d535d41402b858`.
`evidence/sector234_layers_audit.json` and
`evidence/sector359_layers_audit.json` record per-layer counts and set
equality with `sector234/pilot234_graph.txt` and `pilot359/graph359.txt`.
The latter candidate graphs are separately checked against
`SharedSearch.next` in Lean. The two diagnostic exports do not replace
the pinned full-run transcript.
The separate deterministic `xor_cost` differential test compares the pinned
C++ loop against a shortest-path BFS oracle on 1,518 histories and all
453,376 cells in their 7–9-bit cost arrays; every value agrees. Its scope
and source hashes are in `evidence/xor_cost_differential_audit.json`.
The original log does not contain a signed binary identity or a source
digest emitted by the running process. A new full run under
`evidence/full_provenance_2026-09-27/` records the exact source hash,
compiler command, saved binary hash, exit code zero, and full transcript
hash. `scripts/audit_full_provenance.py` rechecks these files and establishes
equality of all 363 sector records and completion summaries with the
preserved run. The wrapper manifest improves reproducibility and provenance,
but it is not a cryptographic attestation emitted by the binary, an
independent solver, or a formal C++ refinement proof.

The accepted Lean theorem
`ConcreteFiniteBoundary.exact_minimum_of_external_finite_result` has one
explicit premise, `ExternalFiniteResult`. It is **not** currently discharged
by the Lean kernel. Its two components are (1) completeness of the exact
literal prefix tables and (2) absence of a terminal state with decoded
core-plus-passive cost at most 18 in every deduplicated abstract frontier
through its sector's depth cap. `FiniteFrontierBoundary` proves that this
state-and-layer fact implies the earlier path-quantified `NoCheapTerminal`.
The static review and transcript checks support these finite claims as
external evidence, with the implementation and execution trust boundary
stated above. They must not be described as an unconditional Lean proof.
