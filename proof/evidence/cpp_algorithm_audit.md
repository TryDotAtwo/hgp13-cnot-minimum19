# Pinned C++ verifier: loop and representation audit

Source: `hgp13_verify.cpp`, SHA-256
`2174f445df534455c30e9ae7b54b8dfff4fdbdce3ff4eaf6b7d7e557fa3f8e4c`.
Line numbers below refer to that exact source. This is a source-level audit of
the external computation, not a Lean proof of C++ semantics or a signed
attestation that the preserved log came from this binary.

## Representation and integer bounds

Each case has one or two active sources (`ns`), zero to two relays (`ny`),
`nc=ns+1+ny <=5`, `dimension=7+ny <=9`, and `maxdepth=12+ny <=14`
(lines 169–190). Mutable rows start as selected basis rows; fixed controls
are the remaining source basis rows (193–211). Every update is an XOR of
values below `2^dimension`, so all later rows and `want` values stay below
`2^dimension <=512`. They fit in `uint16_t`; `row[0..nc)` is inside the
five-element array. `remember` receives only values in `[1,511]`, so
`appeared[x/64]` indexes its eight words and every shift is by `0..63`
(122–125, 141–150, 211, 242–243, 268–269). `has_full` in `xor_cost`
receives `1..2^dimension-1` and the passive target indices are below 128.
No zero row is inserted: candidate value zero is rejected at line 243.

The `projected` loop ORs word `i` into word `i % 2` (lines 147–150):
bit `x` of the 512-bit history becomes bit `x mod 128` of the 128-bit
projection. Thus its low-seven-bit membership test matches the projection
used in `SharedSearch.projected`. This bit-index identity follows from
`x = 64 i + r`, `0 <= r < 64`; its C++ implementation remains in the
external trust boundary.

For generated states `extra <= 2-ns <=1`: each increment is performed on
an old value at most one, then rejected if above the slack (260–261).
The `uint8_t` counter therefore cannot wrap. `changed` and `returned`
use at most two bits; `copied` uses at most two bits (246–257). `capacity`
is three or four whenever catalogue lookup is reached, and the
length check precedes `encode` (264–267). An encoded key has at most four
base-128 digits, hence is below `128^4 = 2^28` and fits `uint32_t`
(38–42). The candidate's `aux` list has no duplicate projected forms;
the appended `p` is absent from `old` when `!seen` (234–263).

## Catalogue generation

The allowed auxiliary domain contains exactly the 113 nonzero seven-bit
forms outside the seven basis and seven distinct goal forms (80–88).
The increasing-index recursion at 90–111 visits every three- and four-
element subset once. For a chosen set, `xor_closure` maintains `available`
as the initial seven basis values plus previously accepted todo values
(51–78). A new value is accepted only if it XORs two currently available
values; adding values during a pass merely chooses a valid order. If an
entire pass adds none, no remaining value is available next in any valid
order. All todo entries are distinct and absent from the initial basis,
so `added == todo.size()` exactly means that all goals and auxiliaries
were generated. Every subset of each accepted set is inserted, and the
three-form prefix table is included in the four-form table (93–113).
These arguments explain the C++ procedure; the saved exported key sets
were independently compared with the two literal Lean trees. They do not
replace a formal C++/Lean refinement theorem.
An independent C++17 enumerator in `scripts/independent_catalogue_check.cpp`
uses simultaneous closure rounds and does not include the pinned verifier.
It exhausts all three- and four-element combinations of the same 113-form
domain, reproducing the four key lists byte for byte. The count and key
comparison is checked by `scripts/audit_independent_catalogues.py`.
This strengthens the external catalogue audit without changing its formal
trust boundary.

## Layer invariant and transition coverage

At the start of the loop for depth `d`, `current` is the set of distinct
states surviving `d` applications of the candidate transition, starting
with `initial` (207–215). A `State` equality comparison includes all rows,
all eight history words, and all four counters (120–128); hash collisions
cannot identify unequal states because `unordered_set` uses equality after
hashing. For each state, targets `t=0..nc-1` and controls
`j=0..nc+fixed.size()-1` are enumerated (238–240). The latter endpoint is
`nc+6-ns = 7+ny = dimension`: every retained mutable or fixed control is
considered. Only self-control and zero XOR are rejected before applying
the same state-field and guard formulas listed in `cpp_refinement_audit.md`
(240–308). After `next.insert`, `current.swap(next)` establishes the
layer invariant for `d+1` (308–311). The deduplicated first-layer states
were exported from a source-hash-pinned instrumented C++ copy and
independently calculated by concrete Lean `SharedSearch.next` for all 363
sectors. All 8,610 records agree, including rows, eight history words and
counters; the per-case sizes also match the preserved C++ transcript.
This checks one transition, not later layers.
For sectors 234 and 359, `scripts/make_sector234_layers_diagnostic.py`
instruments the same hash-pinned source at every layer head. The resulting
6,668 and 2,208 complete state records agree as unordered per-layer sets
with the previously exported candidate graphs, including their empty final
layers; `scripts/audit_sector234_layers.py` checks duplicate records, case
metadata, layer counts, and exact state equality. Lean separately checks
both candidate graphs against `SharedSearch.next`. This strengthens the
bounded differential evidence for two sectors without proving later-layer
correspondence for the other 361 or formally verifying C++ semantics.
Independently of the implementation, `DepthFrontier.reach_iff_frontier`
proves that deduplicating complete abstract states preserves every
reachable state at each depth; `path_mem_frontier` links accepted paths
to those layers. The remaining C++ correspondence is external.

The `current.empty()` break is safe: an empty frontier has no successors.
At `depth == maxdepth`, terminal states are checked before the break, and
no deeper core can satisfy the Lean-proved core-length bound (215–229).
Every state at every processed depth is tested for `changed` and exact
`want` rows (218–223). The terminal `best` is the minimum over those
tested states and their completion costs (223–227).

## Exact terminal cost and sentinel

`xor_cost` starts with cost zero for form zero and 999 for other forms
(152–155). For each nonzero historical form `v`, the pairs
`{x, x XOR v}` partition the form space; `x < x XOR v` visits every pair
once. Both old pair values are copied before either is overwritten
(157–160). The simultaneous assignments implement the 0/1 recurrence:
the new cost of `x` is the minimum of its old cost and one plus the old
cost of `x XOR v`, and conversely for the mate. Thus one historical form
is used at most once. The mathematical 0/1 recurrence and its equality
between full rows and packed forms are proved in `PassiveCost.lean` and
`PackedCostRefinement.lean`; the imperative pair loop is audited here.
`SectorPackedCost.lean` applies the packed equality to every indexed
sector path. `CostSetInvariant.lean` proves that repeats and order in the
full historical list cannot change the exact cost, and that deleting
duplicate supported packed forms preserves it. This justifies the
mathematical set interpretation of the C++ `appeared` mask.

At most `2^dimension-1 <=511` distinct nonzero forms are processed.
Any finite optimum therefore uses at most 511 forms, strictly below 999.
`999+1` is representable by `int`, and a minimum with 999 cannot turn an
unreachable entry into a finite one. A terminal total is at most
`maxdepth + 6*999 < 6010`; it cannot overflow `int`. In particular, no
sentinel value can be mistaken for a candidate of length at most 18.
Each passive target is a seven-bit value representable from the seven
initial basis forms, so any visited terminal has total completion cost
strictly below 999. The `best == 999` transcript convention therefore
means that no terminal state was visited; the log audit checks that
equivalence.
As a bounded independent check, `scripts/xor_cost_differential.cpp`
includes the pinned implementation but computes reference distances by
shortest-path BFS over XOR generators. It compared all 453,376 cost cells
from 1,518 deterministic histories across dimensions 7, 8, and 9, including
empty, singleton, basis, full, and seeded sparse histories. All agreed;
`evidence/xor_cost_differential_audit.json` pins source, harness, and output
hashes. This tests the implementation but does not replace the loop
invariant or a formal C++ refinement proof.

## Completion, parallelism, and evidence limit

Atomic `cursor.fetch_add` gives each worker a distinct case index
(415–427). Workers write distinct `results[id]` elements; the catalogue
objects are only read during search. Output lines are serialized by a
mutex (384–395). The main thread joins every worker before reading the
results; exceptions set `failed` and are rethrown after the joins
(421–436). It rejects any uncomputed case or `best <=18` before printing
the completion marker (437–454). The log audit independently checks all
363 IDs, layer sums, family totals, and absence of a cheap candidate.

The remaining trust boundary is material: the implementation has not been
verified as C++ semantics in Lean; cardinality comparisons do not prove
full transition equality; and the old transcript has no cryptographic
binding to the executed binary. The conditional Lean theorem makes the
finite search result an explicit external premise rather than hiding it.
A new full run in `evidence/full_provenance_2026-09-27/` compiled the pinned
source with GCC 11.4.0 and recorded the resulting binary SHA-256, command,
zero exit code, and transcript hash. Its 363 case records and completion
summaries agree with the preserved run. This is stronger provenance for a
repeat execution of the same code; it still does not verify C++ semantics
or cryptographically attest the old transcript.

As a bounded runtime diagnostic, this exact source was compiled with
`g++ -O1 -g -std=c++17 -pthread -fsanitize=undefined
-fno-sanitize-recover=all` and run with `--one 357` in the offline
`cnot-beam-torch:cu128` container (GCC 11.4.0). It returned zero, emitted no UBSan
diagnostic, and its complete case-357 record exactly matched the preserved
full-run record (`evidence/ubsan_case357.txt`). One diagnostic case does
not validate all 363 executions.
