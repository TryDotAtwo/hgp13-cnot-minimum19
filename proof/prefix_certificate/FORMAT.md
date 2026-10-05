# HGP13 catalogue-prefix tree certificate contract

Status: the generic Lean checker and its soundness theorems are accepted in
`outputs/hgp13-arxiv/lean/PrefixCertificate.lean`,
`PrefixTreeCertificate.lean`, and `PrefixPackedFourth.lean`. No full original
or transpose certificate has been accepted. This is the interface for an
untrusted external exporter; bounded pilots currently use Python, while the
intended large export is C++.

## Payload

For each orientation, emit a `PrefixPackedFourth.Cert4` with layers `l0`
through `l4`. The first four layers use `PrefixTreeCertificate.Tree`, whose
nodes hold lists of seven-bit `Value`s. The fourth layer uses
`PrefixPackedFourth.Tree4`, whose nodes hold a three-form prefix and a 128-bit
mask of fourth values. Intended nodes contain sorted, distinct auxiliary
forms; depth `d` nodes hold `d` forms. The Lean checker does not assume those
formatting properties for soundness. The trees should be balanced by the key
`SharedSearch.encode (xs.map BitVec.toNat)` for practical lookup. Each node
must be its own full list value; `has` compares full lists before branching,
so even a key collision cannot make a false positive.

The concrete check is `verifyThree goals lookup cert` for depth three or
`verifyFour goals lookup cert` for depth four. It requires:

1. `l0` recognizes `[]`.
2. For each listed state at each preceding layer, every new nonzero form
   derivable after greedy goal saturation must be found in the next tree
   after canonical sorting.
3. For every listed final state whose full catalogue is accepted, all 8 or
   16 encoded subset keys must pass the supplied concrete prefix lookup.
   `PrefixPackedFourth.finalTreeOK` checks this per prefix mask without
   constructing the flattened four-form layer; Lean proves it equivalent
   to the original list check.

The checker proves a one-way sufficiency statement. Extra nodes and duplicate
nodes cannot make it unsound, but they increase cost. Missing a reachable
node makes a transition check fail. There is no need to trust the C++
exporter's search or deduplication if the exact concrete certificate is
accepted by Lean kernel.

## Trust and remaining gates

`PrefixTreeCertificate.verifyThree_lookup` and
`PrefixPackedFourth.verifyFour_lookup` prove
that an accepted concrete certificate covers every observed subset of every
abstract `Catalogued` triple or quadruple. The theorems do not establish
that any large concrete certificate is accepted. Their `lookup` argument
must be instantiated with the exact trees used by `SharedSearch`, in both
orientations. The bridge from the actual `SharedSearch.next` catalogue guard
to these lookup theorems still needs composition, and all other pruning,
terminal costs, sectors and the unconditional minimum theorem remain open.

If certificate acceptance is checked only by an external executable instead
of a Lean proof term, the executable, compiler and run enter the trusted base;
that cannot be reported as a fully kernel-checked theorem. The intended
handoff is C++ as an untrusted generator and Lean as the certificate checker.

Before exporting every sector, measure the tree checker on representative
depth-four and q=2/p=1 cases, including memory, wall time, and checked
transitions. Split the certificate into independently checked chunks if a
single reduction is too large. Deleting a required child from a concrete
certificate must make its transition check false; the accepted tiny example
`tiny_deleted_successor_rejected` exercises this property. A real
depth-two omitted-child control is accepted in `PrefixTreeDepth2Omitted.lean`.
The full four-form negative control remains to be run.

The bundled `export_depth2.py` emits an untrusted transpose depth-two probe
with layer sizes 1, 39, 970. Accepted module `PrefixTreeDepth2Transpose.lean`
proves all 39 first-to-second parent obligations and composes them into the
whole depth-two step. `PrefixTreeDepth2Omitted.lean` removes one required
successor of parent 0 and kernel-proves its obligation is false.

The depth-three pilot checked one parent against 20,125 states. An explicit
fourth-layer tree of 386,819 states produced a 28.6 MB source and reached
the 4 GiB memory limit without a successful check. The packed exporter
`export_packed4_probe.py` groups those states into 53,801 three-form prefixes
with 128-bit masks; its 6.2 MB source passed a single parent check under the
same limit. `PackedFourthFinalNodeTranspose.lean` checks one real group
`(3,5,12)` with 55 fourth values against `SectorGraph359.prefix4`; deleting
required lookup key zero makes that check false. None of these local fourth-
layer checks establish complete coverage of its 20,125 parents or all
53,801 final groups. Full prefix coverage, sector checks and the minimum
theorem remain open.

`DEPTH3_BENCHMARK.md` records the next bounded check. Lean accepted the
20,125-node transpose third-layer tree and a group of 25 parent obligations.
The monolithic 970-parent check hit the 4 GiB limit; no complete third-layer
transition theorem or final triple-key theorem has been accepted.
