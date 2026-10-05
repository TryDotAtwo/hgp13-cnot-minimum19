# Transpose depth-three prefix certificate benchmark

Environment: Lean 4.34.0 in `local/lean4:4.34.0`, Docker memory limit 4 GiB.
Candidate layers have 1, 39, 970 and 20,125 states. The tree contains the
20,125 third-layer states; its generator is untrusted, while each accepted
Lean theorem checks its stated condition.

- Building the tree module alone took 45 seconds and passed.
- One monolithic `stepOK` theorem over all 970 second-layer parents reached
  the 4 GiB memory limit and was stopped without an accepted theorem.
- A module with the first 25 separate `nodeStepOK` theorems and a grouped
  Boolean theorem passed in 70 seconds. An intermediate Docker snapshot
  showed 416 MiB in use; this is not a peak measurement.
- A generic explicit-path checker and its soundness theorem compiled. Its
  independent 25-parent pilot passed in 71 seconds, using 155,315 bytes of
  path literals. On this matched block, explicit paths did not reduce wall
  time relative to the direct Boolean check. This is one block, not a claim
  about all parents or peak memory.

The observed 70 seconds per 25 parents extrapolates to roughly 45 minutes
for this transition alone if later parents cost the same; that is only a
planning estimate. The next transition has 20,125 parents and a packed
fourth-layer tree, so the same rate would exceed 15 hours before final-key
checks. These figures do not establish feasibility for both orientations,
the full 363-sector search, or the required representative q=2 and p=1
cases. A more local membership certificate or further chunked checker needs
profiling before mass generation.

`PrefixTreeDepth3TransposeBase.lean`,
`PrefixTreeDepth3TransposeChunk00.lean`, `PrefixPathWitness.lean`, and
`PrefixPathProbe.lean` are the accepted modules. The
remaining generated chunks are candidates only and are not in the audit.
