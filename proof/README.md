# Supplementary proof and computation material

The article sources are main.tex and figures/ at the submission root.
This directory contains the full Lean sources, pinned toolchain and Lake
configuration, source-bound build and axiom-audit logs, exact C++ verifier,
recorded full computation, audit scripts and bounded cross-checks.
lean-project.zip is also included for convenient separate download.

The main conditional Lean theorem is
ConcreteFiniteBoundary.exact_minimum_of_external_finite_result.
Its explicit ExternalFiniteResult consists of concrete catalogue completeness
and absence of cheap terminals in all abstract search frontiers.
The C++ implementation and this finite execution are external to Lean.

Run python verify_lean.py from this directory (requires the pre-existing
local/lean4:4.34.0 Docker image). Full C++ replay: compile hgp13_verify.cpp
with g++ -O3 -std=c++17 -pthread and run the result with argument 3.
The historical STATUS.md and claim map include development history; the
article's formalization-boundary section states the publication claim.
The evidence logs were not regenerated for this editorial release.

vendor/ contains the upstream source of the bundled needspace package;
its original LaTeX Project Public License applies.
