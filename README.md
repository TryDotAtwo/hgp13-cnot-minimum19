# Exact minimum CNOT length 19 for a fixed 13 × 13 binary transformation

Author: Ivan Litvak. Reproducibility supplement for the preprint [Proving the Exact Minimum CNOT Length of a 13 × 13 Binary Transformation](https://www.researchgate.net/publication/415233397_Proving_the_Exact_Minimum_CNOT_Length_of_a_13_13_Binary_Transformation).

## Claim and trust boundary

The target row masks are `(1,2,4,8,16,32,329,402,292,515,1030,2075,4150)`, with bit j representing column j. All 156 directed CNOT gates on 13 labelled coordinates have unit cost. No ancillas or free permutations are allowed. The claimed exact minimum for the full operator is 19.

An explicit witness supplies the upper bound. The lower bound uses mathematical reductions and an exhaustive external C++ calculation covering 363 sectors. Lean proves the general reduction and a **conditional** exact-minimum theorem from explicit finite catalogue/search premises. The full C++ calculation, compiler, execution, and source-to-run correspondence are external evidence, not an unconditional Lean-kernel proof. No independent expert endorsement is claimed.

## Files

- `proof/lean/`: full Lean sources, pinned toolchain and Lake configuration.
- `proof/lean-project.zip`: convenient standalone Lean project archive.
- `proof/hgp13_verify.cpp`: self-contained C++ verifier.
- `proof/evidence/`: preserved computational, provenance and audit evidence.
- `proof/verification_run.txt` and `proof/verification_summary.json`: recorded Lean audit.
- `proof/verify_lean.py`, `proof/scripts/`: reproduction/audit commands.
- `article/`: 27 September editorial source and PDF corresponding to this proof package. The separately linked ResearchGate preprint is dated 5 October; the public-preprint editorial revision is not asserted to be byte-identical to this archived article.
- `SHA256.json`: hashes of every delivered file other than this manifest.

## Reproduce

See `proof/README.md` and `proof/lean/lean-toolchain`. From `proof/`, the supplied Lean audit uses `python verify_lean.py` and the pre-existing Docker image `local/lean4:4.34.0`. To rerun the C++ finite calculation:

```sh
g++ -O3 -std=c++17 -pthread proof/hgp13_verify.cpp -o hgp13_verify
./hgp13_verify 3
```

The historical development status and pilots are retained as evidence; they do not strengthen the stated conditional Lean claim. This publication rechecks the archived file manifest; it does not constitute a new Lean build or full computation rerun.

## AI disclosure

The manuscript acknowledges OpenAI, the Astra AI assistant, and CayleyPy. AI assisted examination of computational evidence and development of the Lean formalization, as well as manuscript preparation. Codex prepared and audited the reproducibility material. The author remains responsible for the claims.

Upstream vendor notices are retained. No new license for the entire source package is imposed by this supplemental release.
