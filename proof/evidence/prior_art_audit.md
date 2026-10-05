# Prior-art boundary for the fixed-matrix claim (27 September 2026)

This note records what the cited primary sources establish. It is not a
claim that a literature search can prove global novelty.

1. Patel, Markov, and Hayes, *Optimal synthesis of linear reversible
   circuits*, Quantum Information and Computation 8 (2008), 282–294,
   [publisher PDF](https://www.rintonpress.com/xxqic8/qic-8-34/0282-0294.pdf):
   asymptotically optimal synthesis up to a multiplicative constant,
   with worst-case order `Theta(n^2/log n)`. It does not state an exact
   diameter for `n=13` or a minimum for the explicit matrix in this draft.
2. Bu, Fan, and Joo, *Minimum Synthesis Cost of CNOT Circuits*,
   [arXiv:2408.07898](https://arxiv.org/abs/2408.07898): a general
   computable lower-bound framework and an exact result of `3(n-1)` for
   an `n`-cycle permutation. For `n=13` this is 36, so 19 cannot be the
   diameter of the unrestricted 13-coordinate CNOT Cayley graph. Their
   paper does not identify the present matrix as a cycle permutation or
   give its exact minimum.
3. Sodhani and Parhi, *Noise-Aware Synthesis of Quantum LDPC Encoder
   Circuits via Two-Sided Hamming Descent*,
   [arXiv:2607.04462v1](https://arxiv.org/html/2607.04462v1): Table 1
   reports 19 CNOTs for an HGP `[[13,1]]` encoder; Table 16 also reports
   19 for PyZX on that benchmark. These are achieved counts. The cited
   tables do not exclude all 18-gate programs. The exact 13-by-13 matrix
   behind their benchmark has not been identified from author-supplied
   data in this package, so identity with our printed matrix is not
   asserted.

The present draft's concrete contribution is an exact lower-bound
argument for its explicitly printed labelled matrix, coupled to an
external finite calculation and a conditional Lean theorem. It does not
claim the first 19-gate construction, an exact `n=13` diameter, a new
general CNOT synthesis asymptotic, or priority over an unlocated result.
Searches for the exact row-mask sequence did not locate a public exact
minimum proof; that negative search result is not proof of novelty.
