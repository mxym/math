# Proof and verification audit

Audit conducted by the primary model, 7 October 2026. No external human
review or whole-paper machine formalization is claimed.

| Step | Proof obligation | Evidence |
| --- | --- | --- |
| Norm/residual conventions | Ordered contraction and pair multiplicities retained | Paper Sections 1–2; direct ordered checker through order 7 |
| Basis change | Mix label space orthogonally and conjugate trace-free matrices; double-angle action covers all plane rotations | Written Lemma 5; exact rational rotation diagnostics |
| Nearest tensor | For fixed orthonormal basis, minimize both real weights; maximize on compact O(2) | Written Lemma 4, including attainment |
| Binary upper bound | Permutation weights at every mixed index, and PSD eigenvalue comparison | Written Theorem 1; no gap assumption |
| Quartic reduction | Nonzero polynomial implies N>0; stationarity plus exact global-circle criterion | Written Section 3.1; explicit harmonic formulas |
| Scalar quartic bound | Both factored endpoints nonnegative; division-free interpolation includes k=0 | Lean all-real-domain theorem plus five ring identities |
| Equality | Strict concavity excludes interior; endpoint zeros give exactly two coordinate forms of one orbit | Written Section 3.3; canonical tensor evaluated in Q(sqrt(3)) |
| Infinite lower family | Exact two-evaluation formula for both parities and all coordinate signs; binomial nonnegative omitted terms | Written Section 4; finite exact replay at orders 5–40 |
| Matching upper growth | Ordered sum of cubic trace inequality; two nonnegative distance bounds | Written Section 5; three Lean scalar statements |
| Sharper upper constant | Complex Hermitian orthonormal symmetrized basis; trace uses bilinear Euclidean contractions | Written Section 5.1; exact finite singular-value formula replay |

Nine exported Lean results are listed in `results/lean-axioms.txt`.
`quartic_scalar_nonnegative` verifies its domain for arbitrary real inputs;
it is not a finite grid check. `order_growth_interpolation` verifies the
scalar implication with arbitrary nonnegative A,B,E,p and B<=A. The tensor
interpretation of these hypotheses remains a written argument.

The Python checker deliberately rejects a perturbed polynomial identity
and a residual with the ordered-pair factor removed. It uses explicit
exceptions, so its checks survive optimized Python. No solver output,
floating-point optimizer or statistical evidence is a proof dependency.

All-results statement: the best binary constant has order p^(1/4), the
quartic constant is exact, and the canonical equality orbit is classified.
Limits: exact C_p for p>=5, the asymptotic leading constant, and sharp
higher-dimensional dependence are not proved. Preliminary novelty screening
does not establish priority. Previous frozen packages are unchanged.
