# Actual theorem and proof/certificate coverage

| Claim | Proof source | Exact verification |
| --- | --- | --- |
| Permanent-only 3/2 and determinant 1 endpoints for arbitrary complex 4×4 A | PAPER §2, elementary two-row Laplace/Cauchy proof; classical attribution | Analytic proof; no old Lean log relabeled |
| Actual original row tensor and permanent/determinant overlap | PAPER §3 definitions | Explicit 24-term tensor and all index conventions in checker |
| Boundary i(3/2−1/√3) sharp inequality, all complex A | PAPER §3, exact sum of partially transposed positive Gram matrices on product row tensors | Seven exact LDL identities, strict ordered-field positive pivots, complete 65,536-entry matrix identity |
| All positive and negative imaginary parameters | PAPER §4, convexity and Hadamard extension; entrywise conjugation | Analytic proof for continuum of t; not inferred from finite tests |
| Greatest norm value and actual attainment | PAPER §5, flat matrix and explicit Fourier3 direct sum | Analytic six-term witness expansions |
| Complete boundary equality for all actual complex matrices | EQUALITY §2–5, actual Gram kernel, support rigidity and three-row equality | Actual first Gram difference matrix; all 65,536 support masks; exact three-row determinant and distinct singular values |
| Complete equality classification for every real t, including transitions and zero rows | EQUALITY §1, §6; interpolation and determinant extension | Universal written proof, with exact boundary-algebra checks |
| Full theorem and equality classification | PAPER §1–5 and EQUALITY combined | Complete written proof and exact algebraic certificates; **no Lean formalization** |

All numerical discovery programs, SOS/PPT optimization relaxations and solver
status are outside the proof premises. The certificate is an explicit matrix
identity whose product-vector implication is proved, not a substitute quantum
model for the original A. The full complex coefficient plane and higher orders are outside this
theorem's scope; all imaginary-axis equality cases are included.
