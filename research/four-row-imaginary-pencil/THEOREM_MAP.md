# Actual theorem and proof/certificate coverage

| Claim | Proof source | Exact verification |
| --- | --- | --- |
| Permanent-only 3/2 and determinant 1 endpoints for arbitrary complex 4×4 A | PAPER §2, elementary two-row Laplace/Cauchy proof; classical attribution | Analytic proof; no old Lean log relabeled |
| Actual original row tensor and permanent/determinant overlap | PAPER §3 definitions | Explicit 24-term tensor and all index conventions in checker |
| Boundary i(3/2−1/√3) sharp inequality, all complex A | PAPER §3, exact sum of partially transposed positive Gram matrices on product row tensors | Seven exact LDL identities, strict ordered-field positive pivots, complete 65,536-entry matrix identity |
| All positive and negative imaginary parameters | PAPER §4, convexity and Hadamard extension; entrywise conjugation | Analytic proof for continuum of t; not inferred from finite tests |
| Greatest norm value and actual attainment | PAPER §5, flat matrix and explicit Fourier3 direct sum | Analytic six-term witness expansions |
| Full theorem | PAPER §1–5 combined | Complete written proof and exact algebraic certificate; **no Lean formalization** |

All numerical discovery programs, SOS/PPT optimization relaxations and solver
status are outside the proof premises. The certificate is an explicit matrix
identity whose product-vector implication is proved, not a substitute quantum
model for the original A. The full complex coefficient plane, equality cases
and higher orders are outside this theorem's scope.
