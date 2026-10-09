# Pure qutrit ECQC: paper-to-Lean map

Baseline: mxym/math main 2d67375906d729862d4eb085186a5fd5670ef390.
The latest README, SOLVED_PROBLEMS, RESEARCH, formalizations, and open Gaussian PRs were checked before choosing this unformalized direction. No tracked AGENTS.md exists at this baseline. Existing frozen packages are not modified.

| Paper object / argument | Required proof | Lean module / endpoint | Status |
|---|---|---|---|
| QUTRIT_EXACT.md, definitions | Actual complex density operators, partial traces, spectral von Neumann entropy, Born expectations | QuantumCore | in development |
| Eq. sigma3 / R3 | Explicit normalized pure vector; positive semidefinite trace-one density; actual partial traces; quadratic operator identities | QutritState | in development |
| Four complete MUBs | Orthonormal columns and squared overlaps 1/3, no assumed basis interface | QutritMUB | in development |
| Born tables | Actual density expectations equal the stated rational table in all four bases | QutritBorn | in development |
| Entropies | Spectral entropy from actual eigenvalues; Shannon entropies of actual Born outcomes | QutritEntropy | in development |
| Original ECQC minimum | Every retained three-setting sum is 3 log 2; minimum equals that value; Q=2 log 2; strict violation | ECQC | in development |

The selected target is a full proof of the explicit pure qutrit counterexample, not the entire prime-dimensional classification paper. Holevo, optimality of the 3/2 ratio, the five-dimensional examples, all-prime analytic estimates, and full-Schmidt-rank witnesses are not inputs and are outside the first certificate.

No Lean verification is claimed until current-source compilation and the specified audit have succeeded. The usual logical axioms propext, Classical.choice, and Quot.sound are permitted; sorryAx, native_decide, custom axioms, and unproved spectral/Born bridges are not.
