# Nonqubit finite logarithmic order band: proof obligations

Prepared before the manuscript, 14 October 2026. Same APPT programme; no new
independent major-conjecture count or expanded Lean audit.

| Statement | Actual-object bridge | Verification boundary |
| --- | --- | --- |
| N1: every m≥3 actual APPT spectrum obeys λ_2≤5/[2(D+3)] | Convex average of genuine unitary conjugates flattens the first two and the tail; a rational three-Schmidt negative test bounds the resulting top/tail ratio. | Necessary physical inequality, not a presumed equivalence of a scalar relaxation. The stronger sharp second cap is not required. |
| N2: every actual m⊗n, 3≤m≤n, α≥32log D+1 has exact pole entropy minimum and only pole equality | Physical rank-two outer condition; its near-cap bottom-three trace stability; N1 gives a uniform tail gap; complete near/far real-power estimates. | Ordinary finite theorem, constant32 sufficient, not optimal. Pole ASEP endpoint credited and supplied by the prior explicit finite product proof. |
| N3: dimension-only nonqubit APPT cutoff has order Θ(log D) | Actual3⊗n projection-only densities with integer rank floor(D/α), α=c log D; lower competing moments for every c<1/log(3/2). | APPT lower bound only. No ASEP status is assumed for the projection family; no sharp cutoff constant asserted. |
| N4: exclusion of a false extension to qubits | Actual2⊗2048 rank-two projection, α=300, exact Bernoulli lower ratio105/82>1 while300>32log4096+1. | Actual all-unitary APPT negative control for the missing m≥3 condition. |

The old rank-two outer condition, the local rational3⊗3 partial-transpose
test and the ASEP pole are explicitly inherited ordinary inputs, with their
needed arguments rederived. Earlier471/558-line records do not review this
new manuscript. No new Lean source, build, axiom, root or kernel coverage
is introduced. Full new internal reading will be version-bound separately.
