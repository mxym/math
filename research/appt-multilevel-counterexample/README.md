# APPT purity: counterexamples and the sharp unrestricted asymptotic

The arbitrary-dimensional purity formula in Ahiable--Kothakonda--Winter Conjecture 6.7 is false. The current primary v2 (18 September 2026) retains this conjecture and the same two candidate values. This checkpoint records a direct mathematical counterexample and the mechanism behind it. No new preprint or Release is being prepared.

## Current result: sharp unrestricted excess purity in all large-dimensional regimes

Let D=mn. The new analytic working proof establishes

    Pmax(m,n)-1/D ~ max{8, 4+D/(m^2-1)} / D^2,

uniformly over all integer pairs 2<=m<=n as D tends to infinity. This is the first nonzero excess-purity term of the **unrestricted** APPT maximum, not a bound restricted to candidate spectral shapes or an exact finite-dimensional interpolation formula.

In particular, whenever m tends to infinity and n/m tends to a finite gamma>=1,

    D^2[Pmax(m,n)-1/D] -> max{8,4+gamma}.

The coefficient is 8 for 1<=gamma<=4 and 4+gamma for gamma>=4. Square systems obey `Pmax(m,m)=m^-2+8m^-4+o(m^-4)`. For fixed m and n tending to infinity, `D*Pmax(m,n) -> m^2/(m^2-1)`.

The main working proofs are [SHARP_ASYMPTOTIC.md](SHARP_ASYMPTOTIC.md), which gives the unrestricted triangular-rearrangement upper bound, normalization and fixed-m argument, and [MULTISCALE.md](MULTISCALE.md), which constructs the separated plateau hierarchy attaining the coefficient eight. [ASYMPTOTIC.md](ASYMPTOTIC.md) supplies the broad-plateau lower family for the other branch. The upper bound applies to every APPT spectrum. The hierarchy is fixed before the dimension limit, and is only enlarged afterward; no finite-state positivity is inferred from a zero-margin limiting test.

The earlier intermediate-rank construction, one-scale graph limit, quartile bound and aspect-ratio-three bound are retained as intermediate research steps. Their previously unresolved leading-constant gaps are closed by the final triangular argument. They are not separate preprints.

Run `python3 check_mesoscopic.py` and `python3 check_triangular.py`, also with `python3 -O`, for exact finite supporting identities. These checks do not certify the infinite-dimensional compactness argument or replace the analytic all-unitary proof. This work is not Lean-formalized or externally peer reviewed. No preprint or Release has been prepared for this continuation.

Still unresolved: the exact finite-dimensional maximum, its higher-order expansion and extremizing spectra, effective convergence thresholds for the hierarchy, and whether the constructed APPT states are absolutely separable.

## Explicit state

On C^10 tensor C^38 take the diagonal density matrix

    diag(41, 17 [146 copies], 15 [233 copies]) / 6018.

Its purity is `2675/1006009`, strictly larger than BOTH conjectured candidates:

    2675/1006009 - 97/36481 = 3802/36700214329 > 0,
    2675/1006009 - 5/1881   = 1630/1892302929 > 0.

APPT is proved for every global unitary by the sum-of-squares identity in [PROOF.md](PROOF.md), not inferred from sampled unitaries. The same proof gives an infinite counterexample family for every m>=11 with n=4m. Mixing the explicit state with 1/1000 of the maximally mixed state preserves both violations and makes every unitary-orbit partial transpose uniformly positive definite.

The central construction is `(2m-5)I + 2P + 4(m-4)|v><v|`, where P is any projection and v is a unit vector in its range. It combines one high spike with a distinct plateau; neither of the two previously conjectured families includes this configuration. An exact membership test is also proved for the wider one-spike/plateau class in the specified projection-rank interval.

## Further structural result

[ASYMPTOTIC.md](ASYMPTOTIC.md) extends the counterexample to every proportional-growth regime: if m tends to infinity and n/m tends to any finite gamma>=1, explicit rational APPT spectra satisfy

    (mn)^2 [purity - 1/(mn)] -> 4+gamma,

whereas the conjectured formula gives max(4,gamma). The difference has strictly positive limiting coefficient min(4,gamma). The value 4+gamma is proved optimal within the classified one-spike/plateau subclass. That earlier subsection records the previous state of the work. The subsequent sharp unrestricted all-regime result is linked above; the earlier subclass theorem remains valid. Run `python3 check_asymptotic.py` for supporting exact parameter identities; the limits are analytic arguments, not finite tests.

## Verification and scope

```sh
python3 check.py --report verification/exact-checks.json
python3 -O check.py
```

Only the Python standard library is used. The checker verifies six dimension-uniform polynomial identities, both exact purity gaps, a rational physical boundary orbit, a strictly interior perturbation, and deliberate failures. The quantum all-unitary statement is the analytic argument; finite tests are not its substitute. This is not a new Lean result and has not undergone external peer review.

Resolved: the proposed general maximum formula is refuted. Unresolved: the true global maximum and maximizers, the smallest possible counterexample dimensions, and whether the constructed spectra are absolutely separable. The qutrit theorem and existing two-level results are not contradicted. Earlier immutable artifacts are unchanged.
