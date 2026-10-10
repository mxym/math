# APPT purity: counterexamples and the sharp unrestricted asymptotic

The arbitrary-dimensional purity formula in Ahiable--Kothakonda--Winter Conjecture 6.7 is false. The current primary v2 (18 September 2026) retains this conjecture and the same two candidate values. This checkpoint records a direct mathematical counterexample and the mechanism behind it. The counterexample, unrestricted asymptotic law and exact rectangular theorem are now incorporated in the [expanded APPT preprint](../../preprints/appt-purity-unified-2026-10/README.md). The earlier immutable qutrit proof release remains unchanged.

## New entropy law and an outlier transition at Renyi order two

[ENTROPY_ASYMPTOTIC.md](ENTROPY_ASYMPTOTIC.md) determines the leading UNRESTRICTED minimum-entropy deficit for every fixed finite Renyi order alpha>=1. With D=mn and n/m->gamma>=1 as m grows,

    D[log D-min_APPT S_alpha] -> A_alpha+(alpha/2)max{4,gamma},
    A_alpha=2alpha                    for 1<=alpha<=2,
    A_alpha=(3^alpha-1-2alpha)/(alpha-1) for alpha>=2.

The joint-growth equivalent is uniform in n>=m. A separate explicit fixed-m limit combines with it to give an equivalent uniform over all dimension pairs as total dimension grows. At alpha=1 this says `D[log D-min S] -> max(4,2+gamma/2)`; at alpha=2 it agrees with the established purity theorem. These are first nonzero asymptotic deficits, not exact finite-dimensional interpolation formulas.

The same proof classifies the fixed-height outlier structure of EVERY entropy near-minimizer at fixed finite gamma. For 1<=alpha<2 it is equivalent to purity near-maximality AND `||D rho-I||_op->0`. For alpha>2 it is equivalent to purity near-maximality, `D lambda_1->3`, and `max_{i>=2}|D lambda_i-1|->0`. At alpha=2 purity alone is required. Neither conclusion assumes a spectral-shape ansatz, and the result is for fixed alpha rather than alpha varying with dimension.

The upper entropy bound uses a new physical Schmidt-star assignment centered at the LEAST eigenvalue and a nonlinear head inequality; a quadratic Taylor expansion at arbitrary negative outliers would be false. [FLAT_EXTREMIZERS.md](FLAT_EXTREMIZERS.md) supplies actual APPT near-maximizers whose ENTIRE normalized spectrum tends to one, and reflected pairs about I/D with equal purity. [TWO_ENDED_GRAPH_LIMIT.md](TWO_ENDED_GRAPH_LIMIT.md) proves the underlying exact graph limit and finite-depth optimization for simultaneous low-rank and high-rank hierarchies, including their different energy-order constraints.

A separate finite rational example on 50x200, `diag(861,330[4899],319[5100])/3244431`, has an all-unitary SOS positivity proof and entropy strictly below all candidates for the original inscribed-polytope minimum. The logarithm gaps are enclosed by exact rational intervals. Its 1/1000 maximally mixed perturbation preserves the entropy violation and has uniformly positive orbit partial transposes.

These new results are research notes, not additional preprints and not retroactively certified by the earlier Lean proof or concurrent manuscript. Run `python3 check_two_ended.py` and `python3 check_entropy.py`, also with `python3 -O`, for exact supporting calculations. Finite checks do not replace the graph compactness proof, all-unitary argument, or entropy optimization. The range 0<alpha<1, exact finite entropy minima, effective hierarchy thresholds, and absolute separability remain separate research questions.

## New exact and structural results

[EXACT_RECTANGULAR.md](EXACT_RECTANGULAR.md) proves the EXACT unrestricted maximum for every m>=3 and n>=m^3-m-2:

    Pmax=[mn(m-1)^2+4mt]/[mn(m-1)+2t]^2, t=ceil((m-1)n/2).

All maximizing spectra are classified: t entries m+1 and mn-t entries m-1, divided by their trace. The cutoff is sufficient for APPT and sharp for the one-Schmidt-test outer-polytope argument, not claimed to be the smallest actual onset. This is independent of the asymptotic compactness proof.

[PHASE_RIGIDITY.md](PHASE_RIGIDITY.md) determines necessary structure of EVERY near-maximizing sequence at a fixed aspect ratio gamma. The empirical rescaled eigenvalues m(mn*lambda_i-1) converge in W1 to zero when gamma<4, and to equal masses at -1 and +1 when gamma>4. At gamma=4 exactly these two subsequential limits are possible and both occur. A new positive-semidefinite matrix inequality excludes intermediate critical profiles. The theorem also fixes the allocation of paired-gap square mass and explains the second moment carried by rare outliers.

[OPTIMAL_HIERARCHY.md](OPTIMAL_HIERARCHY.md) gives an EXACT multiscale graph limit and solves the leading optimization for each fixed J of lacunary intermediate-rank plateaus plus a spike. Its sharp centered-purity coefficient is 8-d_J, where d_0=4 and d_j=d_{j-1}-d_{j-1}^2/8; the optimal limiting scale energies are unique. The deficit is asymptotic to 8/J. This model-specific depth law is not a claim about all conceivable finite-level spectra.

Run `python3 check_rectangular.py` and `python3 check_structure.py`, also with `python3 -O`, for exact supporting calculations. The analytic proofs are not Lean-formalized or externally peer reviewed. Phase rigidity and fixed-hierarchy optimization remain research notes and are not claimed as theorems of the expanded preprint.

## Current result: sharp unrestricted excess purity in all large-dimensional regimes

Let D=mn. The new analytic working proof establishes

    Pmax(m,n)-1/D ~ max{8, 4+D/(m^2-1)} / D^2,

uniformly over all integer pairs 2<=m<=n as D tends to infinity. This is the first nonzero excess-purity term of the **unrestricted** APPT maximum, not a bound restricted to candidate spectral shapes or an exact finite-dimensional interpolation formula.

In particular, whenever m tends to infinity and n/m tends to a finite gamma>=1,

    D^2[Pmax(m,n)-1/D] -> max{8,4+gamma}.

The coefficient is 8 for 1<=gamma<=4 and 4+gamma for gamma>=4. Square systems obey `Pmax(m,m)=m^-2+8m^-4+o(m^-4)`. For fixed m and n tending to infinity, `D*Pmax(m,n) -> m^2/(m^2-1)`.

The main working proofs are [SHARP_ASYMPTOTIC.md](SHARP_ASYMPTOTIC.md), which gives the unrestricted triangular-rearrangement upper bound, normalization and fixed-m argument, and [MULTISCALE.md](MULTISCALE.md), which constructs the separated plateau hierarchy attaining the coefficient eight. [ASYMPTOTIC.md](ASYMPTOTIC.md) supplies the broad-plateau lower family for the other branch. The upper bound applies to every APPT spectrum. The hierarchy is fixed before the dimension limit, and is only enlarged afterward; no finite-state positivity is inferred from a zero-margin limiting test.

The earlier intermediate-rank construction, one-scale graph limit, quartile bound and aspect-ratio-three bound are retained as intermediate research steps. Their previously unresolved leading-constant gaps are closed by the final triangular argument. They are not separate preprints.

Run `python3 check_mesoscopic.py` and `python3 check_triangular.py`, also with `python3 -O`, for exact finite supporting identities. These checks do not certify the infinite-dimensional compactness argument or replace the analytic all-unitary proof. The higher-dimensional work is not Lean-formalized or externally peer reviewed. Its final unrestricted law, fixed-dimension limit and rectangular theorem are included in the expanded preprint; the earlier working notes are retained as dated research history.

Still unresolved: the finite-dimensional maximum outside the proved rectangular region, the smallest true rectangular onset, higher-order expansions and the complete outlier/level classification, effective convergence thresholds for the hierarchy, and absolute separability of the new families.

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

The proposed general formula is refuted. Its broad-plateau value is now proved exactly, with all maximizing spectra, in the rectangular region stated above. The remaining finite dimensions, minimal counterexample dimensions, and absolute separability remain unresolved. The qutrit theorem and existing two-level results are not contradicted. Earlier immutable artifacts are unchanged.
