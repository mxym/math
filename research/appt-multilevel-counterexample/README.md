# APPT multilevel counterexample: research checkpoint

The arbitrary-dimensional purity formula in Ahiable--Kothakonda--Winter Conjecture 6.7 is false. The current primary v2 (18 September 2026) retains this conjecture and the same two candidate values. This checkpoint records a direct mathematical counterexample and the mechanism behind it. No new preprint or Release is being prepared.

## Explicit state

On C^10 tensor C^38 take the diagonal density matrix

    diag(41, 17 [146 copies], 15 [233 copies]) / 6018.

Its purity is `2675/1006009`, strictly larger than BOTH conjectured candidates:

    2675/1006009 - 97/36481 = 3802/36700214329 > 0,
    2675/1006009 - 5/1881   = 1630/1892302929 > 0.

APPT is proved for every global unitary by the sum-of-squares identity in [PROOF.md](PROOF.md), not inferred from sampled unitaries. The same proof gives an infinite counterexample family for every m>=11 with n=4m. Mixing the explicit state with 1/1000 of the maximally mixed state preserves both violations and makes every unitary-orbit partial transpose uniformly positive definite.

The central construction is `(2m-5)I + 2P + 4(m-4)|v><v|`, where P is any projection and v is a unit vector in its range. It combines one high spike with a distinct plateau; neither of the two previously conjectured families includes this configuration. An exact membership test is also proved for the wider one-spike/plateau class in the specified projection-rank interval.

## Verification and scope

```sh
python3 check.py --report verification/exact-checks.json
python3 -O check.py
```

Only the Python standard library is used. The checker verifies six dimension-uniform polynomial identities, both exact purity gaps, a rational physical boundary orbit, a strictly interior perturbation, and deliberate failures. The quantum all-unitary statement is the analytic argument; finite tests are not its substitute. This is not a new Lean result and has not undergone external peer review.

Resolved: the proposed general maximum formula is refuted. Unresolved: the true global maximum and maximizers, the smallest possible counterexample dimensions, and whether the constructed spectra are absolutely separable. The qutrit theorem and existing two-level results are not contradicted. Earlier immutable artifacts are unchanged.
