# APPT multilevel counterexample: research checkpoint

The arbitrary-dimensional purity formula in Ahiable--Kothakonda--Winter Conjecture 6.7 is false. The current primary v2 (18 September 2026) retains this conjecture and the same two candidate values. This checkpoint records a direct mathematical counterexample and the mechanism behind it. No new preprint or Release is being prepared.

## Current result: the sharp balanced maximum asymptotic

The unrestricted APPT maximum now satisfies

    Pmax(m,m) = 1/m^2 + 8/m^4 + o(m^-4).

More generally, `(mn)^2[Pmax(m,n)-1/(mn)] -> 8` whenever m tends to infinity and n/m tends to one. The upper bound applies to **every APPT spectrum**; the lower bound uses a hierarchy of rational spectral plateaus with an eventual all-unitary positivity proof. The number of scales is fixed before the dimension limit and is only increased afterward. This is a proved analytic asymptotic, not an exact finite-dimensional maximum or a new Lean result.

The working proofs are:

- [Unrestricted variance bound](UNRESTRICTED_BOUND.md): physical paired-eigenvalue tests, star and rectangular rearrangements, and a bound for arbitrary spectra.
- [The multiscale construction and matching constant](MULTISCALE.md): a uniform graph estimate whose limiting additive-label graph is a forest; this closes the balanced coefficient at 8.
- [Intermediate-rank plateau](MESOSCOPIC.md) and [sharp four-level sector](GRAPH_LIMIT.md): the steps showing why the earlier coefficient 4+gamma is not an unrestricted upper bound.

For a fixed aspect ratio gamma>=1 the current bounds are

    max(8,4+gamma) <= liminf D^2[Pmax-1/D]
                     <= limsup D^2[Pmax-1/D]
                     <= min(4+4gamma,8+max(1,gamma-1)),  D=mn.

They agree at gamma=1. The exact constant for gamma>1 and the exact finite-dimensional maximum are still unresolved here. Run `python3 check_mesoscopic.py` and `python3 -O check_mesoscopic.py` for supporting exact finite calculations. Those checks do not certify the compactness and all-unitary arguments by themselves. No further preprint or Release is prepared.

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

whereas the conjectured formula gives max(4,gamma). The difference has strictly positive limiting coefficient min(4,gamma). The value 4+gamma is proved optimal within the classified one-spike/plateau subclass. That earlier subsection records the previous state of the work. The subsequent unrestricted bounds and the sharp balanced constant 8 are linked above; the subclass theorem remains valid. Run `python3 check_asymptotic.py` for supporting exact parameter identities; the limits are analytic arguments, not finite tests.

## Verification and scope

```sh
python3 check.py --report verification/exact-checks.json
python3 -O check.py
```

Only the Python standard library is used. The checker verifies six dimension-uniform polynomial identities, both exact purity gaps, a rational physical boundary orbit, a strictly interior perturbation, and deliberate failures. The quantum all-unitary statement is the analytic argument; finite tests are not its substitute. This is not a new Lean result and has not undergone external peer review.

Resolved: the proposed general maximum formula is refuted. Unresolved: the true global maximum and maximizers, the smallest possible counterexample dimensions, and whether the constructed spectra are absolutely separable. The qutrit theorem and existing two-level results are not contradicted. Earlier immutable artifacts are unchanged.
