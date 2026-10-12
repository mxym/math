# Proof dependencies, audit status and reproducibility

**Review date:** 2026-10-08. This is a model-assisted author self-audit, **not** an external peer review, formal mathematical verification by Lean, or a novelty/priority certification.

## Statement audited

We give a finite exact state-space certificate for the **point-generated, invertible-affine product/join class** in every dimension through 48. The theorem is deliberately restricted: no claim is made for all convex bodies, and no extrapolation past dimension 48 is made from the finite certificate. Its all-dimensional part is the *correctness of the recursive Pareto optimization algorithm*, not an all-dimensional closed-form solution.

## Dependencies that the verifier does not prove

1. The exact affine projection-body product and join identities, plus the cone invariant, are inherited from entry 005 v2: `preprints/005-simplex-product-optimum/v2/paper.md`, Git blob `5d5b909b5b6532910af80e17ba5abf74c0ae4c02`. Earlier OpenAI/math family 088 proves the original two-simplex Cartesian-product mechanism. Our new proof directly derives all Pareto monotonicity and induction arguments from the imported identities.
2. Ordinary algebra about finite tree decompositions, affine invariance of the states, and the fact that nontrivial operations strictly increase dimension is in [`paper.md`](paper.md). This is a conventional written proof, not a proof-assistant theorem.
3. Python integer arithmetic and `fractions.Fraction` are trusted. The exact checker uses no floating point, external solver, random choices, compiled optimizer, or assertion-dependent decisions.

## Independent replay and certificate semantics

Run from the root:

```sh
python3 notes/exact-product-join-finite-optima/code/check.py
python3 -O notes/exact-product-join-finite-optima/code/check.py
python3 notes/exact-product-join-finite-optima/code/negative_controls.py
cd notes/exact-product-join-finite-optima && sha256sum -c SHA256SUMS
```

The two checker modes produced **byte-identical outputs** and agreed with the pinned log. The verifier checked exactly **6,494** attainable frontier states and **1,956,775** generated binary candidates; each candidate must be dominated by an actual saved front state. It then computed all 48 sharp fractions from the objective `H*Q/(d+1)`, checked explicit witnesses' construction grammars, and confirmed the old dimension-14 maximum `385/384`. The dimension-48 constant is additionally reconstructed as `27/49*(175/128)^3*(189/128)^2`, with exact factorial checks of both product blocks.

Three negative controls intentionally corrupt (a) a state value, (b) a necessary dominating frontier element, and (c) a reported sharp fraction. All cause an explicit failure at the appropriate early stage. This tests the certificate trust boundary, not independence of the inherited geometric lemmas.

Optional source-independent regeneration with the producer can compare output bytes with the frozen certificate, but it is the *separate checker* that certifies the finite tree grammar. The proof of closure for all grammars is mathematical induction in Section 3 of `paper.md`.

## New versus old

- **Inherited:** underlying affine-geometric calculus, and exact maximum through dimension 14 from 005 v2.
- **New:** an all-dimensional coordinatewise dominance principle for the two-state calculus, a compact *exact* dynamic program on nondominated fronts, sharp extrema for dimensions 15–48, proof that an optimal join of simplex products exists in each of the first 48 dimensions, and the explicit sharp 48-dimensional value exceeding three times the simplex.
- **Still open:** dimensions beyond the exact certificate, classification of all equality shapes, optimum unrestricted convex-body value, and the point-generated class's full asymptotic constant. Any apparent growth law or small frontier-size pattern beyond the checked range is experimental only.
