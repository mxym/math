# Independent replay scope and analytical trust boundary

**Date: 8 October 2026.** This is model-assisted self-review, **not** external refereeing, priority certification or a Lean formalization of the entire theorem.

## Claim-to-source map

1. **Inherited affine geometry**: product/join identities, positive cone invariant, `2<=H<=D`, rationality of states and the central binomial factor are from `preprints/005-simplex-product-optimum/v2/paper.md` (Git blob `5d5b909b5b6532910af80e17ba5abf74c0ae4c02`) and `v3/paper.md` (Git blob `27a7883cbbe99ab674565cbb9fa5daaee150678a`). The v3 source already proves a general spectral-amplification theorem; the new hierarchy gives a *strict product-depth classification, finite attainment and effective exact optimization at each level*. We do not count v3 amplification itself as new.
2. **Inherited depth-one spectral/defect inequalities**: `notes/two-layer-projection-depth-separation/paper.md` (Git blob `60787f5859b0e673d67daf233a2efdbdaba22a0e`) proves `log Q<= A D` and `log Q<=B(D-H)` for all joins of two-simplex-product blocks, including unbounded simplex dimensions. These inputs are used as **theorems**, with their own infinite-tail derivations, not as conjectures.
3. **Inherited exact depth-one Pareto fronts**: `notes/projection-first-nesting-d55/certificates/two_layer56.json` (SHA `101ffdf287f984965c941b1f98f93de89ae4a3bd0d4e796f02558a8039cb3d9f`) and `notes/projection-persistent-nesting-gap/certificates/extension57to85.json` (SHA `caaa1ced19c2a2511e3537a8a4851d0d2e5bcb51d8b857990360c4fa2efcdb8d`) together contain all exact depth-one fronts required through dimension 79. Their original checkers establish production pointers, completeness and Pareto closure independently of this note. The most recent previously published exact two-layer checker is `notes/projection-persistent-nesting-gap/code/check.py` (Git blob `0a34b5cbde08ff3f73b3c2bbebb3981cda2f5dfb`); the new read-only workflow reruns it before replaying the new theorem. The new code hash-pins both input files and rejects alterations.
4. **New mathematical hierarchy**: `paper.md` Sections 3–4 prove a sublinear uniform bound on the product multiplier, a strict spectral amplifier with an explicit join count, finite attainment at every depth, and a provably terminating recursive exact search. These are *paper-level proofs*, not merely code results. In particular the all-depth effective theorem does not depend on the finite second-level search.
5. **New exact second-level classification**: `paper.md` Sections 5–7 partition all integer factor pairs into two analytic infinite tails (`r>=12, r+s>=63` and `r<=11,s>=80`) and an exhaustive finite complement. A 12-line analytic tail certificate (one `n=63` anchor and eleven small-factor anchors, plus global constants) is checked by rational atanh logarithm bounds. The finite core is `1,214` dimension splits and `2,770,504` candidate pairs, all evaluated with exact `Fraction` multiplication by an independent checker. Only split `(21,21)` and the state indices `(48,48)` tie the winning bound; every other candidate is strictly below it. The separate producer also saves every split's rational winner in `certificates/finite_splits.tsv`, and the checker independently reproduces and checks every entry.
6. **New depth-three strict example**: the same exact checker evaluates the dimension-170 nested product `Y=(P*P)x(P*P)` and checks `Q(Y)^43>Q(P)^171`, which proves strict improvement without claiming a depth-three optimum.

## Computation versus mathematical deduction

There is no use of `numpy`, `scipy`, floating-point comparisons, randomized solvers, or `assert` statements in the published checker or certificate producer. Positive rationals are represented by arbitrary-precision integers and `Fraction`. The finite core uses only integer powers and fraction comparisons. The logarithmic constants in the analytic tail are enclosed using a finite rational atanh series with an explicit upper tail bound. The pi enclosure is rechecked from the rational Machin formula. Both Python modes are required to produce byte-identical output.

The infinite-dimensional theorem rests on the analytical *derivative inequalities, Robbins estimates and hierarchical induction* in the manuscript, not on checking many finite `r,s`. The public trust boundary also includes the previously proved 005 geometric identity and two depth-one block inequalities. A numerical PASS line without those written inputs is insufficient to establish the complete theorem.

## Reproduction and controls

From repository root:

```sh
python3 notes/projection-persistent-nesting-gap/code/check.py
python3 notes/projection-product-depth-hierarchy/code/check_depth2.py
python3 -O notes/projection-product-depth-hierarchy/code/check_depth2.py
python3 notes/projection-product-depth-hierarchy/code/negative_controls.py
(cd notes/projection-product-depth-hierarchy && sha256sum -c SHA256SUMS)
```

The negative tests corrupt (i) the certified pi lower endpoint, (ii) the inherited depth-one maximizing block value, (iii) the parent Pareto-source SHA, and (iv) one finite split's stored exact optimum. All four must trigger an explicit RuntimeError even under optimized Python. The separate producer may regenerate all 1,214 winning split records. `results/replay.txt`, `results/replay-optimized.txt`, `results/producer.txt` and `results/negative.txt` are frozen comparison artifacts.

## Remaining open issues

The hierarchy does **not** identify the full spectral optimum `lambda_*`, nor compute a formula for all finite-depth `lambda_k`. Its exact algorithm has proved termination but possibly enormous finite runtime for larger `k`. The depth-three product is a strict witness only. No claim about all convex bodies, all equality shapes, the optimum relative convergence speed, or worldwide priority is made.
