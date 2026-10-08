# Mathematical/reproducibility audit — permanent 005 nesting gap

**Date: 8 October 2026.** Model-assisted author self-review, *not* external peer review, comprehensive novelty assessment or whole-paper Lean formalization.

## Source and claim boundaries

1. **Affine geometric calculus (inherited).** The product/join formula for `D=d+1`, `H=1/a` and `Q=aR/g(d)` is from `preprints/005-simplex-product-optimum/v2/paper.md`, Git blob `5d5b909b5b6532910af80e17ba5abf74c0ae4c02`, which acknowledges upstream OpenAI/math family 088 and earlier projection-body literature. This note does not re-prove the convex-geometric identity.
2. **All-dimensional sharp two-layer block inequalities (inherited).** The exactly proved inequalities `log Q <= log(189/128)*D/11` and `log Q <= log(175/128)*(D-H)/4` are in `notes/two-layer-projection-depth-separation/paper.md`. They are used, and cited explicitly, in the analytic large-dimension envelope. The new arithmetic checker alone would *not* prove the inequalities for all simplex parameters without that analytic proof.
3. **Sharp 55D maxima (inherited).** `notes/projection-first-nesting-d55/paper.md` and its all-tree (`code/check_all_tree.py`) and two-layer (`code/check_two_layer.py`) exact replayers establish the complete maxima used to define the sharp constant. The parent two-layer certificate `certificates/two_layer56.json` is SHA-256 pinned to `101ffdf287f984965c941b1f98f93de89ae4a3bd0d4e796f02558a8039cb3d9f`. The parent checker source is pinned to `f6ce470365577580d3f94663b486c4a52ea878e09b59c43a11b7a3da4e5becd6`; the prior all-tree extension source is pinned to `7cb6b097984163b471ead5ac08fca71fb7425c489ba372d99f3809269552b60c`. The new checker reruns the previous two-layer checker and validates the original complete-tree optimal fraction against its pinned source. To additionally replay the prior full-tree *closure* rather than only check its source identity, run its separate checker (listed below).
4. **New finite work.** `code/build.py` is an exact producer for 29 new two-layer Pareto levels and thirty nested witnesses. The *separate* `code/check.py` checks all state pointers and coordinates, Pareto antichains, **all 2,837,399 one-step closure candidates** of the extended two-layer grammar, the sharp objective for every new dimension, and thirty explicit strictly rational witness-to-optimum comparisons. No optimizer-only claim is used as a theorem.
5. **New infinite work.** A direct one-variable argument optimizes the prior two sharp block inequalities for every `D>=24`; integer-power checks prove `27/50 < t_* < 11/20` and rational atanh terms prove the necessary derivative sign. In every `D>=86` an explicit `K_2` body is joined with `k` copies of `T5×T5` and `0<=r<=10` points. Monotonicity in `k` is proved analytically, and eleven **strict integer/Fraction inequalities** establish a relative factor exceeding `209/200`, uniformly for the entire infinite tail. A second dimension-filling construction joins copies of the 85-dimensional body directly and proves an explicit exponential relative bound `ratio > (1009/1000)^(d-84)/45` for every `d>=85`, using two further exact integer/fraction inequalities. Finite enumeration is **not** being substituted for the infinite tail proof.

## Full public replay (repository root)

```sh
# Original exact complete-tree optimum at d=55 (independent previous result):
python3 notes/projection-first-nesting-d55/code/check_all_tree.py

# New independent certificate + its inherited exact two-layer base:
python3 notes/projection-persistent-nesting-gap/code/check.py
python3 -O notes/projection-persistent-nesting-gap/code/check.py

# Hostile controls and frozen hashes:
python3 notes/projection-persistent-nesting-gap/code/negative_controls.py
(cd notes/projection-persistent-nesting-gap && sha256sum -c SHA256SUMS)
```

`check.py` makes every proof decision with Python integers and `fractions.Fraction`, not decimal comparisons, `assert`, floating approximations, SAT solver assumptions or network services. Logarithms in the **written analytic argument** are compared by *exact integer powers* and a positive atanh-series lower bound; these rational premises are replayed by the checker. Normal and `python -O` modes give byte-identical reports. Four hostile mutations (fake attained state, deleted required Pareto point, false tail potential, false parent hash) all cause an explicit rejection.

Optional reproducibility of the producer:

```sh
python3 notes/projection-persistent-nesting-gap/code/build.py
# After regenerating, verify SHA256SUMS again. No third-party packages.
```

The 30 finite witness ratios and their selected seed/filler pointers are also exported in `results/finite_witnesses.tsv` and byte-checked against the exact certificate by the checker.

## New conclusions versus imported results

**Imported:** first mandatory nesting at dimension 55, its exact two sharp rational maxima, exact two-layer block inequalities, and the 85D binary-orbit witness.

**New:** a **sharp multiplicative lower bound for the ratio of the full-tree and two-layer extrema simultaneously over *all dimensions* d>=55**, attained only in dimension 55; a strict factor above `101/100` at all `d>=56`; a strict factor above `209/200` at all `d>=85`, plus explicit exponential divergence of the ratio at rate `1009/1000` with rational prefactor `1/45`; a finite extension of the entire two-layer sharp-value certificate to dimension 84; and a uniform eleven-residue tail theorem covering infinitely many dimensions.

This does **not** compute individual full-tree sharp extrema after dimension 55, classify all maximizing shapes, solve the asymptotic optimal rate of the full recursive class, or establish a result for unrestricted convex bodies. No priority or human-referee claim is made.
