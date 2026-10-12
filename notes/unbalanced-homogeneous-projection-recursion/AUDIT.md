# Proof and reproducibility audit

Date: 2026-10-07. Scope: **model-assisted self-review**, not independent human referee review, Lean formalization or novelty certification.

## Claim/dependency map

- The projection-body product identity, join identity, affine cone parameter, and simplex input are quoted from **005 v2**, `preprints/005-simplex-product-optimum/v2/paper.md` (Git blob `5d5b909b5b6532910af80e17ba5abf74c0ae4c02`). The original product mechanism is also in OpenAI/math family 088; the latter does not state our classification.
- The certified lower endpoint of the unique winning orbit is quoted from **005 v5**, `preprints/005-simplex-product-optimum/v5/paper.md` (Git blob `382dc13ca633b76d9663ec7205d7d2556b6f88fe`) and its exact checker (blob `9b2ce977dc8501ab1d63fdd862ee342c2748bc61`). We separately reran that standard-library checker and observed its PASS report, including the level-6 integer inequality.
- The new result uses these pinned inputs; all independent-arity limit formulae, global majorants, infinite parameter range reductions, and finite comparisons are derived in `paper.md`, not attributed to the upstream source.

## Coverage matrix

The proof partitions positive integers into: (i) `m=1` or `k=1`; (ii) `m,k>=2,p>=20`; (iii) `m>=20,2<=k,p<=19`; (iv) `3<=m<=19,k>=20,p<=19`; (v) `m=2,k>=20,p<=19`; and (vi) finite `2<=m,k<=19,p<=19`. Case (vi) retains a single candidate `(2,2,5)`; the other **6,155** triples are excluded by strict upper bounds. No finite scan is used to infer an infinite statement without a preceding monotonicity or global-envelope argument.

The finite certificate checks continuous real tails through inequalities, not by sampling real arguments. For `p>=20`, it validates the derivative and start-point checks and the paper proves uniform concavity; for `m>=20`, it uses monotonicity in `m`; for `k>=20`, it uses explicit endpoint maxima and monotonicity in `k`. The exceptional `m=2,k>=20` tail uses a tangent inequality with verified rational preconditions.

## Trust boundary

All decisions of `checker.py` are exact integers or Python `Fraction`. Logarithm endpoints are rational atanh-series intervals with an analytic remainder; powers of two are normalized exactly. The pi enclosure is independently replayed using alternating arctangent bounds plus the elementary Machin identity. No external solver, random search or floating arithmetic is used in the proof certificate. Standard analytic Robbins--Stirling bounds and the geometric calculus are **paper-level inputs**, not formalized by this program.

Run `python3 checker.py` and `python3 -O checker.py` in this directory (or use the root-relative commands in `README.md`). Both produce the same eight-line report. An out-of-scope change to an inherited calculus lemma could invalidate the mathematical conclusion even if the finite checker remained green; the inherited proof sources are therefore pinned above. There is no claim of independent proof-assistant coverage for the new infinite statements.

## Negative controls

`python3 negative_controls.py` deliberately supplies a false lower bound for pi, a false inherited winning benchmark, and an overstrong competitor ceiling. All three must be rejected by explicit exceptions. The recorded output is in `negative_controls.txt`; these are control-flow tests rather than a substitute for proof.

## Residual research gap

Only fixed homogeneous arities and simplex seeds are optimized. Alternating/periodic arities, non-simplex starting bodies and nonhomogeneous product/join trees remain outside Theorem 1; the entire recursive class has an independent upper bound `Gamma_C <= exp(1049/1000)` from the mixed-Bellman supplement, not equality. Nothing here asserts the unrestricted projection-body maximizer or a first-in-literature result.
