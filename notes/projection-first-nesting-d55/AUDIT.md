# Audit: first necessary nesting dimension d=55

**Date:** 2026-10-08. **Type:** model-assisted reproducibility and mathematical self-review. This is not external human peer review, an all-theorems Lean formalization or a literature-priority assertion.

## Dependency chain

1. The geometry is the two-state product/join calculus from `preprints/005-simplex-product-optimum/v2/paper.md` (pinned Git blob `5d5b909b5b6532910af80e17ba5abf74c0ae4c02`). Its simplex-product prototype derives from the credited `openai/math` family 088.
2. The exact Pareto-domination theorem and **all dimensions 1–48** come from `notes/exact-product-join-finite-optima/`, with the **exact public SHA-256** of `certificates/frontiers48.json` equal to `975c4cc5c37f309426d57661e8b5d4dcb45fb2811c6a000da3204faeb4ddea38`. That source has its own checker which reconstructs every original frontier and candidate.
3. Our `all_tree49to55.json` extends *that exact source*, not a free-floating unverified list. Its independent checker proves the full new binary-operation closure and every construction pointer, checking **3,066** new frontier states and **2,523,858** operations over dimensions 49–55.
4. A separate two-layer producer/checker pair uses the all-atom grammar `point` or `T_p×T_q` and independent `H,Q` calculations, with **5,611** attained states and **430,360** exact point/block additions for dimensions up to 55.
5. The two checkers compare rational maxima across every dimension 49–54 and at 55 (strict inequality). The dimension-55 nested body and two-layer winner are re-evaluated from displayed exact rational formulas, not merely trusted construction pointers. Thus the *first necessity* claim follows from the previous 1–48 theorem plus the new 49–55 and two-layer checks.

## Mathematical assumptions outside the code

The Pareto soundness proof requires monotonicity of exact geometric product/join identities and induction on finite expression trees. This is proved in `paper.md` Sections 1–4. The checker trusts Python exact integers/Fraction and the pinned geometric source; it cannot itself independently prove the imported projection-body identities or the underlying real convex geometry. No floating-point inequality, interval-rounded optimization, external solver or disabled `assert` is used to accept the certificate.

## Reproduction and tamper tests

See `README.md` for all commands. In particular run `python3 code/check_all_tree.py` and `python3 -O code/check_all_tree.py` (both invoke the independent two-layer checker) and compare output logs, and likewise replay `code/check_two_layer.py` in both modes. Run `code/negative_controls.py`, which corrupts state attainability, a two-layer frontier, and/or a reported maximum; every corruption must trigger an explicit exception. `SHA256SUMS` pins all published research file bytes apart from its own checksum file and temporary Python cache files. The all-tree producer was independently rerun and its output **byte-compared successfully** with the full extension. The separate two-layer producer generated the frozen certificate and is reproducible by Python 3's standard library.

## Exact scope

The class comparison is `C_d` (all finite point-generated product/join trees) against its concrete proper subgrammar `B_d` (joins of points and products of exactly two simplices). `d=55` is the **first dimension where no B witness attains the C optimum**. It does not show that *all* maximizing bodies necessarily contain the displayed particular subtree or that no nested body can tie a two-layer one in earlier dimensions. All dimensions beyond 55, the unrestricted convex-body sharp constants and complete equality classifications remain outside the result.
