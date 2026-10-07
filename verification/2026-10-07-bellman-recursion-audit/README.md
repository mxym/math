# Independent replay and scalar-reduction audit of entry 005

Date: 2026-10-07. AI-assisted audit, not human peer review or proof-assistant verification.

## Result and exact scope

The original v5 balanced-recursion certificate and the new v2 Bellman verifier both pass under ordinary Python and `python -O`. No counterexample to either main theorem was found. The Bellman supplement had a local statement error: its high-boundary quadratic was written using the symbol for the full piecewise minimum on an interval extending outside the high branch. The corrected statement below preserves the intended proof. Three valid endpoint-monotonicity facts have also been made explicit in the checker.

Two different optimization statements must be kept separate:

- v5 fixes one integer arity `t >= 2` and a simplex seed dimension `p >= 1`, and iterates `K_(j+1) = (K_j^t)^{*t}` from `T_p`. Its limiting projection-volume root rate has unique maximum at `(t,p)=(2,5)`. It does not classify unequal arities, changing arities, arbitrary operation trees, or all convex bodies.
- The Bellman supplement covers the entire point-generated class of finite Cartesian-product/join expressions and affine-isomorphic images on their affine hulls. Its inequality is `log Q <= alpha (D-H^2/D)`, with `alpha=(11/85)log(189/128)`. Combined with the spectral reduction and v2 lower construction, this proves `2.8534 < Gamma_C <= e(189/128)^(11/85) < 2.8589`. It neither determines `Gamma_C` exactly nor proves that the binary `T_5` orbit is optimal in this larger class. It is not an upper bound for all convex bodies.

The coefficient of this particular quadratic potential is sharp, because `T_5 x T_5` forces equality. Sharpness of that coefficient does not establish attainability of the resulting asymptotic upper bound.

## Audited source and isolation

The source audited was commit `80b3317de497dffdaa6b6398d7ba908c29cb252a`, tree `1917de5a50dd94941833c903be9aa3eb88c12b2d`. It was extracted with `git archive` into an independent directory. No checkout, pull, release-stage edit, catalogue edit, or push was used for the audit. The correction is a small delta against that commit; unchanged newer publications are outside its scope.

Primary source paths:

- `preprints/005-simplex-product-optimum/v5/paper.md`
- `preprints/005-simplex-product-optimum/v5/code/check_balanced.py`
- `preprints/005-simplex-product-optimum/v5/MANIFEST.json`
- `preprints/005-simplex-product-optimum/v2/BELLMAN_UPPER_BOUND.md`
- `preprints/005-simplex-product-optimum/v2/code/check_bellman_upper.py`
- `preprints/005-simplex-product-optimum/v2/paper.md`
- `preprints/005-simplex-product-optimum/v2/ASYMPTOTIC_SPECTRAL_REDUCTION.md`

## Mathematical reduction reviewed

### Balanced homogeneous recursion

The inherited calculus gives `d_(j+1)=t^2 d_j+t-1`, `a_(j+1)=a_j/t`, and

`R_(j+1)=R_j^(t^2) t a_j^(t-1) g(d_(j+1))/g(t d_j)^t`.

With `c=1/(t+1)`, the identities `d_j+c=(p+c)t^(2j)` and `a_j=1/((p+1)t^j)` give the stated logarithmic limit. The two-sided Stirling bounds cancel the dimension growth in the step factor. The uniform upper envelope, its restarted version, and the signs in the two parameter-tail arguments agree with the code.

The finite screening covers all 342 pairs with `2 <= t <= 19`, `1 <= p <= 19`: 335 direct exclusions, six three-level exclusions, and the winning pair. The small-arity large-seed tail covers `p >= 20`; the large-arity tail covers every `t >= 20`, `p >= 1`. These regions exhaust the theorem's parameter set. The lower endpoint is recomputed from the exact level-six state (`d=21845`, exponent `65536`), rather than inferred from floating-point output.

### Bellman induction and box minimum

For a product of dimensions `r,s >= 1`, the exact calculus reduces the induction to

`log(A_(r,s) B) <= alpha (G-1)`.

Weighted harmonic mean is at most weighted arithmetic mean, so replacing the negative harmonic-mean square by the negative arithmetic-mean square gives a lower bound on `G` in the required direction. The remaining problem is a strictly convex quadratic minimum with `1 <= H_1 <= r+1`, `1 <= H_2 <= s+1` and `s H_1+r H_2=(r+s)B`.

Independent symbolic algebra confirms the stationary point and minimum in (4.2)-(4.3). After eliminating `H_1`, the coefficient of `H_2^2` is exactly

`r(4rs+3r+3s+2) / [s(r+1)(s+1)(r+s+1)] > 0`.

The new standard-library regression reconstructs the quadratic directly from (4.1), independently of the expanded coefficient routine, for every finite-strip branch. It checks equality of the quadratic at three rational points, feasibility, the correct constrained derivative sign, and positive curvature. Equality at three points establishes identity of these quadratic polynomials; feasibility and the derivative conditions also persist along each affine branch.

The finite strip `1 <= s <= 9`, `s <= r < 1000` has exactly 26,847 branches. Symmetry, the `s >= 10` tail, and the `s <= 9, r >= 1000` tails cover all dimension pairs. The exceptional `(5,5,B=6)` equality is checked algebraically with a positive derivative at its endpoint. Every other branch has a strict negative certified upper margin.

Joins preserve the region by Cauchy's inequality. The formal point is an equality seed, and products involving a point add no new shape. Thus the finite-expression induction is well founded. The separate join-closed spectral theorem supplies the all-dimensional limit; the finite arithmetic alone does not establish that analytic theorem.

## Corrected defect and regression witnesses

In the original supplement, (6.5)-(6.6) used `q_(r,s)` for what their displayed difference identities actually compute: the boundary polynomial `q_(s+1)` from (4.4). The full piecewise minimum does not satisfy those displayed lower bounds throughout the enlarged intervals.

Exact counterexamples to that original literal formulation are:

- `r=1000,s=2,B=3`: the middle-branch value is `423/172 < 3`, while the limiting high quadratic is `3`.
- `r=1000,s=3,B=4`: the middle-branch value is `48176/15011 < 4`, while the limiting high quadratic is `4`.

The intended high-branch argument is valid. The correction explicitly defines `q_high=q_(s+1)` and uses it on the actual high interval `[B_+,B_max]`. For `r >= s`,

`B_+-(s+1)=s(r-s)/(3r+s+2) >= 0`,

and `B_max < 2s+1`. Thus the actual interval lies inside the enlarged interval `[s+1,2s+1]` used to certify the limiting polynomial. The two original difference formulas are exact identities for `q_high`; their numerator sign claims hold on those enlarged intervals.

For the low and middle tails,

`(4s+3)/3-B_+ = 2s(2s+1)/[3(3r+s+2)] > 0`.

The endpoint bound for `s=2,3` is therefore valid once `1-2 alpha k B_mid^2 > 0` is checked, with `k=3/(4s+3)`. The analogous `s=1` endpoint is `B=3`. All three inequalities are true using the rigorous upper endpoint of the alpha interval. The correction adds explicit exception-based checks, and the regression verifies them independently. They remain active under `python -O`.

## Arithmetic and replay evidence

Runtime: Python 3.12.14. All proof comparisons use integers and `fractions.Fraction`. Logarithms use power-of-two range reduction with sign-correct interval scaling and a positive atanh-series remainder; the Bellman checker encloses pi with Machin's identity and alternating-series bounds. Branch bisection keeps an enclosing interval if the derivative sign becomes uncertain. Evaluating the logarithm at the bracket's upper endpoint and subtracting the minimum quadratic contribution gives a valid upper bound. No floating-point number decides a pass.

Completed runs, ordinary and optimized:

1. v5 manifest checker: all nine pinned dependencies pass.
2. v5 balanced checker: outputs byte-identical to each other and to the committed replay.
3. Original Bellman checker: all 26,847 branches and analytic tails pass; both exact JSON reports and stdout are byte-identical.
4. v2 inherited checker with `--self-test`: full finite closure, direct geometry, both winning-orbit endpoints, and four deliberately corrupted certificates pass/reject as expected; ordinary/optimized reports match.
5. Corrected Bellman checker: both modes pass and produce exactly the original report and stdout.
6. New structural regression: both modes pass, checking 26,847 branches at 80,541 rational points, all three endpoint monotonicity facts, both notation-regression witnesses, boundary identities, and invalid-log negative controls.

The full Bellman JSON report is 857,255 bytes, SHA-256:

`cd66ff9796b985b18f9fd3c051109d09ab30973d79c97606a6a614e8b67986de`.

Its nearest strict branch is `(r,s)=(5,4)`, high branch. For display only, its certified upper margin is approximately `-0.0004556011594737194`. The `s >= 10` tail margin is approximately `-0.00781065029720849`; the worst fixed-small-side tail is approximately `-0.004557165125223321` at `s=4`. These decimal displays are not proof inputs.

The v5 report SHA-256 is `652613a08093481d48c2a5ffce83edfb31fb05c9bfd12c6428ea2ac0c5c2fc15`; the inherited v2 self-test JSON SHA-256 is `a362e9e4b1331ceb5f0b36d9fe1ffb4271226c7e1d967e53df8f85188fe9f17b`.

## Reproduction

From the repository root, set `out` to an empty directory and run:

```sh
out=$(mktemp -d)
python3 preprints/005-simplex-product-optimum/v5/code/check_manifest.py
python3 -O preprints/005-simplex-product-optimum/v5/code/check_manifest.py
python3 preprints/005-simplex-product-optimum/v5/code/check_balanced.py > "$out/v5.txt"
python3 -O preprints/005-simplex-product-optimum/v5/code/check_balanced.py > "$out/v5-opt.txt"
cmp "$out/v5.txt" "$out/v5-opt.txt"
cmp "$out/v5.txt" preprints/005-simplex-product-optimum/v5/results/check_balanced.txt
python3 preprints/005-simplex-product-optimum/v2/code/check_bellman_upper.py --report "$out/bellman.json" > "$out/bellman.txt"
python3 -O preprints/005-simplex-product-optimum/v2/code/check_bellman_upper.py --report "$out/bellman-opt.json" > "$out/bellman-opt.txt"
cmp "$out/bellman.json" "$out/bellman-opt.json"
cmp "$out/bellman.txt" "$out/bellman-opt.txt"
python3 preprints/005-simplex-product-optimum/v2/code/check_bellman_structure.py > "$out/structure.txt"
python3 -O preprints/005-simplex-product-optimum/v2/code/check_bellman_structure.py > "$out/structure-opt.txt"
cmp "$out/structure.txt" "$out/structure-opt.txt"
python3 preprints/005-simplex-product-optimum/v2/code/check.py --self-test --report "$out/v2.json" > "$out/v2.txt"
python3 -O preprints/005-simplex-product-optimum/v2/code/check.py --self-test --report "$out/v2-opt.json" > "$out/v2-opt.txt"
cmp "$out/v2.json" "$out/v2-opt.json"
cmp "$out/v2.txt" "$out/v2-opt.txt"
sha256sum "$out/bellman.json" "$out/v5.txt" "$out/v2.json"
```

## Nonblocking observations and limitations

The v5 source contains stale comments saying two recurrence levels where the code uses three, and monotonicity from 8 where the valid paper and executable checks use 9. Its strict-positive remainder notation should allow zero when the reduced logarithm argument is one; the actual checker already handles that endpoint exactly. These editorial items do not change its proof or replay and are outside this narrow Bellman correction.

At the audited base, the new Bellman files were not covered by the historical v2 manifest or by the existing v5 CI workflow. The v5 manifest correctly describes its own pinned dependencies and passes. This audit supplies reproducible Bellman commands and a regression; it does not claim that existing CI had run them. No publication-priority, novelty, unrestricted extremizer, or external-referee claim is made.
