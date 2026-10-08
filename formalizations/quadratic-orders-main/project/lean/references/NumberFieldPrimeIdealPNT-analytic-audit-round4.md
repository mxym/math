# Number-field prime-ideal PNT: analytic audit, round4

The actual number-field prime-ideal PNT remains open. This read-only audit found no public Lean endpoint that closes it in the inspected sources. It identified useful source-level intermediate candidates and a concrete route through an effective all-ideal count. Neither an analytic package supplied as an assumption nor a Dirichlet-density statement is a proof of the frozen premise.

The fixed environment is Lean `leanprover/lean4:v4.34.1`, official mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, and source-v3 snapshot `c897a556e12e460380c7cf521e88f84286994915`. The immutable round3 ZIP was read and its SHA-256 remains `b522ad7db760522efd762dc9a8dfc97b75bc794ecdb2ce5f059b30f628cb7cc7`. No proof, control, verifier, pin, or prior evidence file was edited. No Lean build was run by this audit. Public temporary source downloads were inspected under `/tmp/entry002-nf-public-audit-r4`.

The new machine-readable evidence is [nf-analytic-public-audit-round4.json](../logs/nf-analytic-public-audit-round4.json), SHA-256 `c19b9cfee7181d7da5d86d8869d23f24c79c22f1a24542f4abafab831722fa32`. It records commit-addressed source hashes, finite keyword scans after removing nested comments and strings, candidate declarations and proof holes, and the inspected local source hashes. It is evidence of source inspection, not new kernel verification. The managed runtime skill and networking reference were read first; the inspected network policy permits HTTP through the inherited proxy and has `vpn_configured: false`. The `environment_status` tool was unavailable. No credential value was inspected.

The sole open premise is still the exact statement in `ArithmeticSupplyMainFromPrimeIdealPNT.lean`:

```lean
∀ (N : Type) [Field N] [NumberField N],
  Tendsto (fun x : ℝ =>
    ((Entry002.nonzeroPrimeIdealsUpTo N ⌊x⌋₊).card : ℝ) /
      (x / Real.log x)) atTop (nhds 1)
```

The public quantification is over all number fields. The existing target assembly uses it at an actual finite Galois normal closure, but this audit does not change the public premise or the all-quadratic-orders MainTarget. The complete FiniteSieveTarget proof and existing conditional arithmetic chain retain their prior status.

The following intermediate results are already actual statements with proof bodies in the delivered/pinned foundation. Their previously recorded verification is retained; this audit does not claim a fresh full mathlib build or a second kernel.

| Existing result | Exact hypothesis and limit of its usefulness |
| --- | --- |
| `WienerIkeharaTheorem'`, delivered patched `PrimeNumberTheoremAnd/Wiener.lean:2050` | For `f : ℕ → ℝ`, assumes `0 ≤ f`; norm summability for every real `σ > 1`; `∃ C, ∀ n, cumsum ‖f‖ n ≤ C*n`; `ContinuousOn G {s \| 1 ≤ s.re}`; and agreement of `G` with `LSeries f s - A/(s-1)` on `Re(s)>1`. Concludes `cumsum f N/N → A`. |
| `WeakPNT` and `Entry002.arithmeticSupply_prime_counting_ratio_tendsto` | Prove the rational PNT for the actual rational von Mangoldt and `Nat.primeCounting` definitions. They do not count number-field prime ideals. |
| `NumberField.Ideal.tendsto_norm_le_div_atTop₀`, `Ideal/Asymptotics.lean:128` | Counts all actual nonzero integral ideals, with limit equal to the class-number/regulator/discriminant residue. It yields an `O(x)` bound and `Cx+o(x)`, with no stated exponent below one for the error. |
| `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`, `DedekindZeta.lean:77` | A right-hand real-axis limit `(s-1) ζ_K(s) → C_K`, with `C_K>0`. It does not establish a meromorphic complex continuation at `1`, or analytic continuation at `1+it`. |
| `LSeriesSummable_of_sum_norm_bigO_and_nonneg`, `SumCoeff.lean:90` | Nonnegative real coefficients whose partial sums are `O(n^r)`, with `r≥0`, give absolute convergence at complex `s` when `r<s.re`. |
| `LSeries_deriv`, `Deriv.lean:86`, and `LSeries_convolution'`, `Convolution.lean:149` | Differentiate in the open half-plane of absolute convergence and multiply absolutely convergent Dirichlet series. They can support a genuine ideal-factorization convolution identity; they do not supply that identity for ideal counts. |
| `Ideal.sum_ramification_inertia_eq_finrank`, `RamificationInertia/Basic.lean:72` | For a prime of an integral domain and a finite flat algebra, with a finite prime fiber, proves `Σ e*f = finrank`. The Galois specialization `ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn` is already used by the delivered counting chain. |

The exact six-root PNT audit in `upstream/arithmetic-audit/logs/pnt-recursive-audit-summary.json` includes `WienerIkeharaTheorem'` and the rational counting endpoint. Its stored-type/body traversal agrees with `collectAxioms`; only `propext`, `Classical.choice`, and `Quot.sound` occur, with no recorded unsafe, partial, or missing dependencies. This is prior evidence for the exact four-module patched import closure. It does not authenticate unimported candidate theorems merely because they share a repository.

The [pinned Dedekind-zeta source](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/NumberTheory/NumberField/DedekindZeta.lean) defines the actual ideal-counting L-series. The corresponding file at observed public master commit `021ce68bf125a049beee22b3fc7664d78728e21d` has identical definitions and proofs; its sole observed difference changes the `BigOperators.Ring.Nat` import from public to private and moves its position. The latest file therefore contributes no new analytic theorem. `LSeries/Nonvanishing.lean` proves line-one nonvanishing for Dirichlet-character L-functions and Riemann zeta, with an actual `DirichletCharacter` parameter. Its `norm_LSeries_product_ge_one` is a useful proof model, not an arbitrary-number-field theorem.

The fresh public-source inspection produced these findings:

| Source and exact revision | Actual finding |
| --- | --- |
| [CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density/tree/c64095e6cc6483b401849c7fd9182d983d3bf261), `c64095e6cc6483b401849c7fd9182d983d3bf261` | All seven Lean files inspected. Lean `4.32.0-rc1`; mathlib `e568743e9c24da15c8f8347a47931d2a6c33ff85`. `Main.lean:26` states Dirichlet density and has `sorry` at line 33. `Density.lean` has actual `sorry` at lines 101, 120, 127, 150, 158. The last two are the prime-ideal higher-power-tail and Euler-log comparison inputs, so the downstream prime-ideal zeta-sum limit inherits holes. |
| Same repository, `Density.lean:163` | `logDedekindZeta_sub_log_inv_sub_one_bounded` has a written proof using the positive real residue and its real-axis limit. No local sorry-containing declaration is used in this body. It provides a real logarithmic bound and no complex boundary extension. No pinned port/build or recursive kernel audit was performed here. |
| Same repository, [IndexImageCount.lean:194](https://github.com/CBirkbeck/chebotarev-density/blob/c64095e6cc6483b401849c7fd9182d983d3bf261/CebotarevDensity/ForMathlib/IndexImageCount.lean#L194) | A written proof bounds grid cells meeting a frontier covered by `m` globally `M`-Lipschitz images of a `(d-1)`-dimensional unit cube. The explicit bound is `m*(2*ceil(M)+1)^d*2^(d-1)*n^(d-1)` for `n≥1`. The file has no source-level proof escapes. Its finite Lipschitz cover is an actual premise. No cover for `normLeOne K`, or full effective lattice-count theorem, is present in the seven-file tree. The prose mentions `LatticePointCount.lean`, but that file is absent. Port and kernel verification remain necessary. |
| [AlexKontorovich/PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/c39a751132c88b6e8080b74c74023fd95b3d8be0/PrimeNumberTheoremAnd/Wiener.lean), `c39a751132c88b6e8080b74c74023fd95b3d8be0` | Pristine `Wiener.lean:3904` contains `WienerIkeharaTheorem''`, which removes the separate Chebyshev input using `auto_cheby` at line 3891. It still needs nonnegativity, every-`σ>1` norm summability, continuous boundary `G`, and exact agreement with the pole-subtracted L-series. The delivered four-module patch removes this section. Pristine `prelim_decay_2/3` contain `sorry` at lines 327/347; their only observed downstream mentions are in `decay_alt`. A future port needs a true dependency/body audit before stronger Wiener can be accepted. Dedekind/Artin/Chebotarev prose at lines 4054–4384 is `blueprint_comment` content, not theorem declarations. |
| [AxiomMath/PrimeNumberTheoremAnd](https://github.com/AxiomMath/PrimeNumberTheoremAnd/tree/d71f7b41560c1487cc6b9fbbe6914b55fd8aac13), `d71f7b41560c1487cc6b9fbbe6914b55fd8aac13` | All 135 Lean source members scanned. Stronger Wiener/automatic Chebyshev statements occur; no actual-code Dedekind-zeta/prime-ideal/Hecke-L/Chebotarev keyword candidate was found. It uses Lean `4.35.0-rc2`, so the current fork is not already compiled at the fixed pins. |
| [n-yamaguchi-0729/ClassFieldTheory](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/7713795234690681b4406ae198b07aa95e82716a), `7713795234690681b4406ae198b07aa95e82716a` | All 1661 Lean source members scanned after removing comments/strings. No actual-code match for the recorded Dedekind-zeta/PNT/Chebotarev/Hecke-L/Wiener/NumberField-LSeries pattern was found. This observed current revision uses Lean `4.35.0-rc2`; it is distinct from the already audited delivered pin `2eb22d6485af45f29c5219de6c49f196a61c4f49`. |
| `Cobord/ZetaThetaFunctions` `aa3809e5fbaf1fbe8322c3dafecd6586bbcd430d`; `lean-forward/class-number` `812ff19e6fbde86f8d71689851adaa2bbae9695e` | Complete scans of 13 and 19 Lean source members respectively found no candidate for the recorded analytic number-field patterns. |

These are bounded source-inspection conclusions. Repository-name searches and finite keyword scans cannot prove that no suitable theorem exists anywhere. They do rule out the concrete apparent candidates above as a presently checked number-field PNT foundation.

A concrete mathematical route, still to formalize, can be kept substantially smaller than a full Dedekind functional equation. Let `a_K(n)` be the actual ideal coefficient of the pinned zeta series, and let

\[
\Lambda_K(n)=\sum_{\mathfrak p\ne0,\;m\ge1,\;(N\mathfrak p)^m=n}\log N\mathfrak p.
\]

For `n=p^r`, actual norm/inertia theorems give

\[
\Lambda_K(p^r)=\log p\sum_{\mathfrak p\mid p,\;f_{\mathfrak p}\mid r}f_{\mathfrak p}
\le [K:\mathbb Q]\log p.
\]

For other `n`, the coefficient is zero. This follows from `e_p≥1` and the genuine fundamental identity `Σ e_p f_p=[K:Q]`. Thus `0≤Λ_K(n)≤[K:Q] Λ(n)`. This is a proposed elementary formalization, not a proved new Lean lemma in this audit. It reduces convergence and the Chebyshev bound to the existing rational von Mangoldt bounds, without requiring another deep analytic assumption.

Actual ideal factorization should next prove `log(n)*a_K(n)=(a_K ⍟ Λ_K)(n)`. The existing convolution and derivative theorems would then give `-ζ'_K/ζ_K=LSeries Λ_K` on `Re(s)>1`, once actual Euler-product nonvanishing there is proved. The coefficients and identities must be tied to actual `Ideal.absNorm` throughout.

The serious missing construction is an effective all-ideal count `A_K(x)=C_K x+O(x^α)` for some `α<1`. A finite Lipschitz chart cover of the actual mixed-embedding fundamental norm domain, followed by quantitative lattice counting and the existing ideal-class equivalence, offers a direct route to `α=1-1/[K:Q]`. Mathlib currently proves boundedness and zero volume of that frontier; these do not by themselves supply the quantitative chart-cover bound. The public grid-cell lemma is one intermediate ingredient only.

With such an actual error estimate, the existing integral representation suggests constructing

\[
Z_K(s)=C_K\frac{s}{s-1}
 +s\int_1^\infty (A_K(t)-C_Kt)t^{-s-1}\,dt,
\qquad \Re(s)>\alpha.
\]

This construction would need proved complex differentiability and equality to the genuine ideal Dirichlet series on `Re(s)>1`. It supplies a simple pole with residue `C_K>0`. An actual Euler product and the positivity identity `3+4 cos θ+cos(2θ)=2(1+cos θ)^2` then give the standard three-point product inequality and rule out zeros at `1+it` for `t≠0`. This adapts the pattern in pinned `LSeries/Nonvanishing.lean`; it does not treat its Dirichlet-character theorem as a number-field theorem.

Define the regularized analytic function `H_K(s)=(s-1)Z_K(s)`, with the proved value `H_K(1)=C_K`. Proving `H_K≠0` on the closed right half-plane makes `G_K=-H'_K/H_K` continuous there. The exact identity is then `G_K=LSeries Λ_K-1/(s-1)` on `Re(s)>1`. Notice that Wiener receives residue `1` for the logarithmic derivative, independently of the positive residue `C_K` of zeta. This is the genuinely missing boundary input, to be constructed and proved, not supplied as an opaque analytic package.

Finally, Wiener gives `ψ_K(x)/x→1`. The higher-power difference is bounded by `O(√x log x)=o(x)` using actual prime fibers; partial summation of the actual norm-indexed prime count then yields the literal finite-count `x/log x` premise, including floor/endpoints. These final weighted/unweighted counting steps are still required; the existing rational Chebyshev lemmas are proof models rather than automatically applicable ideal-count theorems.

The immediate reusable results are the existing audited Wiener theorem and rational bounds, the pinned convolution/derivative/summability APIs, and the public source-level finite Lipschitz frontier-cell bound pending a fixed-pin port. The remaining analytic bottleneck is the actual Dedekind-zeta boundary construction and nonvanishing, preceded by quantitative number-field geometry and actual Euler/log-derivative identities. No unconditional prime-ideal PNT or MainTarget is claimed.
