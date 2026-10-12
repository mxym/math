# A universal second-order oscillation obstruction for sharp projection-body Bellman potentials

**Entry-005 research continuation — 8 October 2026.**

[Full mathematical proof](paper.md) · [Independent pure-rational quadratic-germ checker](code/check.py) · [Independent canonical-profile rational checker](code/check_canonical_rational.py) · [Optional second SageMath/Arb replay](code/check_canonical_arb.py) · [Audit and dependencies](AUDIT.md).

The full spectral optimum for the point-generated convex-polytope Cartesian-product/affine-join class is still **open**. The main candidate is the binary self-product/self-join recursion seeded by \(T_5\). We prove two strict, genuinely **all-dimensional constraints** on attempts to certify that candidate with a *single* homogeneous Bellman potential \(\Phi(D,H)=D(c_*-\psi(H/D))\), separately inductive under product and join.

## The main result: no quadratic germ, even without convexity

If \(\psi(0)=0\), \(\psi(1)=c_*\), \(\psi(t)\to0\) at zero, and the ordinary separate join/product closure inequalities hold for **all actually constructible states**, define
\[
 \alpha_*=\frac8{81}\left(c_*+\frac12\log\frac{27}{4\pi}\right).
\]
Then we prove the **strict universal relative oscillation**
\[
\boxed{\liminf_{t\downarrow0}\frac{|\psi(t)-\alpha_*t^2|}{t^2}=0,
\quad \limsup_{t\downarrow0}\frac{|\psi(t)-\alpha_*t^2|}{t^2}>\frac1{4000}.}
\]

More strongly, the necessary deviation has a **deterministic signed form at every orbit index**: for every `j>=1`, if `tau_j=H(A_j)/(dim(A_j)+1)` and `sigma_j=H(A_j)/(2 dim(A_j)+1)` for `A_j=K_j*point^(*2^(j-1))`, then **either** `(psi(tau_j)-alpha*tau_j²)/tau_j²>1/4000` **or** `(psi(sigma_j)-alpha*sigma_j²)/sigma_j²<−1/4000`. Nine strict rational cases and one analytic infinite-tail inequality verify **every index**, not just an asymptotic subsequence. In particular, **no such sharp scalar Bellman potential can possess a quadratic expansion at zero or be twice differentiable there**. Convexity, nonnegative Taylor coefficients, polynomiality and analyticity are **not** assumptions. For a hypothetical **convex** sharp profile, the theorem additionally pins the exact regularity threshold: its right first derivative at zero **must exist and equal zero**, but a second derivative is impossible, and even `psi'_+(t)/t` cannot converge. This strictly strengthens the previous 005 exclusions of all real-analytic/polynomial profiles. The proof uses an actual infinite family obtained by joining \(2^{j-1}\) points to the \(j\)-th binary \(T_5\) orbit body. Its self-product forces a negative limiting quadratic slack \(<-1/200\); the original orbit simultaneously forces an exact quadratic coefficient. The strict sign and rational oscillation bound have an **independent standard-library rational interval certificate**.

## The natural canonical nonanalytic interpolation also fails

We construct a natural nonanalytic extension \(\psi_{\mathrm{can}}\) that matches **every exact orbit interpolation equality** through a continuous real-Gamma version of the binary-tail series. Yet the concrete body
\(A=(T_1\times T_2)*\mathrm{point}^{*5}\), of dimension eight with \(H(A)=53/7\), violates its necessary self-product Bellman inequality by **more than \(1/20000\)**, rigorously.

This is replayed in *two independent interval implementations*: one uses only Python integers/Fraction with 136-bit outward dyadic rounding, four Binet–Stirling terms and a rigorous signed next-term bound, plus a closed infinite-series tail; the other uses SageMath/Arb 192-bit real balls with `log_gamma` and an independent closed analytic tail. The **pure-rational checker is the publication certificate**; SageMath is optional, not a dependency of CI.

Consequently any future exact sharp profile must differ from the canonical one at two explicitly given rational arguments by a nonzero amount:
\[
18\bigl(\psi-\psi_{\mathrm{can}}\bigr)(53/63)
-17\bigl(\psi-\psi_{\mathrm{can}}\bigr)(53/119)>1/20000.
\]

## Reproduction

From repository root, Python 3.10+ standard library only:

```sh
python3 notes/projection-bellman-quadratic-oscillation/code/check.py
python3 -O notes/projection-bellman-quadratic-oscillation/code/check.py
python3 notes/projection-bellman-quadratic-oscillation/code/check_canonical_rational.py
python3 -O notes/projection-bellman-quadratic-oscillation/code/check_canonical_rational.py
python3 notes/projection-bellman-quadratic-oscillation/code/negative_controls.py
(cd notes/projection-bellman-quadratic-oscillation && sha256sum -c SHA256SUMS)
```

Optional separate numerical-interval implementation if SageMath with Arb is installed:

```sh
sage -python notes/projection-bellman-quadratic-oscillation/code/check_canonical_arb.py
```

No floating optimizer or finite extrapolation participates in the proof. The convex-geometric identities and exact definition of the binary orbit are inherited from the previously public 005 v2/v5 results; infinite limits and all uniform inequalities are proved explicitly in [`paper.md`](paper.md). The results obstruct a particular *sharp proof architecture*, **not the truth of the binary \(T_5\) global optimality conjecture itself**. We do not claim a globally valid sharp replacement potential, human peer review, Lean formalization, or worldwide publication priority.
