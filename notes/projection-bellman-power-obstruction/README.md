# A rigorous all-degree barrier to sharp positive-power projection-body Bellman bounds

**Supplement to entry 005, 8 October 2026.**

[Complete mathematical proof](paper.md) · [Independent exact power-dual checker](code/check.py) · [Certified binary-tail join obstruction](code/check_binary_tail.py) · [Trust boundary and attribution](AUDIT.md).

The core open problem is to determine the exact asymptotic projection-body growth constant for **all** finite point-generated Cartesian-product/affine-join trees. Earlier 005 work gives a sharp binary \(T_5\) *candidate* lower construction and positive-polynomial Bellman upper estimates, but has not proved equality.

This note rigorously demonstrates **two obstructions to natural proof methods**, without asserting any counterexample to the candidate optimum.

**(1) Sharp three-state infinite-degree positive-power obstruction.** Consider every Bellman potential
\[
\Phi(D,H)=\sum_{k\ge1}a_k\left(D-\frac{H^{2k}}{D^{2k-1}}\right),
\quad a_k\ge0,\quad T=\sum_{k\ge1}a_k<\infty.
\]
If its ordinary separate one-step product-closure inequality holds for all *actually attainable* operands, then
\[
\boxed{T>486139/10^7=0.0486139.}
\]
This floor lies **strictly above the certified binary \(T_5\) orbit's logarithmic rate**, so **no finite or countably infinite number of additional positive even powers** can make that product-inductive method certify the conjecturally sharp constant. Three explicit polytopes in dimensions **5, 13 and 36**, all genuinely constructible from points, yield the dual obstruction. Six powers are checked separately; *every other even power*, without cutoff, is controlled by one exact rational geometric bound. Moreover the **entire infinite linear programme on the three necessary test states is solved exactly**, with a unique minimizing sequence supported on degrees **2, 4, 8**, certified by an exact rational 3-by-3 primal-dual pair. This is the sharp optimum of the *three-test relaxation*, not a claim that the resulting polynomial satisfies all other full-class product inequalities.

**(2) No analytic sharp Bellman potential.** An all-orders **Stirling–Bernoulli** proof rules out **every real-analytic profile near $H/D=0$** (even an infinite convergent power series) from attaining the T5 candidate constant under ordinary separate join/product induction. The underlying central-binomial Stirling series has factorially growing coefficients; a genuine analytic sharp profile would force a convergent series with those same coefficients, an impossibility. If a sharp profile is instead merely **smooth**, its **entire formal Taylor series is uniquely forced, all odd coefficients vanish, and the formal even series has zero radius of convergence**. The first six even coefficients through $t^{12}$ are replayed as exact rational expressions in the single constant $L=c_*+\log(3\sqrt3/(2\sqrt\pi))$. A standard-library checker certifies the first sixteen exact Bernoulli coefficients and their factorial lower bounds; the theorem relies on classical all-orders Euler–Maclaurin asymptotics, not extrapolation.

**(3) No finite polynomial or finite-knot sharp Bellman potential.** By Bertrand’s postulate, the exact binary `T5` orbit multipliers each have a new prime factor, and their logarithms are linearly independent over the rationals. This gives a rigorous infinite-rank obstruction: **any** continuous-at-zero sharp homogeneous potential satisfying separate join/product closure cannot agree near zero with a finite-degree polynomial, even with arbitrary signed coefficients, or with any finite-knot polynomial spline. Moreover, for **each fixed polynomial degree**, every nondecreasing separately closed polynomial potential has a **strictly positive (degree-dependent) gap** above the sharp T5 value, proved by finite-dimensional compactness without assuming coefficient positivity. A separate all-integer checker replays 13 explicit prime witnesses; the infinite proof relies on Bertrand, not on extrapolation.

**(4) Sharp-orbit interpolation, forced curvature and failure of naive join induction.** We derive an exact, absolutely convergent series for the limiting binary-recursion spectral rate from **any finite seed**. Any continuous convex potential that would prove the sharp binary rate by separate product/join closure must **interpolate every point of the infinite binary `T5` orbit** and, if quadratic near zero, has the uniquely forced coefficient $\alpha=\frac8{81}(c_*+\frac12\log(27/(4\pi)))\in(0.04256,0.04257)$. At the same time, the corresponding natural exact binary-tail scalar candidate fails the standard join-induction step already for the realizable polytope `T1 × T2`, with a rigorously certified join defect below **−3/10**. This does **not** falsify the candidate's global inequality; it shows why the naive induction cannot prove it without accounting for state-dependent slack.

A **third exact comparison** confirms why the barrier is method-specific: a simple rational convex hinge potential with endpoint `191/4000` passes all three dual-test products even though that endpoint is below the binary-orbit rate; the same hinge profile fails a deeper genuinely attained binary-orbit product `(d,H)=(85,24)`. These results suggest that a sharp proof must use a more flexible convex potential, dimensions/reachability information, or a new Bellman architecture. Finite numerical convex-spline experiments motivate this possibility but are **not** used in the two theorems or presented as independently certified general results.

Run from the repository root (Python 3.10+, standard library only):

```sh
python3 notes/projection-bellman-power-obstruction/code/check.py
python3 -O notes/projection-bellman-power-obstruction/code/check.py
python3 notes/projection-bellman-power-obstruction/code/check_formal_germ.py
python3 notes/projection-bellman-power-obstruction/code/check_stirling_germ.py
python3 notes/projection-bellman-power-obstruction/code/check_prime_independence.py
python3 notes/projection-bellman-power-obstruction/code/check_sharp_dual.py
python3 -O notes/projection-bellman-power-obstruction/code/check_sharp_dual.py
python3 notes/projection-bellman-power-obstruction/code/check_binary_tail.py
python3 -O notes/projection-bellman-power-obstruction/code/check_binary_tail.py
python3 notes/projection-bellman-power-obstruction/code/negative_controls.py
(cd notes/projection-bellman-power-obstruction && sha256sum -c SHA256SUMS)
```

The code uses arbitrary-precision rationals, exact integer powers and rigorous rational logarithm/tail enclosures. Normal and optimized reports are byte-comparable; hostile data mutations must be rejected. The imported convex-geometric calculus and binary \(T_5\) source bounds are clearly cited. This is an AI-assisted research result, not external human peer review, full Lean formalization or a priority claim.

**Subsequent stronger result — no C² sharp scalar potential.** The separate [quadratic-oscillation theorem](../projection-bellman-quadratic-oscillation/README.md) proves that **no** continuous-at-zero sharp homogeneous scalar potential can have even a second-order asymptotic expansion at zero under the same ordinary separate product/join induction. Therefore the earlier *conditional* statements about a smooth sharp profile's uniquely forced divergent Taylor jet should be read as **formal orbit-consistency calculations**, not as suggesting such a smooth sharp global potential exists. The later note also rigorously rejects the natural nonanalytic Gamma-interpolation through a real attainable dimension-eight product.
