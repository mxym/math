# Unique optimum in the balanced homogeneous simplex recursion

**Entry 005, version 5 — 7 October 2026. Complete written proof; exact rational logarithm certificate.**

Read the [manuscript](paper.md), [proof audit](PROOF_AUDIT.md), [checker](code/check_balanced.py), [recorded replay](results/check_balanced.txt), [dependency manifest](MANIFEST.json), and [focused prior-work comparison](../../../comparisons/2026-10-07-balanced-recursion.md).

## Result

For integers
\[
t\ge2,\qquad p\ge1,
\]
start from a \(p\)-simplex and iterate
\[
K_{j+1}=(K_j^t)^{*t},
\]
where \(K^t\) is the \(t\)-fold Cartesian product and \(K^{*t}\) the \(t\)-fold join. Let
\[
\Lambda_{t,p}=\lim_j R(K_j)^{1/\dim K_j}.
\]

Version 5 proves that the unique maximizer over the entire two-parameter family is
\[
\boxed{(t,p)=(2,5).}
\]
Every other pair satisfies
\[
\Lambda_{t,p}<e^{131/125}<2.8534,
\]
whereas the binary \(T_5\) orbit satisfies
\[
2.8534<\Lambda_{2,5}<2.8535.
\]

This converts the earlier discovery observation that the \(T_5\) binary orbit looked best among small homogeneous recursions into an infinite-family theorem.

## Proof structure

The exact product/join calculus gives
\[
d_{j+1}=t^2d_j+t-1,\qquad
a_{j+1}=a_j/t,
\]
and
\[
R_{j+1}=R_j^{t^2}
\left(
t a_j^{t-1}\frac{g(d_{j+1})}{g(td_j)^t}
\right).
\]
Robbins--Stirling bounds yield a uniform upper envelope for the parenthesized factor. The parameter space then splits into:

- a finite core \(2\le t\le19,\ 1\le p\le19\);
- the tail \(2\le t\le19,\ p\ge20\);
- the tail \(t\ge20,\ p\ge1\).

The finite core has 342 pairs. The first uniform envelope excludes 335; six of the remaining seven are excluded after three exact recurrence levels; the sole survivor is \((2,5)\). The two infinite tails are closed by monotonicity of explicit logarithmic majorants.

## Exact replay

Python 3.10 or newer; standard library only:

~~~sh
python3 code/check_balanced.py
python3 -O code/check_balanced.py
~~~

The reports must be byte-identical. The checker uses only integers and fractions.Fraction.

Logarithms are bounded by the exact expansion
\[
\log y
=
2\sum_{n=0}^{N-1}\frac{z^{2n+1}}{2n+1}
+\mathcal R_N,
\qquad
z=\frac{y-1}{y+1},
\]
with an explicit rational geometric-tail bound. It uses 48 terms and the rational enclosure
\[
333/106<\pi<355/113.
\]

The replay certifies:

- 335 finite-core exclusions;
- the seven first-stage exceptional pairs;
- six three-level exceptional exclusions;
- all 18 moderate-arity \(p\)-tails;
- the entire \(t\ge20\) tail;
- the exact level-6 integer inequality giving \(\Lambda_{2,5}>2.8534\);
- the strict comparison \(\log(2.8534)>1.048\).

## Scope

The theorem is restricted to balanced homogeneous recursions \((K^t)^{*t}\) with simplex seeds. It does **not** settle:

- recursions \((K^m)^{*k}\) with \(m\ne k\);
- periodic or variable operation trees;
- the full product/join closure;
- the unrestricted projection-volume asymptotic problem.

The natural next target is the independent-arity family \((K^m)^{*k}\), followed by a Bellman envelope for arbitrary operation trees.

No first-discovery claim is made before a broader literature review.
