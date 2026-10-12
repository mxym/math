# Random-determinant rigidity and explicit spectral amplification

**Entry 005, version 3 — 7 October 2026. Complete written proof draft; exact finite replay.**

Read the [manuscript](paper.md), [proof audit](PROOF_AUDIT.md), and [research record](RESEARCH_LOG.md). This continuation preserves [v1.1](../v1.1/) and [v2](../v2/README.md). Its inherited geometric formulas and the earlier spectral reduction are explicit dependencies, not duplicated novelty claims.

## What is added

For every full-dimensional convex body in dimension $d$, the projection-cone invariant now has a complete lower-bound equality classification:

$$a(K)=\frac1{d+1}\quad\Longleftrightarrow\quad K\text{ is a simplex}.$$

Version 2 established this only for polytopes. The proof here treats arbitrary centered probability laws first, and therefore does not infer equality from continuity of strict inequalities. For fixed $d$ and every $\varepsilon>0$, near equality also forces

$$S\subseteq K\subseteq z+(1+\varepsilon)(S-z)$$

for every maximum-volume inscribed simplex $S$ with centroid $z$. The tolerance $\delta(d,\varepsilon)>0$ is uniform but nonexplicit.

For centrally symmetric convex bodies, we prove the sharp bound $a(K)\le1/2$. Parallelotopes attain it in every dimension, as do all centrally symmetric planar bodies and products of such planar bodies and intervals. The octahedron has $a=15/32$, so planar constancy does not extend to every symmetric body in higher dimensions. A full higher-dimensional upper-bound equality classification is not asserted.

For independent centered samples with finite first moment and spanning support, put

$$A=\mathbb E|\det(X_1,\ldots,X_d)|,\qquad
B=\mathbb E|\det((X_1,1),\ldots,(X_{d+1},1))|.$$

The underlying theorem is $A\le B<(d+1)A$, with $A=B$ exactly for simplex-vertex laws. It includes an exact cancellation-defect identity, finite sign-changing witnesses on at most $d+2$ support points, and a family approaching the strict upper constant. The inequalities alone are elementary; the equality analysis and geometric consequences are the reason for using this formulation.

Finally set $\lambda=(aR/g(d))^{1/(d+1)}$, as in the v2 spectral supplement. Every integer $k\ge1$ satisfying

$$k\lambda(K)^2\ge4a(K)^2(d+1)$$

gives the explicit strict amplification

$$\lambda\bigl(K^{*k}\times K^{*k}\bigr)>\lambda(K).$$

A Cartesian square suffices. The proof is elementary and the threshold and comparison have rational cross-powered forms. No finite-dimensional body can attain the spectral supremum in any product/join-closed class. This strengthens v2's nonattainment for the different functional $R^{1/d}$; it does not determine the optimal asymptotic constant.

## Replay

Python 3.10 or newer, standard library only. From this directory:

```sh
python3 code/check_manifest.py
python3 code/generate.py --output /tmp/005-v3-exact.json
cmp certificates/exact.json /tmp/005-v3-exact.json
python3 code/check.py certificates/exact.json --self-test --report /tmp/005-v3-check.json
python3 -O code/check.py certificates/exact.json --self-test --report /tmp/005-v3-optimized.json
cmp results/check.json /tmp/005-v3-check.json
cmp /tmp/005-v3-check.json /tmp/005-v3-optimized.json
```

The producer uses subset sums and Gaussian elimination. The independent checker enumerates ordered tuples and uses a permutation determinant; it imports no producer code. The exact replay covers **23 rational laws, 18,199 ordered lifted tuples, 1,149 balanced-sign tests, five geometric spectral-amplification recipes, all 126 horizontal/lifted octahedron minors, and seven rejected deliberate corruptions**. Both ordinary and optimized Python modes give identical reports.

The [certificate](certificates/exact.json), [normal report](results/check.json), [optimized report](results/optimized_check.json), and [run log](results/run.txt) record the finite evidence. The [manifest](MANIFEST.json) pins the version files and the two inherited v2 proof inputs. A hash verifies file identity, not theorem correctness.

The general probability laws, Hausdorff-continuity and rigidity argument, affine compactness argument, and all-dimension amplification are written proofs. Finite tests do not replace those arguments. The verification is algorithmically separate exact checking, not external human peer review or full proof-assistant formalization.

## Scope and remaining questions

The recursive-class optimal spectral supremum remains undetermined. No improvement of v2's certified $2.8534<\Lambda<2.8535$ orbit is claimed. No explicit geometric stability exponent, full symmetric upper-equality classification in higher dimensions, or unrestricted projection-volume extremizer is established here.

The manuscript identifies classical cone-volume and random-simplex background and the related cone literature. The focused search is not an exhaustive novelty check. No first-discovery or best-known unrestricted bound is claimed. Authorship is the mxym repository account, with AI assistance and no asserted institutional affiliation.
