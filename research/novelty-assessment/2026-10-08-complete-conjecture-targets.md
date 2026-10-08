# Two complete-conjecture targets: source and status screen

**Screen date: 8 October 2026.** This is a limited source check, not a proof review or an exhaustive survey. It distinguishes statements explicitly called conjectures in primary sources from the present status of those conjectures. A bounded search with no hit is not evidence of nonexistence or of current open status.

## A. Kahn’s triple-codegree cover conjecture (1994, Conjecture 5.5)

### Exact primary statement

Jeff Kahn, “On a Problem of Erdős and Lovász. II: \(n(r)=O(r)\),” *Journal of the American Mathematical Society* 7 (1994), 125–143, DOI [10.1090/S0894-0347-1994-1224593-5](https://doi.org/10.1090/S0894-0347-1994-1224593-5), §5, printed pp. 140–142. The AMS full text was read through the cited DOI source.

Kahn’s auxiliary-hypergraph formulation is the precise one to use. For fixed c, suppose \(\mathcal H'\) is \(r\)-regular, has at most \(cr\) vertices, every pair of distinct vertices occurs together in an edge, and

\[
\max_{x,y,z\text{ distinct}}d_{\mathcal H'}(x,y,z)=o(r).
\]

Conjecture 5.5 predicts that the minimum number of edges covering all vertices satisfies
\[
\rho(\mathcal H')\le \bigl(c/(c+1)+o(1)\bigr)r.
\]
Kahn presents this as the triple-codegree relaxation of Corollary 5.3, which has the stronger hypothesis that maximum pair-codegree is \(o(r)\).

In the dual language, this is the claimed edge-cover bound for an intersecting \(r\)-uniform family with at most \(cr\) members and maximum common intersection of three distinct members \(o(r)\). The exact primary formulation is safer where the dual family could have repeated edges; do not silently impose simplicity unless it follows from the setup being considered.

Kahn also records the separate Conjecture 5.6: fixed rank bound \(k\), fractional cover/tiling \(t\), maximum triple weight \(\alpha_3(t)\to0\), and local matching-polytope parameter \(b(t)\to\infty\) imply asymptotically integral cover cost. Here MP(X) is the matching polytope on **all subsets of (X) of size at least two**, not merely the graph matching polytope on pairs.

### What Kahn–Kayll establishes, and what remains unverified

P. Mark Kayll, *Asymptotically Good Covers in Hypergraphs: Extended Abstract of the Dissertation*, DIMACS Technical Report 95-55 (December 1995), Theorem 2.1, p. 5, was read in full. Public source: [DIMACS report 95-55](https://archive.dimacs.rutgers.edu/archive/TechnicalReports/TechReports/1995/95-55.ps.gz). For fixed \(k\), a \(k\)-bounded hypergraph and fractional cover \(t\), Kayll proves \(\rho(H)\le(1+o(1))t(H)\) under the two conditions \(\alpha_3(t)\to0\) and \(b(t)\to\infty\). The report identifies this as the dissertation’s main theorem and says the proof would appear in the journal paper below.

Jeff Kahn and P. Mark Kayll, “Fractional v. Integral Covers in Hypergraphs of Bounded Edge Size,” *Journal of Combinatorial Theory, Series A* 78 (1997), 199–235, DOI [10.1006/j.jcta.1997.2761](https://doi.org/10.1006/j.jcta.1997.2761). Bibliographic record and abstract were checked; the journal full text was not available in the prior screen. Kayll’s readable primary extended abstract proves the theorem that resolves Conjecture 5.6 (indeed in a fractional-cover form), but its extra \(b(t)\to\infty\) hypothesis is not part of Conjecture 5.5.

Kahn explicitly says he did not see whether 5.6 implies 5.5. The readable Kahn–Kayll theorem does not establish that missing implication. A prior limited screen of accessible citing material did not verify a later proof or counterexample of the full Conjecture 5.5. Therefore the defensible status here is **“not resolved by the Kahn–Kayll theorem as checked; later resolution status not verified in this limited search.”** Do not state that 5.5 is currently open, and do not treat the repository’s affine example as a counterexample: it satisfies the conjectured bound.

## B. Four equal Gaussian masses and the regular tetrahedron

### Exact prior conjecture already matching the global target

The requested first-Hermite objective is
\[
\mathcal E(A_1,\ldots,A_k)=\sum_i\left\|\int_{A_i}x\,d\gamma_d(x)\right\|^2.
\]
It is precisely the derivative at \(\rho=0\) of the Gaussian noise-stability sum \(\sum_i\int 1_{A_i}T_\rho1_{A_i}\,d\gamma_d\); Steven Heilman writes this identity as equations (12)–(14).

The direct prior statement is **Steven Heilman, “Stable Gaussian Minimal Bubbles,” arXiv:1901.03934v1 (2019)**, §1.4, Problem 1.15 and Conjecture 1.16 (printed p. 8). The paper states that for prescribed Gaussian masses a_i, one should maximize the sum of squared centered first moments, with the centering vector w/a_i specified from the translated regular-simplex cones in equation (1); Conjecture 1.16 predicts that all maximizers are simplicial cones over a regular simplex when the ambient dimension is at least m-1. The preceding paragraph on printed p. 4 says explicitly that, when m>3, this first-moment quantity “should be maximized” by the sets in the simplex conjecture and “this is still an open problem [IM12].”

For m=4 and equal masses a_i=1/4, the regular-simplex cones are centered without translation, so w=0. Thus the proposed optimizer is exactly the regular tetrahedral conical partition, and the objective differs from \(\mathcal E\) only by the paper’s fixed positive normalization factor. The conjecture ranges over **all measurable partitions** of \(\mathbb R^d\), not just conical partitions; its asserted conclusion is that an optimizer is conical over a regular simplex. It applies for every d≥3. This is a direct, explicit prior conjecture for the requested complete target, not merely an adjacent perimeter or noisy-partition problem.

Steven Heilman, “Euclidean Partitions Optimizing Noise Stability,” *Electronic Journal of Probability* 19 (2014), no. 71, 1–37, arXiv:[1211.7138](https://arxiv.org/abs/1211.7138), was read in full. Its Conjecture 1 is the equal-measure Standard Simplex Conjecture for the full positive-correlation noise-stability objective. The paper proves only k=3 and sufficiently small positive correlation (Theorem 1.2 / Theorem 7.2). More specifically, its Conjecture 3, printed pp. 36–37, states for k=4,n=3 that a maximizer of the first-moment functional \(\psi_0\) among equal-mass fractional partitions must be simplicial conical. Heilman says the unconstrained-mass analogue is known, while the equal-volume constraint causes difficulty. This is a direct low-dimensional open formulation of the four-cell first-Hermite question. The 2014 paper says the k≥4 Standard Simplex Conjecture remains entirely open in that work; that historical statement is not by itself a claim about its 2026 status.

### Sources that do not settle this target

- Heilman 2019’s principal theorems concern Gaussian perimeter (multi-bubble) minimization and stability. Those are not the first-Hermite maximization problem. The paper itself separates the Propeller/first-moment conjecture from the Gaussian multi-bubble theorem.
- Abhijeet Mulgund, “Stochastic Domination of Gaussian Maxima by the Regular Simplex,” arXiv:[2609.28452](https://arxiv.org/abs/2609.28452), v2, 27 September 2026, was read in full. Theorem 1.1 compares the CDF of the maximum of a centered unit-variance Gaussian vector with the regular-simplex Gaussian maximum, with equality characterization; Corollary 1.2 gives the circumscribed-simplex Gaussian-volume inequality. Theorem 6.2 applies this to equal-energy signal identification with an inactive state and false-alarm constraint. These optimize Gaussian maxima/decoding geometry, not the first-moment sum over arbitrary equal-mass measurable partitions. No direct implication to the target was found in the theorem statements or applications checked.

### Status statement

The tetrahedral first-Hermite global optimizer is an explicitly stated prior conjecture (Heilman 2019, Conjecture 1.16; already isolated for k=4,d=3 in Heilman 2014, Conjecture 3). The checked Heilman sources present it as unresolved, and the 2026 Mulgund theorem addresses a different optimization problem. This screen did not verify a later theorem settling or refuting the exact equal-mass partition conjecture. That is a limited status finding, not a proof that it remains open as of the screen date.

## Reading and search boundaries

Primary full text read for this screen: Heilman 2014 and Heilman 2019; Mulgund 2026. Kahn 1994 and Kayll’s DIMACS 1995 extended abstract were full-text reads in the prior repository source screen; the Kahn–Kayll 1997 journal paper was checked only at abstract/metadata level there. This update does not re-run an exhaustive citation search, and none of its negative search results supports a priority claim.

## Follow-up: unequal-mass noise-stability counterexamples versus the first-moment endpoint

The arXiv record for Heilman’s *Stable Gaussian Minimal Bubbles* (1901.03934) has one version, v1, dated 13 January 2019; the arXiv API lists no v2 or later. Its Conjecture 1.16 in v1 includes arbitrary positive prescribed masses and the regular-simplex-cone conclusion. The separately posted *Structure of Gaussian Minimal Bubbles*, arXiv:1805.10203v3 (9 July 2021), is a different paper about Gaussian perimeter; it is not a later correction of 1901.03934 and does not contain Problem 1.15 / Conjecture 1.16.

The cited unequal-mass noise-stability result is Steven Heilman, Elchanan Mossel, and Joe Neeman, “Standard Simplices and Pluralities are Not the Most Noise Stable,” *Israel Journal of Mathematics* 213 (2016), no. 1, 33–53, arXiv:[1403.0885](https://arxiv.org/abs/1403.0885), v3. Its abstract and Theorem 2.6 state that for \(k\ge3\), unequal prescribed cell measures, and positive noise parameter \(0<\rho<1\), a shifted flat/simplex partition is not noise-stability optimal. This result concerns each positive-\(\rho\) functional. It does **not** state that the derivative at \(\rho=0\), equivalently the first-Hermite squared-centroid objective, is larger for a competitor. Pointwise strict improvement for every \(\rho>0\) alone is not the same theorem as a strict inequality of the right derivatives at zero. Heilman 2014 likewise cites this positive-noise unequal-mass failure and then poses a separate problem of identifying the optimizer for fixed positive noise, \(k=3,n=2\); that is not the \(\rho=0\) endpoint. Heilman 2019 explicitly calls the \(m>3\) first-moment problem open.

Accordingly, the cited unequal-mass noise-stability counterexample is not, as stated in its abstract or Theorem 2.6, an already published counterexample to the first-moment Propeller conjecture. The supplied tetrahedral facet-exchange calculation is a candidate direct challenge to Conjecture 1.16, but this literature update does not validate that calculation. Its proof status and any resulting correction to the 2019 conjecture require separate mathematical review. No priority or novelty claim is made here.
