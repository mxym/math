# Nearly balanced pairs in posets with arbitrary endpoint constraints

**Yongxian Zhang.** AI-assisted development and internal verification; no external peer review or priority claim.

## Result

Let \(w\ge2\) and let the elements be partitioned into \(w\) specified chains of a common length \(n\). Generate the order by the relations within the chains and any acyclic collection of cross-chain comparisons whose endpoints are both in the first \(k\) or last \(k\) positions of their respective chains. Call these coordinates early and late, respectively. Comparisons within either cap and from early to late are unrestricted; forbid late-to-early generators. This condition concerns generators, not their transitive closure.

Write \(m=n-2k\). For any fixed \(\alpha<1/2\), if \(1\le k\) and \(wk\le\alpha m\), then for any ordered pair of distinct chains \(A,B\) the vertex \(a=A_{k+\lceil m/2\rceil}\) has a partner \(B_j\), \(k\le j\le n-k+1\), with
\[
\left|\Pr[L(a)<L(B_j)]-\frac12\right|=O_\alpha(m^{-1/2})
\]
in a uniform linear extension \(L\), for all sufficiently large \(m\). In particular at width three this permits any fixed \(k/n<1/8\). An explicit finite statement: if \(k\le n/(3w+2)\) and \(m\ge1024\), the left side is at most
\[
\frac{5\sqrt{2m}}{2(m+1)}+e^{-m/200}<\frac16.
\]
Thus the \(1/3\)–\(2/3\) conjecture holds here with balance tending uniformly to \(1/2\). This includes constrained early and late regions of linear length with no restriction on the number or arrangement of the comparisons other than those above. For \(k=0\), equal-length disjoint chains have an exact half pair by symmetry. No claim is made for arbitrary width-three posets.

## 1. Cap compression bounds exceptional conditional coordinates

Give each chain \(n\) independent uniform \([0,1]\) values, then sort within the chain. The resulting shuffle is uniformly distributed: all \((wn)!\) unsorted orders were uniform and each shuffle has \((n!)^w\) preimages. Let \(E\) denote the event that the extra comparisons hold. It depends only on the cap values. Conditioning on \(E\) gives a uniform linear extension, and \(E\) has positive probability because the generators are acyclic.

For chain \(i\), denote the early and late endpoints by \(l_i\) (the \(k\)-th order statistic) and \(u_i\) (the \((n-k+1)\)-st). On the domain of permitted cap coordinates, their joint density with the other cap coordinates is proportional to
\[
W=\prod_{i=1}^w(u_i-l_i)^m.
\]
Indeed the ordered \(m\)-coordinate interior simplex on that chain has volume \((u_i-l_i)^m/m!\). Conditional on all cap coordinates, the chain interiors are independent, each the ordered sample of \(m\) iid uniforms on \((l_i,u_i)\). This follows from the same product-simplex volume.

Fix \(0<\eta<1/3\), and call the caps good when every \(l_i\le\eta\) and every \(u_i\ge1-\eta\). For the early-bad subset where some \(l_i>\eta\), apply the affine dilation that multiplies **all early** cap coordinates by \(0<\rho<1\) and fixes all late coordinates. This maps the cap domain injectively into itself: each within-layer order is preserved, and early-to-late inequalities only improve. Its Jacobian is \(\rho^{wk}\). Every interior interval increases in length, and for at least one chain the former width \(u_i-l_i\) is at most \(1-\eta\) and the gain is at least \((1-\rho)\eta\); thus the weighted density \(W\) gains a factor at least \(((1-\rho\eta)/(1-\eta))^m\). Integrate over the image, which lies inside the full cap domain, and divide by its total integral. The upper bound on the early-bad conditional probability is
\[
\rho^{-wk}\left(\frac{1-\eta}{1-\rho\eta}\right)^m.
\]
The same bound holds for the late-bad set by moving all late coordinates toward \(1\) by the factor \(\rho\) and fixing all early coordinates. Therefore the conditional probability of any bad cap is at most
\[
\epsilon=2\rho^{-wk}\left(\frac{1-\eta}{1-\rho\eta}\right)^m.
\tag{1}
\]
No lower bound on \(\Pr(E)\) is required; it can itself decay exponentially.

If \(wk/m\le\alpha<1/2\), choose \(\eta\) so \(\alpha<\eta/(1-\eta)<1/2\). Then choose \(\rho<1\) close enough to \(1\) so
\[
\log\frac{1-\rho\eta}{1-\eta}-\alpha\log(1/\rho)>0.
\]
This is possible because the left side divided by \(1-\rho\) tends to \(\eta/(1-\eta)-\alpha>0\). Thus \(\epsilon\le2e^{-c_\alpha m}\). For the explicit bound, take \(\eta=3/10\), \(\rho=3/4\), and \(wk\le m/3\). The exponent is at least \(\log(31/28)-\frac13\log(4/3)>1/200\), since the cube of its exponential is \(89373/87808\), and \(\log(1+x)\ge x/(1+x)\) for \(x\ge0\).

## 2. Interpolate after conditioning on the caps

Let \(r=\lceil m/2\rceil\). The normalized \(r\)-th uniform order statistic has beta density
\[
m\binom{m-1}{r-1}x^{r-1}(1-x)^{m-r},
\]
mean \(r/(m+1)\) and variance at most \(1/(4(m+2))\). The central coefficient bound \(4^{-v}\binom{2v}{v}\le1/\sqrt{v+1}\) follows by induction (ratio \((2v+1)/(2v+2)\)). For odd \(m=2v+1\) this bounds the density peak by \(\sqrt{2m}\) using \(x(1-x)\le1/4\). For even \(m=2v\), using \(x^{v-1}(1-x)^v\le 4^{1-v}\) and \(\binom{2v-1}{v-1}=\tfrac12\binom{2v}{v}\) bounds the peak by \(2\sqrt{2m}\). On good caps the interval width is at least \(1-2\eta\), so the conditional density of \(a\) is at most \(2\sqrt{2m}/(1-2\eta)\).

Write \(p_j\) for the conditional probability of \(a\) before \(B_j\) given \(E\), which equals the stated linear-extension probability. As \(j\) runs from \(k\) through \(n-k+1\), \(p_j\) is nondecreasing. For neighboring indices their \(B\)-value gap has conditional mean \((u_B-l_B)/(m+1)\le 1/(m+1)\), including both gaps adjacent to the deterministic endpoints. Independence on fixed caps and the density estimate show
\[
p_{j+1}-p_j\le\frac{2\sqrt{2m}}{(1-2\eta)(m+1)}+\epsilon.
\]
The exceptional event contributes at most its probability.

On good caps \(l_B\le\eta\) and \(u_B\ge1-\eta\). In normalized \(A\)-coordinates the lower threshold \(\eta\) is at most \(\eta/(1-\eta)<1/2\); the upper threshold \(1-\eta\) is at least \(1-\eta/(1-\eta)>1/2\). For sufficiently large \(m\), the beta mean is at a fixed positive distance from the two outer thresholds. Chebyshev gives \(p_k=O_\eta(m^{-1})+\epsilon\) and \(p_{n-k+1}\ge1-O_\eta(m^{-1})-\epsilon\). For \(\eta=3/10\), \(m\ge1024\), each distance is at least \(1/16\), so the bounds specifically use \(64/(m+2)+\epsilon<1/2\). Thus the two endpoints straddle \(1/2\), and the nearest value on the crossing step is at most half the upper bound on the step away. This proves both bounds. A balanced pair is necessarily incomparable.

The same compression inequality handles unequal cap lengths \(k_i^-,k_i^+\) and unequal interiors \(m_i\): replace \(wk\) by the compressed side's total cap dimension, and \(m\) by \(\min_i m_i\). The subsequent interpolation uses the beta density for \(m_A\) and the mean spacing for \(m_B\); in particular it gives the same asymptotic order when all \(m_i\) are comparable. Unsupplied cap sides can be treated as the constant endpoints \(0\) or \(1\).

## 3. An asymmetric width-three witness outside several familiar classes

For \(w=3\), use chains \(A,B,C\), \(k=3\), and arbitrarily large \(n\) satisfying the numerical condition. Generate the additional relations
\[
A_1<B_2,\quad C_1<B_2,\quad B_2<A_{n-1},\quad
B_2<C_{n-2},\quad A_2<B_3.
\]
Its three middle vertices give an antichain, so width is exactly three. Middle vertices of \(A,B\) give an induced \(2+2\), excluding interval orders and semiorders. \(A_2,A_3,B_2,B_3\) induce the \(N\) order, excluding \(N\)-free and series-parallel orders. The Hasse graph has the cycle \(A_1,A_2,B_3,B_2,A_1\), and \(B_2\) has degree six, exceeding the degree-four bound for skew Young diagram posets. The Hasse graph is connected. The incomparability graph also is connected: every vertex off \(C\) is incomparable to a middle vertex of \(C\), and every vertex of \(C\) is incomparable to a middle vertex of \(A\). Thus neither a nontrivial parallel nor ordinal sum applies. Middle vertices have at least \(n-4\) incomparables and the height is at least \(n\), ruling out the thin and low-height cases; there are only three minima.

For triviality of the automorphism group, \(B_2\) is the unique degree-six vertex. Its upper Hasse branches have distinct lengths \(n-2,2,3\), so are fixed pointwise. Of its minimal lower covers, \(B_1\) is the only one with one upper cover, and \(A_1\) is distinguished from \(C_1\) by whether its second upper cover is below \(B_3\). The remaining \(A\) and \(C\) vertices are each the elements whose set of minimal predecessors is respectively \(\{A_1\}\) or \(\{C_1\}\), and these sets are chains. Thus all vertices are fixed.

The example has a genuinely growing subclass. Let \(k\) now vary up to the theorem's bound, and for an arbitrary \(I\subseteq\{3,\ldots,k\}\) add \(A_i<C_i\) for every \(i\in I\). All these relations are covers: a path through an \(A\)-vertex after \(A_i\) would reach the \(C\)-chain strictly after \(C_i\), and no \(B\)-vertex is above \(A_i\) for \(i\ge3\). The four-vertex \(N\), the Hasse cycle and the midpoint \(2+2\) persist. The incomparability graph stays connected: the \(A\)-midpoint is incomparable to every vertex in \(B\) or \(C\); early and middle \(A\)-vertices are incomparable to \(C_1\), and late \(A\)-vertices are incomparable to the \(C\)-midpoint. (Choose midpoints outside the caps.) There is still only one degree-six vertex \(B_2\), with the same upper branches; its three lower covers are still distinguished as before. Once \(C_1\) is identified, the \(C\)-chain is traced by its unique upper covers after ignoring the \(C_1<B_2\) edge. With \(B\) and \(C\) known, the remaining chain \(A\) is known. This identifies all vertices by their chain indices in every isomorphism, so different \(I\) yield nonisomorphic posets. In particular the claim includes exponentially many nonisomorphic asymmetric examples for the same number of vertices, with a linear number of essential cross-chain covers allowed.

The bound is not meant to be optimal for any individual example. The class theorem permits arbitrary (acyclic, forward across caps) comparisons there, including within-cap constraints that can have probability \(\exp(-\Theta(n))\) under the unconstrained shuffle. For example insisting on all \(k\) early elements of \(A\) before \(B_1\) already forces the two-chain projected shuffle to begin with \(k\) copies of \(A\).

## Prior art and limits

See [Aires–Chan–Pak–Panova, arXiv:2609.30888v2](https://arxiv.org/abs/2609.30888), for the current general balance problem and proved classes; [Chan–Pak survey, §13](https://www.math.ucla.edu/~pak/papers/LEsurvey11.pdf), for the geometric approach to balance and earlier structural cases; [Sah, arXiv:1811.01500](https://arxiv.org/abs/1811.01500), for improved width-two results. The [lexicographic-sum transfer theorem of Dolores-Cuenca, Guzmán-Sáenz and Kim](https://arxiv.org/abs/2410.12494) preserves a balanced pair within a substituted non-chain block; it does not supply this across-chain pair when the inflated blocks are chains. A targeted search for endpoint/cap perturbation, shuffle, and order-statistic formulations found no equivalent result. The order-polytope model and order-statistic facts are standard; the bound here combines a cap-domain compression with conditional independence with anti-concentration across an entire chain, and does not assert independent novelty of these tools. The conjecture in general remains open.

[Exact fixture checker](verify-poset-endpoint-cap-balance.js) computes linear-extension counts as three-dimensional lattice-path counts with prerequisite barriers using integer arithmetic. It checks the structural claims on 33 instances (17 base examples and all 16 optional-edge patterns at one size), and balance on those and 4 heavier cap fixtures. These are sanity checks, not prerequisites for the theorem.
