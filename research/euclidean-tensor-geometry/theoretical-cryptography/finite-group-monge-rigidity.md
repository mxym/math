# Dimension-free rigidity of orderable convolution costs

This note classifies when explicitly given finite-group pairwise cost tables can be made Monge by ordering the labels. It gives a stability version and a binary graph-cut specialization on arbitrary synthetic graphs. It does not give a recovery algorithm for noisy cryptographic samples, and the ordering hypothesis is not claimed for a standard noise model.

## 1. Single-table theorem

Let \(G\) be a finite group; no commutativity is required. For \(f:G\to\mathbb R\), consider the convolution cost \(C(x,y)=f(x^{-1}y)\). Given total orders on its rows and columns, let its defect be the maximum of zero and all values
\[
    C(x,y)+C(x',y')-C(x,y')-C(x',y)
            \qquad(x<x',\ y<y').
\]
Call \(\varepsilon(f)\) the smallest defect over arbitrary independent row and column orders. Define \(\mathcal B\) to consist of all constants and all \(x\mapsto a+b\chi(x)\), where \(\chi:G\to\{+1,-1\}\) is a nontrivial group character. Then
\[
   \frac{1}{16}\operatorname{dist}_{\infty}(f,\mathcal B)
     \le\varepsilon(f)
     \le4\operatorname{dist}_{\infty}(f,\mathcal B).                       \tag{1}
\]
If \(G\) admits no nontrivial character into \(\{+1,-1\}\), the first constant improves to \(1/2\). In particular the exact orderable convolution costs are precisely constants or costs taking one value on each of the two cosets of one index-two subgroup. For odd-order groups that means just constants. In the cyclic even case the only nonconstant possibility is a function of parity.

The optimal row and column orders may differ. A near-Monge condition here controls all rectangles, not merely adjacent \(2\)-by-\(2\) rectangles. Replacing it by adjacent control would accrue a size-dependent error when summing small rectangles.

## 2. Approximate sorting forces two translation classes

Fix row and column orders with defect at most \(\varepsilon\ge0\). For \(t\in G\), set \(g_t(z)=f(tz)-f(z)\). For every \(x\), comparison of the two rows indexed by \(x\) and \(xt^{-1}\) shows that the sequence \(g_t(x^{-1}y)\), as \(y\) follows the fixed column order, is either \(\varepsilon\)-increasing or \(\varepsilon\)-decreasing. Here \(\varepsilon\)-increasing means earlier value \(\le\) later value \(+\varepsilon\), and \(\varepsilon\)-decreasing reverses the roles. Which orientation applies depends on the row order. For \(t\) equal to the identity the assertion is immediate.

An \(\varepsilon\)-increasing list differs in every position by at most \(\varepsilon\) from its increasing sort. In fact if position \(j\) exceeds the \(j\)-th order statistic by more than \(\varepsilon\), every position at or after \(j\) strictly exceeds that order statistic, an impossibility. If position \(j\) is more than \(\varepsilon\) below it, all positions at or before \(j\) fall strictly below it, again impossible. Reverse the order for decreasing lists.

Every translation of \(g_t\) is therefore in one of two closed sup-norm balls of radius \(\varepsilon\), about the increasing and decreasing sorts of the same multiset. If \(\operatorname{osc}(g_t)\le4\varepsilon\), its mean zero gives \(\|g_t\|_\infty\le4\varepsilon\). Otherwise the two centers are at distance \(\operatorname{osc}(g_t)>4\varepsilon\), so orbit points in one ball have mutual distance at most \(2\varepsilon\), and those in different balls are at distance strictly greater than \(2\varepsilon\). Thus the relation “distance at most \(2\varepsilon\)” is an equivalence relation on the translation orbit with at most two classes. Both occur: if all the translates are in one class, averaging them to zero gives \(\|g_t\|_\infty\le2\varepsilon\), contradicting the oscillation assumption.

Translations preserve sup distance and act transitively on this orbit. Their induced permutation on the two classes furnishes a nontrivial \(\{+1,-1\}\)-character, with kernel an index-two normal subgroup \(H_t\). This is a group homomorphism using the action \(h\cdot g(z)=g(h^{-1}z)\); inverses of translations trace the same orbit. Averaging \(g_t\) over \(H_t\) changes it by at most \(2\varepsilon\) in sup norm, since each summand is in its own class. The result is constant on each of the two left cosets of \(H_t\), and has mean zero. Hence it is \(c_t\chi_t\) for a nontrivial character \(\chi_t\). In particular, with \(\delta=4\varepsilon\), each \(g_t\) has a mean-zero approximant \(c_t\chi_t\) of error at most \(\delta\), allowing the zero approximant.

## 3. All large derivatives use one character

Distinct homomorphisms into \(\{+1,-1\}\) are orthogonal for the uniform measure on \(G\); their product is a nontrivial homomorphism and has mean zero. The Fourier coefficient in any such real character changes by at most the sup-norm error. Use
\[
       g_{st}(z)=g_t(z)+g_s(tz)
\]
and suppose two of the selected approximants to \(g_t,g_s\) have coefficients of magnitude strictly larger than \(3\delta\) on different characters. Their sum with the indicated translation still has these two coefficient magnitudes: left translation only changes the second sign. The derivative \(g_{st}\) is within \(2\delta\) of that sum, so has coefficients of magnitude strictly greater than \(\delta\) on both characters. But it is within \(\delta\) of at most one nontrivial-character term, contradiction.

There is therefore at most one character among the approximants whose coefficients have magnitude greater than \(3\delta\). Replace all other approximants by zero at error at most \(4\delta\), and average over \(t\). Since the mean of \(g_t(z)\) over \(t\in G\) is \(\bar f-f(z)\), we obtain an approximant to \(f\) in \(\mathcal B\) at distance at most \(4\delta=16\varepsilon\). If there is no index-two subgroup, the large-oscillation case in Section 2 is impossible. A derivative at a pair realizing the oscillation of \(f\) has one value at least that oscillation, so \(\operatorname{osc}(f)\le4\varepsilon\). Its best constant approximation is within \(2\varepsilon\).

Conversely a single-character cost has the form \(a+b\chi(x)\chi(y)\). Order the two cosets in blocks at each end, selecting one reversal if necessary so the mixed difference is nonpositive. Constants are immediate. Perturbing any table by at most \(d\) in sup norm adds at most \(4d\) to a rectangle defect. This proves (1), including the exact iff at defect zero. As a concrete necessary bound, if \(f\) has a unique strict minimizer with a gap \(\Delta\) to the other values and \(|G|>2\), every member of \(\mathcal B\) is at distance at least \(\Delta/2\), because each coset containing that minimizer contains another element. Hence \(\varepsilon(f)\ge\Delta/32\), or \(\Delta/4\) when there is no index-two subgroup.

## 4. Simultaneous orders on a graph

Let \(G\) label every vertex of a finite undirected graph without loops. Put a cost \(f_e(x^{-1}y)\) on each oriented edge presentation \(e=(u,v)\), with arbitrary additional unary costs at vertices. A simultaneous set of label orders must use one order per vertex, shared by all incident tables. The following is the exact structural criterion for all individual edge tables to become Monge at once:

1. Each nonconstant \(f_e\) has the form \(a_e+b_e\chi_e\), \(b_e\ne0\).
2. The characters \(\chi_e\) agree throughout each connected component formed by the nonconstant edges.
3. In each such component the signed graph with edge signs \(-\operatorname{sign}(b_e)\) is balanced: its product of signs along every cycle is \(+1\).

To prove necessity of the second condition, for a nonconstant term, take a pair from distinct character cosets at one end. Comparison with every cross-coset pair at the other end forces a consistent relative order there, since changing the sign of one such pair changes the nonzero mixed difference from negative to positive. Thus each end must group its two character cosets into contiguous blocks. Two distinct index-two characters cannot both have their two equal-size cosets contiguous in one total order: such a partition must cut at the midpoint. For the third condition let \(\tau_u\) be the character value on the first block at \(u\). The mixed difference on a cross-coset rectangle is \(4b_e\tau_u\tau_v\). Hence \(\tau_u\tau_v=-\operatorname{sign}(b_e)\). The cycle-product criterion is necessary by multiplication and sufficient by assigning \(\tau_v\) along a spanning tree, as in [Harary's balance criterion](https://doi.org/10.1307/mmj/1028989917). These assignments and block orders also prove sufficiency.

For explicit rational costs the criterion is polynomially checkable in table bit length. For an arbitrary \(G\) given by its multiplication table, the binary-valued homomorphisms are obtained by solving the linear equations \(\lambda(xy)=\lambda(x)+\lambda(y)\) over \(\mathbb F_2\), and there are at most \(|G|\) such homomorphisms: independent ones give a surjective map onto the corresponding binary vector space. For each character, the nearest coset-constant values in sup norm are the midranges on its two cosets; also check the best constant. Then verify character agreement and balance. For exact qualifying data, minimize each unary term separately inside each of the two cosets and reduce the remaining energy to one binary submodular graph-cut problem, using the now attractive edge signs. This is the usual binary graph-cut result, not an assertion that arbitrary graphs of such tables are tractable: the compatibility hypothesis is essential. The optimization statement refers only to explicit mathematical cost tables.

There is a uniform stability counterpart. Suppose some simultaneous orders give all edge rectangles defect at most \(\varepsilon\). Select an approximant in \(\mathcal B\) for each \(f_e\), at distance at most \(16\varepsilon\) by (1). Replace any approximation with \(|b_e|\le17\varepsilon\) by its constant part. The new uniform edge error is at most \(33\varepsilon\). The remaining nonconstant terms are exactly Monge under the original simultaneous orders. Indeed a forbidden positive rectangle in the retained approximant would have value \(4|b_e|>68\varepsilon\), so the true rectangle would be greater than \(68\varepsilon-64\varepsilon>\varepsilon\) when \(\varepsilon>0\), and strictly positive when \(\varepsilon=0\). This is impossible. Thus a system of simultaneous orders with small defect is uniformly close to the exact balanced binary class. The nearest coset-constant calculations produce these local approximants without having to find the originally promised orders; verify the exact compatibility of the resulting tables directly. The approximating energy, with unchanged unary terms, differs uniformly from the original by at most \(33\varepsilon |E|\). This is an additive objective comparison, not exact optimization of the perturbed original.

## 5. Prior work and scope

[Cechlárová–Szabó](https://www.sciencedirect.com/science/article/pii/0012365X90901436) studies recognition of arbitrary independently permutable Monge matrices; [Hütter–Mao–Rigollet–Robeva](https://arxiv.org/abs/1904.03136) studies statistical estimation of Monge/pre-Monge matrices under additive observations. Those results address different questions from the stability of the intersection with group-convolution tables. [Kolmogorov–Zabih, Theorem 4.1](https://www.robots.ox.ac.uk/~cvrg/trinity2005/kolmogorov_zabih_pami04.pdf) is the binary pairwise cut criterion used in the positive case. Harary's criterion supplies exactly the already known sign compatibility. The increment here is the dimension-independent sorting and translation rigidity in (1) and its quantitative simultaneous version for convolution costs, not the min-cut optimization mechanism.

No conclusion is drawn about a representation using auxiliary variables or a different algebraic algorithm when the ordering criterion fails, and non-Monge does not imply computational hardness. No implementation is provided for applying this result to actual cryptographic data. The adjacent verifier only checks finite structural identities and toy cost tables.
