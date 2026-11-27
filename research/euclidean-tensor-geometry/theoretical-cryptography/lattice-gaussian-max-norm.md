# Expected norms of lattice Gaussians: zonoid monotonicity and certified counterexamples

For a lattice \(L\) in Euclidean space and positive definite precision \(P\), write \(D_{L+z,P}\) for the probability of \(x\in L+z\) proportional to \(e^{-x^TPx}\). Consider two assertions for a norm \(f\):

* **Shift:** \(\mathbb E_{D_{L+z,P}} f\ge\mathbb E_{D_{L,P}} f\).
* **Widening:** for centered laws and \(P'\preceq P\), \(\mathbb E_{D_{L,P'}} f\ge\mathbb E_{D_{L,P}} f\).

Both hold for norms that are averages of absolute linear functionals, including **every norm in dimension at most two**. The restriction is material: **shift fails in dimension three** and **widening fails in dimension four**, both for the standard maximum norm, with explicit rational lattices. Thus dimension three is the smallest dimension in which the shift assertion can fail. We do not settle whether dimension three also allows widening failure, or whether widening can fail when the precision varies by a scalar factor only. These are abstract Gaussian-law comparisons, not procedures for solving lattice or cryptographic problems.

## 1. A common positive mechanism

Suppose \(f(x)=\int|\langle v,x\rangle|\,\nu(dv)\) for a finite positive measure \(\nu\) on the unit sphere. Equivalently, the dual unit ball of \(f\) is a zonoid, i.e. a limit of Minkowski sums of centered segments. The representation can be replaced by uniform approximation of support functions on the unit sphere. In dimension two every centrally symmetric polygon is such a sum: pair its opposite parallel edges, then form one centered segment having the length and direction of each edge pair. The sum has the same cyclic boundary edge list as the polygon, so agrees with it after centering. Approximation of centrally symmetric convex bodies by such polygons gives all planar norms.

For a rank-one observable \(H=vv^T\), the shift comparison follows from [Regev–Stephens-Davidowitz, Proposition 4.2](https://arxiv.org/pdf/1502.04796):
\[
 \mathbb E_{D_{L+z,P}} e^{-t(\langle v,X\rangle)^2}
 \le \mathbb E_{D_{L,P}}e^{-t(\langle v,X\rangle)^2}.
\]
Indeed this expectation is the mass for precision \(P+tH\) divided by that for \(P\); normalize each mass by its value on \(L\) and apply the proposition, noting that covariance decreases with precision. Integrating \(1-e^{-tq}\) against the positive square-root integral measure proves the comparison for \(|\langle v,X\rangle|\).

For widening, centered Poisson summation gives \(\mathbb E_{D_{L,P}}\cos(2\pi\langle v,X\rangle)\) as the normalized Gaussian mass of \(L^*+v\) at precision \(\pi^2P^{-1}\). Thus it **decreases** pointwise as the primal law widens, by the same proposition on the dual. The Fourier integral of \(|\langle v,X\rangle|\) is a positive integral of \(1-\mathbb E\cos(2\pi t\langle v,X\rangle)\) against \(t^{-2}dt\), so the mean absolute projection increases. Integrating over \(\nu\) proves both assertions. Uniform approximation is permitted since the laws have finite first moments.

There is an exact limitation to the positive-kernel version of this proof, independent of the counterexamples. For a norm \(f\), the real kernel \(G_f(x,y)=f(x+y)-f(x-y)\) is positive semidefinite on the vector space **if and only if** the dual unit ball is a zonoid. For one absolute linear functional this follows from the scalar identity
\[
 |u+v|-|u-v|=2\operatorname{sgn}(u)\operatorname{sgn}(v)\min(|u|,|v|),
\]
a positive mixture of products of signed threshold indicators, then integrate over directions. Conversely, choose a nonzero point \(w\) at which \(f\) is differentiable. Given finitely many \(x_i\) and scalars \(c_i\) with \(\sum c_i=0\), test the kernel on \(Rw+x_i\). By homogeneity and differentiability, \(f(2Rw+x_i+x_j)=2Rf(w)+D f(w)[x_i+x_j]+o(1)\) as \(R\to\infty\). Its quadratic form in \(c_i\) tends to zero; the other term does not depend on \(R\). So \(\sum c_i c_j f(x_i-x_j)\le0\). By the [Bretagnolle–Dacunha-Castelle–Krivine negative-type characterization of isometric \(L_1\) embedding](https://www.numdam.org/item/AIHPB_1966__2_3_231_0/), \(f\) is a norm represented by an average of absolute linear functionals (write a linear \(L_1\) embedding in a finite coordinate basis). This equivalence does not by itself characterize every possible proof of Gaussian norm monotonicity.

## 2. A finite rigorous three-dimensional shift example

In \(\mathbb R^3\) use precision \(P=I\), norm \(\|\cdot\|_\infty\), and orthogonal lattice generators
\[
 b_1=\frac{2(1,1,3)}{11},\qquad
 b_2=\frac{(1,-1,0)}{12},\qquad
 b_3=\frac{(3,3,-2)}{34}.
\]
Let \(L\) be their integer span, and \(z=b_1/2\). A direct exact interval certificate gives disjoint bounds:
\[
 \begin{array}{c|c}
 \text{law}&\mathbb E\|X\|_\infty\\ \hline
 D_{L,I}&[0.93862140,\ 0.93862141]\\
 D_{L+z,I}&[0.93586970,\ 0.93586971].
 \end{array}
\]
In particular the gap is greater than \(1/1000\). Here are the finite certificate data, including the infinite-tail bound, so the example is not a floating-point claim.

* At offset \(d\in\{0,1\}\), use \(x=(i+d/2)b_1+jb_2+kb_3\). The three independent terms in the squared norm are \((2i+d)^2/11,\ j^2/72,\ 11k^2/578\); each coordinate of \(2244x\) is integral. Truncate at \(|i|\le15,\ |j|\le70,\ |k|\le60\).
* On each one-sided discarded tail the first squared norm contribution is at least \(70\) and each subsequent increment is at least one. Since \(e>2\), the two-sided axis tail mass is at most \(4\,2^{-70}\), and its \((|i|+1)\)-weighted tail is at most \(4( M+3)\,2^{-70}\) for cutoff \(M\). Each whole one-axis mass is at most \(142\) and the \((|i|+1)\)-weighted mass at most \(72\cdot142\). Since \(\|x\|_\infty\le |i|+|j|+|k|+3\), a union bound gives a joint tail smaller than \(3\cdot4(73+2\cdot72)142^2\,2^{-70}<2^{-40}\) for the unnormalized numerator, and also below \(2^{-40}\) for the unnormalized denominator.
* For each retained scalar exponent \(q\), \(0\le q/128\le1\). Enclose \(e^{-q/128}\) by the odd and even alternating Taylor sums of degrees \(23,24\), evaluated exactly with a common integer denominator. Round outward to denominator \(2^{70}\), and square seven times with outward rounding. This encloses \(e^{-q}\). Positive products and sums then enclose the finite denominators and numerators. Add the tail budget to each upper bound and compare fractions with integer cross-multiplication. The accompanying program implements precisely this certificate with 1,057,782 fixed grid terms.

The use of an orthogonal basis is not a contradiction to a coordinatewise product comparison: the maximum norm is measured in the ambient fixed axes, not in the three rotated lattice coordinates.

### Analytic explanation and a full asymptotic family

The example can also be obtained without any finite arithmetic. In the convention \(\widehat F(\xi)=\int e^{-2\pi i\langle \xi,x\rangle}F(x)\,dx\), the tempered-distribution transform of \(f(x)=\|x\|_\infty\) on \(\mathbb R^3\), away from the coordinate planes and from \(\pm\xi_1\pm\xi_2\pm\xi_3=0\), is the smooth function
\[
 -\frac{1}{8\pi^4 \xi_1\xi_2\xi_3}
 \left(
 \frac1{\xi_1+\xi_2-\xi_3}
 +\frac1{\xi_1-\xi_2+\xi_3}
 +\frac1{-\xi_1+\xi_2+\xi_3}
 -\frac1{\xi_1+\xi_2+\xi_3}\right).
 \tag{1}
\]
To verify this, write the norm as the integral of \(1-\mathbf1_{[-t,t]^3}(x)\) over \(t\ge0\), first with a factor \(e^{-\varepsilon t}\). This regularized integral converges to \(f\) in tempered distributions by dominated convergence. The constant contributes only at frequency zero; the other term is the negative integral of the product of three box transforms \(\sin(2\pi \xi_jt)/(\pi\xi_j)\). Expand the sine product and use \(\int_0^\infty e^{-\varepsilon t}\sin(at)\,dt=a/(\varepsilon^2+a^2)\). On any compact set avoiding the stated hyperplanes the limit is smooth and gives (1). In particular it is **positive** at \(u=(1,1,3)\), with value \(1/(45\pi^4)\).

Write \(F(x)=f(x)e^{-\|x\|^2}\). For \(R\to\infty\),
\[
 \widehat F(Ru)=\frac{1}{45\pi^4 R^4}+O(R^{-6}).
 \tag{2}
\]
Indeed multiplication by the Gaussian convolves (1) as a distribution with a Gaussian of total integral one. In a ball of radius \(\alpha R\) around \(Ru\), for small fixed \(\alpha>0\), (1) is smooth; its second derivatives are \(O(R^{-6})\) by homogeneity. Taylor expansion against an even Gaussian cutoff cancels the first derivative. Outside that ball the Gaussian test function has exponentially small Schwartz seminorms, up to powers of \(R\), and the tempered distribution contributes exponentially little. This proves (2), with the same estimate when \(R\) is replaced by \(kR\), \(k\ge1\).

Let \(\theta=u/\|u\|\). First consider a mixed measure with the \(\theta\) coordinate on the grid of step \(h=1/(R\|u\|)\) and ordinary continuum Lebesgue measure on \(\theta^\perp\), using the same Gaussian weights \(e^{-\|x\|^2}\). Compare offsets \(0\) and \(h/2\) along \(\theta\). The Fourier transform of the plane-integrated numerator \(G(t)=\int_{\theta^\perp}F(t\theta+y)\,dy\) is \(\widehat F(\omega\theta)\). Its summable Fourier decay (2) justifies one-dimensional Poisson summation of the continuous, rapidly decaying \(G\). The difference of the two unnormalized sums selects four times the sum over positive odd frequencies, divided by \(h\). The Gaussian normalizers are \(\pi^{3/2}h^{-1}(1+O(e^{-\pi^2/h^2}))\), so the centered minus the shifted expectation is
\[
 \frac{4}{45\pi^{11/2}R^4}\sum_{\substack{k\ge1\\k\text{ odd}}}k^{-4}
     +O(R^{-6})
   =\frac{1}{1080\pi^{3/2}R^4}+O(R^{-6})>0
\]
for large \(R\). Replacing the transverse plane by a sufficiently fine two-dimensional lattice in it preserves the strict inequality, by ordinary Riemann-sum convergence on compact sets and Gaussian tail domination. This produces a family of actual full lattices, independent of the fixed certificate above.

## 3. Turning the shift loss into a widening loss on a centered lattice

Use the explicit \(L,z\) from §2 and \(\varepsilon=1/10000\). In \(\mathbb R^4\) define the full lattice
\[
 L'=\{(x+kz,\varepsilon k): x\in L,\ k\in\mathbb Z\},
 \qquad P_T=\operatorname{diag}(1,1,1,T/\varepsilon^2).
\]
Keep the ordinary maximum norm on all four coordinates. Conditional on \(k\), the first three coordinates have \(D_{L,I}\) if \(k\) is even and \(D_{L+z,I}\) otherwise, since \(2z\in L\). Write \(m_k\) for the conditional four-dimensional mean norm and \(M(T)\) for the unconditional mean. Then \(m_1\le\mathbb E_{D_{L+z,I}}\|X\|_\infty+\varepsilon <m_0-9/10000\), and \(0\le m_k\le1+\varepsilon |k|\) by the certified means.

Here is a finite range in which the reversal already holds. Let \(r=Z_I(z)/Z_I(0)\), where \(Z\) is Gaussian mass. Poisson summation gives \(r\le1\). The normalizer quotient reduces to the first axis alone. The centered mass of that axis is bounded by \(1+\sqrt{11\pi}/2<4\), by the monotone integral bound; the shifted mass is at least \(2(e^{-1/11}+e^{-9/11})\ge24/11\), using \(e^{-x}\ge1-x\). Hence \(r>1/2\).

Group \(k\) by \(j=|k|\). Unnormalized probabilities are \(1\) at zero and \(2r_j e^{-Tj^2}\) for \(j\ge1\), with \(r_j=1\) or \(r\) by parity. Their sum is at most 2 for \(T\ge10\). Differentiate the absolutely convergent Gaussian series: \(M'(T)=-\operatorname{Cov}(m_j,j^2)\). In the pairwise covariance sum over \(i<j\), the contribution from \((0,1)\) is at most \(-9e^{-T}/40000\). All pairs with \(j\ge2\) together have absolute sum at most \(2\sum_{j\ge2} j^2(2+j)e^{-Tj^2}<37e^{-4T}\), using \(j^2\ge4+5(j-2)\) and \(j^2(2+j)\le16\cdot4^{j-2}\). The latter bound is smaller than \(9e^{-T}/40000\) for all \(T\ge10\). Thus \(M'(T)>0\) there. In particular \(P_{10}\preceq P_{11}\) but \(M(10)<M(11)\): widening in one coordinate *decreases* the expected maximum norm. A strict comparison persists under sufficiently small additional widening in the other directions, by continuity at these positive definite precisions.

The known normalized-theta monotonicity and classical \(L_1\) embedding theorem supply the positive class. The explicit maximum-norm examples and the Fourier sign mechanism concern a different issue from the Euclidean assertion in the introduction of the Regev–Stephens-Davidowitz paper; they do not contradict that Euclidean assertion.
