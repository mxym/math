# Proof

## 1. Model and theorem

Fix a sensitivity \(\Delta>0\), \(0<\delta<1\), and loss exponent \(p>0\). The input-independent additive noise law \(\mu\) is any Borel probability on \(\mathbb R\), with the same constraint as equation (7) of Geng–Ding–Guo–Kumar:
\[
 d_{\rm TV}(\mu,\tau_h\mu)\le\delta\quad\text{for all } |h|\le\Delta.   \tag{1}
\]
Here \(\tau_h\mu\) is the law after adding \(h\); \(d_{\rm TV}\) is the supremum over measurable events, or half the total variation norm of the signed difference. Rescaling \(X=\Delta Y\) reduces to \(\Delta=1\) and multiplies the cost by \(\Delta^p\).

In the symmetric decreasing class, the authors' Theorems 2 and 3 yield the optimum at
\[
 \mu_\alpha=\alpha\,\delta_0+(1-\alpha)\,{\rm Unif}[-L/2,L/2],
 \quad L=\frac{1-\alpha}{\delta-\alpha},\qquad
 \alpha=\max\{0,(p+1)\delta-p\}.                                      \tag{2}
\]
In (2), \(\delta_0\) is a point mass, not a privacy parameter. We have \(0\le\alpha<\delta\), hence \(L>1\) and \(\alpha+(1-\alpha)/L=\delta\).

**Theorem.** The restricted minimum from (2) equals the infimum over all laws in (1) if and only if
\[
 p=1,\qquad
 \left(\delta\ge \frac12\quad\text{or}\quad
       \delta=\frac1{2k}\text{ for some integer }k\ge1\right).          \tag{3}
\]
In the remaining cases there is an explicit improved law. No assertion about the exact unrestricted infimum is made in those cases.

## 2. A shift-uniform perturbation lemma

Let \(L>1\). Write the continuous density in a translated coordinate \(t=x+L/2\), on \([0,L]\), as
\[
 f(t)=\frac1L+\eta g(t),
\]
and extend \(f\) by zero outside the interval. Suppose \(g\) is a one-periodic Lipschitz function on the real line, with zero integral on one period and also on \([0,L]\). Assume \(f(t)\ge b>0\) on \([0,L]\), and that \(K=\eta\operatorname{Lip}(g)\) (with \(\eta>0\)) satisfies \(LK/2\le b\). Then \(f\) is a probability density, and its privacy level in (1) is exactly \(1/L\) for \(\Delta=1\).

Indeed, for \(0\le h\le1\), split the integral of \(|f(t)-f(t-h)|/2\) into the boundary contributions and the overlap:
\[
 \frac12\int_0^h f(t)\,dt+\frac12\int_{L-h}^L f(t)\,dt
 +\frac12\int_h^L |f(t)-f(t-h)|\,dt.                                  \tag{4}
\]
At \(h=1\) the last integral vanishes by periodicity within the overlap; each length-one boundary integral is \(1/L\). For smaller \(h\), the first two terms together are at most \(1/L-b(1-h)\). For \(t\in[h,L]\), \(g(t-h)=g(t-h+1)\), so the integrand in the last term is at most \(K(1-h)\); the comparison point \(t-h+1\) may lie outside \([0,L]\), and this bound is for the **periodic extension** \(1/L+\eta g\), not the zero extension of \(f\). Thus the overlap contribution is at most \(LK(1-h)/2\). Combining the bounds proves the result for every real \(h\) in the interval, and negative shifts give the same distance by translation invariance.

For \(h\ne0\), if \(\nu\) has density \(f\) in the centered coordinate, then the signed difference between \(\alpha\delta_0+(1-\alpha)\nu\) and its \(h\)-translate has a singular and an absolutely continuous part, which are mutually singular. Hence
\[
 d_{\rm TV}\big(\alpha\delta_0+(1-\alpha)\nu,\,
             \tau_h[\alpha\delta_0+(1-\alpha)\nu]\big)
   =\alpha+(1-\alpha)d_{\rm TV}(\nu,\tau_h\nu).                         \tag{5}
\]
At \(h=0\) the distance is zero. Therefore changing only the continuous part of (2) by a perturbation from this lemma keeps exactly the same privacy budget.

## 3. The explicit bumps and their cost

Let
\[
 T(u)=(1-|u|)_+,\qquad P(u)=2T(2u)-T(u).
\]
This even, piecewise linear function vanishes outside \([-1,1]\), has absolute value at most one, Lipschitz constant three, and integral zero. On \(0<|u|<1/3\) it is positive, and on \(1/3<|u|<1\) it is negative. Its absolute and squared moment integrals are
\[
 \int |u|P(u)\,du=-1/6,\qquad
 \int u^2 P(u)\,du=-1/8.                                               \tag{6}
\]
For example \(\int |u|^j T(u)du=2/((j+1)(j+2))\) for \(j\ge0\), and the change of variables in \(2T(2u)\) proves the two values and the zero integral.

Put \(m=\lfloor L\rfloor\) and \(r=L-m\). Construct \(g\) in \([0,1]\) from disjoint bumps \(P((t-c)/a)\) or their negatives on intervals \([c-a,c+a]\) of common halfwidth \(a>0\). Each interval lies in \([0,r]\) or \([r,1]\). Make the choice symmetric under \(t\mapsto r-t\bmod 1\), and extend periodically. The endpoints of each bump are zero. All nonzero contributions within \([0,L]\) come from complete copies (also in the final \([0,r]\) piece when chosen). Thus both integrals in the lemma vanish, \(\|g\|_\infty\le 1\), and \(\operatorname{Lip}(g)\le 3/a\), including across periods. Taking
\[
 \eta=\frac{a}{4L^2},\qquad
 b=\frac1L-\eta\ge\frac7{8L},\qquad
 K=\frac{3}{4L^2}
\]
gives \(LK/2=3/(8L)<b\), because \(a\le 1/2\) and \(L>1\). The same symmetry makes the final continuous law even in \(x=t-L/2\).

For a single positive bump with center \(C=c+j-L/2\) in the \(x\) coordinate, its contribution to a loss \(\varphi\), divided by its positive scale \(\eta a\), is
\[
 \int_0^1 \big(\varphi(C+au)+\varphi(C-au)\big)P(u)\,du.                \tag{7}
\]
By evenness and zero integral of \(P\), one can subtract the value of the bracket at \(u=1/3\). If the bracket is strictly increasing with \(u\), (7) is strictly negative; if strictly decreasing it is strictly positive. Strict convexity of \(\varphi\) on the interval gives the first case: for \(0\le v<u\), \(C\pm av\) are convex combinations of the two outer points \(C\pm au\), and adding the strict inequalities gives the claim. Strict concavity gives the second case by the reverse inequalities.

- **\(p>1\).** Use one positive bump filling the interval \([r,1]\) each period, of halfwidth \(a=(1-r)/2\). The loss \(|x|^p\) is strictly convex on \(\mathbb R\); every complete copy strictly decreases the cost. In particular for \(p=2\), (6) and the zero mass and first moment of the bump give an exact continuous-component decrease of \(m\eta a^3/8\). At \(\delta=1/2\), \(\Delta=1\), this decreases MSE from \(1/3\) to \(1/3-1/1024\).
- **\(0<p<1\).** Let \(w=(1-r)/2\) and \(c=(1+r)/2\). Use two **negative** bumps of halfwidth \(a=w/4\), with centers \(c-w/2\) and \(c+w/2\). They lie in \((r,1)\), are disjoint, and their intervals avoid \(c\). If \(m\) is odd, \(L/2\bmod1=c\); if \(m\) is even, \(L/2\bmod1=r/2\) lies outside both supports. Consequently no copied bump meets \(x=0\). The loss \(|x|^p\) is strictly concave on each of the two open half-axes, so the integral for a positive bump would be strictly positive. Its negative strictly decreases the cost.
- **\(p=1\) and \(L\) is not an even integer.** If \(m\) is even, then \(r>0\); place one positive bump in \([0,r]\), filling it. If \(m\) is odd, fill \([r,1]\). The phase midpoint in each case is \(L/2\bmod1\), so exactly one copy is centered at \(x=0\). Other copies lie entirely in one half-axis, where the loss \(|x|\) is affine and their mass and first moments vanish. The unique central copy yields the strict continuous-component decrease \(\eta a^2/6\) by (6).

All comparisons remain strict with (5), because \(1-\alpha>0\) and the atom does not change. In (2) for \(p=1\), \(L=2\) if \(\delta\ge1/2\), and \(L=1/\delta\) otherwise. This proves strict suboptimality in exactly the asserted nonexceptional cases.

## 4. A lower certificate for absolute loss over all laws

No regularity of the noise law is needed for this part. From (1) at \(h=1\), by taking the difference of two half-line probabilities, for every real \(a\)
\[
 \mu([a,a+1))\le\delta.                                               \tag{8}
\]
For an integer \(k\ge1\), let \(w_k\ge0\) be constant on each \([j,j+1)\), \(j=-k,\ldots,k-1\), with value \(k-|j+1|\); let \(w_k=0\) on the complement. Then \(\int w_k=k^2\), and for all \(x\),
\[
 (k-|x|)_+ = \int_{\mathbb R}w_k(a)\mathbf 1_{\{a\le x<a+1\}}\,da.      \tag{9}
\]
Indeed the right side is \(\int_{x-1}^x w_k\), a continuous function linear on each unit interval, and equals \((k-|x|)_+\) at each integer \(x\).

By nonnegative Fubini, (8) and (9) give
\[
 k-\mathbb E|X|\ \le\ \mathbb E(k-|X|)_+
         \ \le\ \delta k^2,\qquad
 \mathbb E|X|\ \ge\ k-\delta k^2.                                     \tag{10}
\]
Alternatively, (10) follows directly from the interval anti-concentration principle in Awan–Ramasethu Lemma 3: the triangle inequality gives \(d_{\rm TV}(\mu,\tau_k\mu)\le k\delta\), so every interval of length \(k\) has mass at most \(k\delta\) (the length-\(k\) instance of the bound in their Theorem 5 for \((0,\delta)\)). Integrating over starting points in \([-k,0]\) gives (10), since \((k-|x|)_+=\int_{-k}^0\mathbf 1_{\{a\le x<a+k\}}\,da\). Thus the lower inequality is an elementary consequence of known anti-concentration, not a new general inequality in \(f\)-DP.

For \(\delta=1/(2k)\) equality is attained by the uniform law on \([-k,k]\): its total variation for a shift of magnitude \(h\le1\) is \(h/(2k)\), and its absolute cost is \(k/2\). For \(\delta\ge1/2\), take \(k=1\) in (10). The law with atom \(2\delta-1\) at zero and remaining mass uniform on \([-1,1]\) has cost \(1-\delta\) and exactly this privacy budget, by (5). These are precisely the corresponding optimizers (2).

This proves (3). The argument shows why absolute loss has special exact regimes without implying the envelope (10) is attained at all intermediate \(\delta\). The result is not an unrestricted optimizer formula when (2) is suboptimal.
