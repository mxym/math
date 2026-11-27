# Sharp cumulant bounds at the lattice smoothing width

**Scope:** abstract lattice Gaussians, including the canonical lattices that occur in Ring-LWE. This result concerns the covariance and higher derivatives of their partition functions, not a hardness reduction, an implementation, or any encryption scheme.

## 1. Normalization and main statements

Let \(L\subset\mathbb R^n\) be a full-rank lattice and \(A\) an invertible real matrix. Give \(X\in L\) the weights \(\exp(-\|A^{-1}(X-c)\|^2/2)\), and let \(Y=A^{-1}(X-c)\), \(z=A^{-1}c\). The matching continuous Gaussian would have \(Y\sim N(0,I)\). Put
\[
 \Gamma=2\pi A^T L^*,\qquad
 F(z)=\sum_{b\in\Gamma}e^{-\|b\|^2/2}e^{i\langle b,z\rangle},
 \qquad m=\sum_{b\ne0}e^{-\|b\|^2/2}.
\]
Here \(L^*\) is the Euclidean dual. For \(A=sI/\sqrt{2\pi}\), \(m\le\epsilon\) is precisely \(s\ge\eta_\epsilon(L)\) in the usual \(\exp(-\pi\|x\|^2/s^2)\) convention. Poisson summation and completion of the square give the identity
\[
 \log\mathbb E e^{\langle t,Y\rangle}
   =\frac{\|t\|^2}{2}+\log F(z+t)-\log F(z)\qquad(t\in\mathbb R^n). \tag{1}
\]
The sign of the Fourier phase is immaterial since \(\Gamma=-\Gamma\). All Fourier series below converge normally on compact subsets of the complexified space.

Throughout, \(0<\epsilon<1\) is an upper budget for \(m\), and
\[
 \ell=\log(2/\epsilon),\quad R=\sqrt{2\ell},\quad
 H=\operatorname{arcosh}(2/\epsilon^2+1/\epsilon),\quad R_+=H/R.
\]
As \(\epsilon\downarrow0\), \(H=R^2+\log(1+\epsilon/2)+O(\epsilon^4)\). Thus \(R_+=R+O(\epsilon/R)\). The order-\(k\) cumulant discrepancy in (1) is the symmetric tensor \(D^k\log F(z)\): at orders 1 and 2 it is the bias and the covariance minus \(I\), and at higher orders it is the cumulant itself. Use the real multilinear operator norm, equivalently the supremum along a repeated unit direction by [Banach's theorem](https://arxiv.org/abs/1808.03864).

1. **Sharp fixed and growing-order scale.** For every fixed \(\tau>0\), uniformly over integers \(1\le k\le(1/\log 2-\tau)\ell\) (when this range is nonempty),
   \[
      \sup_{\Gamma,z:\,m\le\epsilon}\|D^k\log F(z)\|
        =(1+o(1))\,\epsilon [2\log(2/\epsilon)]^{k/2}. \tag{2}
   \]
   The supremum is over all full-rank lattices of arbitrary finite dimension and all real shifts. In particular, the bias and covariance errors at smoothing are sharp to leading order and independent of dimension.
2. **First higher-order transition.** For integers \(k=\log_2(1/\epsilon)+O(1)\), put \(d=\epsilon\,2^{k-2}\). Uniformly for bounded offsets,
   \[
      \sup_{\Gamma,z:\,m\le\epsilon}
      \frac{\|D^k\log F(z)\|}{\epsilon R^k}
       =
       \begin{cases}
          1+d+o(1), & k\text{ even},\\[2mm]
          \displaystyle\max_{0\le a\le1}\sqrt{1-a^2}(1+2da)+o(1),
                    & k\text{ odd}.
       \end{cases} \tag{3}
   \]
   The odd maximum is reached at \(a=(\sqrt{1+32d^2}-1)/(8d)\) for \(d>0\), and at \(a=0\) for \(d=0\). Rank one attains both asymptotics, with an appropriate shift.
3. **Real displacement and complex zero distance.** Let \(f(r)=2\sin(\min\{r,\pi\}/2)\) for \(r\ge0\). For real \(t\), \(|\log F(z+t)-\log F(z)|\le\epsilon f(R_+\|t\|)/(1-\epsilon)\). In particular the sharp supremum of the error term in (1) on \(\|t\|\le r/R\) is \(\epsilon(f(r)+o(1))\), uniformly for \(r\) in compact sets. For small \(\epsilon\), every \(F\) is zero-free when \(\|\operatorname{Im}z\|<\operatorname{arcosh}(1/\epsilon)/R_+\). The infimum, over this lattice class, of the imaginary distance to a complex zero is \(R/2+O(\epsilon/R)\).

## 2. One projected probability measure

Completing the square for the Gaussian on \(\Gamma\), and then using maximal Gaussian mass at an unshifted lattice, yields for every unit \(u\) and real \(t\),
\[
 \sum_{b\in\Gamma}e^{-\|b\|^2/2}e^{t\langle b,u\rangle}
 =e^{t^2/2}\sum_{b\in\Gamma}e^{-\|b-tu\|^2/2}
 \le (1+m)e^{t^2/2}.
\]
The shift inequality follows immediately from Poisson summation and positivity of the unshifted Fourier coefficients. Define a probability law of \(V\ge0\) by taking the measure of \(|\langle b,u\rangle|\) for \(b\ne0\) with weights \(e^{-\|b\|^2/2}/\epsilon\) and adding the missing mass \(1-m/\epsilon\) at zero. Pairing \(b,-b\) in the preceding estimate at \(t=R\) gives
\[
 \mathbb E\cosh(RV)
 \le \frac{(1+m)e^{R^2/2}-1+\epsilon-m}{\epsilon}
 \le \frac{2}{\epsilon^2}+\frac1\epsilon=\cosh H. \tag{4}
\]
In particular, with \(U=V/R\) we have
\[
 \mathbb E e^{R^2(U-1)}\le 1+\epsilon/2. \tag{5}
\]
This uses \(e^x\le2\cosh x\) for \(x\ge0\).

For any fixed \(c_0<2\) and all integers \(1\le p\le c_0\ell\), (4) implies \(\mathbb E V^p\le R_+^p\) for sufficiently small \(\epsilon\). To see this, use the tangent to \(G(x)=\cosh(R x^{1/p})\) at \(x=R_+^p\). On \(R x^{1/p}\ge p\) the second derivative has the sign of \(v\cosh v-(p-1)\sinh v\), where \(v=R x^{1/p}\), hence is nonnegative. The tangent at \(R_+^p\), evaluated at \(x=(p/R)^p\), is nonpositive because
\[
 \frac{H}{p}\tanh H\bigl(1-(p/H)^p\bigr)\ \ge 1 .
\]
For large \(p\) this follows uniformly from \(H/p\ge1+\eta\) for some \(\eta>0\), and for the finitely many smaller \(p\) it follows from \(H\to\infty\). The tangent has positive slope, so it is below \(G\) also on the remaining interval. Averaging this global supporting line and using (4) proves the moment inequality. In particular, if \(h=F-1\),
\[
 \|D^p h\|\le\epsilon R_+^p \qquad(1\le p\le c_0\ell). \tag{6}
\]
Along a repeated unit direction this follows by summing the absolute Fourier terms; Hölder gives the same upper bound in independent unit directions. For \(p=0\) use \(|h|\le\epsilon\).

At real \(z\), the bias norm is at most \(\epsilon R_+/(1-\epsilon)\). The covariance is at most \(I+\epsilon R_+^2 I/(1-\epsilon)\) by differentiating \(\log F\). For its lower bound, the centered covariance minimizes the covariance in positive semidefinite order by [Regev–Stephens-Davidowitz, Corollary 3.2](https://arxiv.org/abs/1502.04796), and \(D^2\log F(0)=D^2F(0)/(1+m)\). This gives \(\operatorname{Cov}(Y)\succeq(1-\epsilon R_+^2)I\) at all shifts. The second moment about the specified center, rather than about the actual mean, is \(I+D^2F(z)/F(z)\) by (1), so has operator error at most \(\epsilon R_+^2/(1-\epsilon)\).

## 3. Cumulants and the transition

For all orders in (6), the product rule gives \(\|D^k(h^j)\|\le\epsilon^j(jR_+)^k\). The derivative series of \(\log(1+h)\) converges uniformly at every fixed real derivative order: \(\sum_{j\ge1}\epsilon^j j^{k-1}\) is finite. In the range (2), each \(j\ge2\) term after division by \(\epsilon R_+^k\) is bounded by \(\epsilon^{j-1}j^{k-1}\); since \(j\le2^{j-1}\), the sum tends to zero uniformly. Also \((R_+/R)^k=1+O(\epsilon)\) for \(k=O(\ell)\).

In the range (3), the terms \(j\ge3\) still have normalized sum \(o(1)\), using \(\log j/(j-1)\le(\log 3)/2\) for \(j\ge3\) and \(k(\log 3)/2< (1-\eta')\ell\) for some fixed \(\eta'>0\). Thus only \(h-h^2/2\) matters. To preserve the relation between its two terms, take one representative of each pair \(b,-b\) with \(\langle b,u\rangle\ge0\), and retain its phase \(\theta=\langle b,z\rangle\) in the law of \((U,\theta)\) discussed above. When the projection is zero, either representative is valid. For the artificial mass at zero use phase \(\pi/2\). Then \(h(z+tu)=\epsilon\,\mathbb E\cos(\theta+R U t)\). Let \(T=U^{k/2}\). From (6)'s moment proof, \(\mathbb E T^2\le (R_+/R)^k=1+o(1)\).

Here is the required uniform pair estimate. Take \(\delta=\ell^{-2/3}\) and independent copies \(U,U'\). In the window (3), for \(j=k\) or \(j=k/2\), the contribution of \(U\notin[1-\delta,1+\delta]\) to \(\mathbb E e^{j(U-1)}\) is at most
\(e^{-j\delta}+(1+\epsilon/2)e^{-(R^2-j)\delta}=o(1)\), by (5).
The full exponential moment is bounded by Jensen applied to (5). Because \(((U+U')/2)^k\le \exp((k/2)(U-1)+(k/2)(U'-1))\), its contribution outside this two-copy event is \(o(1)\); the same holds for \(U^{k/2}{U'}^{k/2}\) and \(|(U-U')/2|^k\). Inside the event, the last expression is at most \(\delta^k\), and
\[
 \frac{((U+U')/2)^k}{U^{k/2}{U'}^{k/2}}
   =\left(1+\frac{(U-U')^2}{4UU'}\right)^{k/2}=1+o(1)
\]
uniformly, since \(k\delta^2=o(1)\). Applying these estimates to the sum and difference terms in the product of cosines gives the repeated-direction discrepancy, divided by \(\epsilon R^k\):
\[
 \operatorname{Re}\!\left[
   i^k\left(\mathbb E[T^2 e^{i\theta}]
            -d\,(\mathbb E[T e^{i\theta}])^2\right)\right]+o(1). \tag{7}
\]
For even \(k\) its absolute value is at most \(1+d+o(1)\) by \(\mathbb E T^2\le1+o(1)\). For odd \(k\) put \(A_0=\mathbb E(T^2\cos^2\theta)\), \(B_0=\mathbb E(T^2\sin^2\theta)\). Cauchy–Schwarz bounds the two contributions by \(\sqrt{B_0(A_0+B_0)}+2d\sqrt{A_0 B_0}\), with \(A_0+B_0\le1+o(1)\). Dividing through by \(A_0+B_0\) when it is nonzero, and optimizing \(A_0/(A_0+B_0)=a^2\), proves the upper bound in (3). The scalar critical point of \(\sqrt{1-a^2}(1+2da)\) solves \(4da^2+a-2d=0\).

For sharpness let \(\Gamma=g\mathbb Z\) with \(2\sum_{j\ge1}e^{-g^2j^2/2}=\epsilon\). Then \(e^{-g^2/2}=(\epsilon/2)(1+O(\epsilon^3))\) and \(g/R=1+O(\epsilon^3/\ell)\). For \(k=O(\ell)\) in (2) or (3), higher lattice multiples make a vanishing relative contribution to \(\mathbb E T^2\) and to the first harmonic derivative: their relative weights are bounded by a constant times \(\sum_{j\ge2} e^{-(j^2-1)\ell}j^k=o(1)\), since \(j^2-1\ge3(j-1)\) and \(j\le2^{j-1}\). Thus the rank-one law in (7) has effectively \(T=1\) and a single freely adjustable phase. Take \(\theta=\pi\) for even \(k\), and \(\cos\theta=-a\), \(\sin\theta=\sqrt{1-a^2}\) for odd \(k\). Both upper bounds are attained to leading order. With only the linear term in the range (2), choose the phase to maximize the absolute \(k\)-th derivative of a single cosine. At orders 1 and 2 this also identifies the leading constants for the bias and the two covariance errors: quarter-period for bias, zero and half-period for covariance.

## 4. Real displacement and complex tube

The function \(f(r)=2\sin(\min\{r,\pi\}/2)\) is concave and nondecreasing for \(r\ge0\). For \(t\ne0\), take \(u=t/\|t\|\) in (4); the paired cosines give
\[
 |F(z+t)-F(z)|\le\epsilon\,\mathbb E f(\|t\|V)
           \le\epsilon f(\|t\|R_+).
\]
Use the mean-value theorem for \(\log\) and \(F\ge1-\epsilon\) on real arguments. In rank one with the \(g\) above, the first cosine attains its maximal difference for phase displacement up to \(\min\{\pi,gr/R\}\), and the higher harmonics are \(O(\epsilon^4)\) in total. This proves the sharp real displacement profile, including its saturation at \(r=\pi\).

For real \(w\) with \(s=\|w\|\le R\), the modulus of the symmetric Fourier pair at \(z+iw\) is bounded by its weight times \(2\cosh(sV)\). The function \(x\mapsto \cosh(q\operatorname{arcosh}x)\) is nondecreasing and concave on \(x\ge1\) for \(0\le q\le1\). Indeed the derivative at \(x=\cosh v\) is \(q\sinh(qv)/\sinh v\), which is decreasing since \(v\coth v\) is increasing; handle \(q=0\) by continuity. Taking \(q=s/R\) and applying (4) gives
\[
 |F(z+iw)-1|\le\epsilon\,\mathbb E\cosh(sV)
                  \le \epsilon\cosh(sR_+).
\]
This proves the zero-free tube stated above, whose radius is less than \(R\) for small \(\epsilon\). Rank one has an exact zero at \(\pi/g+i g/2\): terms with indices \(j\) and \(-j-1\) cancel there. The lower tube radius is \(R/2+O(\epsilon/R)\), and \(g/2=R/2+O(\epsilon^3/R)\). These bounds place the closest possible imaginary zero at the stated precision; no claim of exact extremality at finite \(\epsilon\) is needed.

## 5. Width inflation, scope, and primary comparison

For fixed \(\alpha\ge1\), replacing \(A\) by \(\alpha A\) transforms each spectral weight into its \(\alpha^2\)-th power. Pairing and the elementary \(\ell^p\) inequality give \(m_\alpha\le2(\epsilon/2)^{\alpha^2}\). This upper bound is attained to leading order by the rank-one family. At the enlarged width, and with the newly standardized law, the sharp fixed-order discrepancy in the original budget \(\epsilon\) is consequently
\[
 (1+o(1))\,2^{1-\alpha^2}\epsilon^{\alpha^2}
        [2\alpha^2\log(2/\epsilon)]^{k/2}.
\]
No width inflation is needed for (2). For a uniform *trace* bound instead of an operator bound, dimension dependence cannot be removed: take \(\Gamma=g_n\mathbb Z^n\) with total mass budget \(m=\epsilon>0\) fixed and exact. Each factor has mass \((1+\epsilon)^{1/n}-1\sim \log(1+\epsilon)/n\), and \(g_n^2\sim2\log n\). The centered trace deficit is therefore asymptotic to \(2\log(1+\epsilon)\log n\), while the operator deficit vanishes.

[Micciancio–Regev, Lemmas 4.2–4.3](https://cseweb.ucsd.edu/~daniele/papers/Gaussian.pdf) bound the first two moments using Fourier derivatives and a premise \(s\ge2\eta_\epsilon(L)\). [Regev–Stephens-Davidowitz, §3](https://arxiv.org/abs/1502.04796) gives shape, covariance order and fourth-moment inequalities for periodic Gaussians. [Zhao and Qian (2024)](https://doi.org/10.1155/2024/7777881) give identities for second and fourth moments and dual moments. The contribution here is not the Fourier derivative identities or covariance ordering: it is a dimension-free, asymptotically attained quantitative profile at a prescribed smoothing budget, including a growing-order transition. [Genise–Micciancio–Peikert–Walter](https://cseweb.ucsd.edu/~daniele/papers/PKC2020.pdf) use general covariance matrices, smoothing and linear/convolution estimates; those results have a different aim. The rank-one zero is classical theta-function geometry. The present uniform lower bound on the zero-free tube comes from (4).

The adjacent checks evaluate only fixed synthetic Gaussian sums, exact trigonometric identities, and scalar witnesses. They report 14,841 exact checks and 22,345 numerical checks; the dimension-uniform conclusions follow from the proof. Earlier repository work on fixed-dimensional shape optimization, dyadic transition of the dual mass itself, deterministic rounding, and convolution factorization does not give a width-fixed derivative envelope across arbitrary shifted lattices. The general sharpness examples are rank one; they do not show that the same extremum is attained within a more restricted ideal-lattice family.
