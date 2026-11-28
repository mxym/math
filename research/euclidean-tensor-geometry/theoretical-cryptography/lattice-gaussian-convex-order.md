# Sharp Gaussian variance inflation for convex order on a lattice

A centered lattice Gaussian has the same familiar exponential-moment upper bound as the continuous Gaussian of its *nominal* variance, but that does not imply domination for all convex losses. Even on the integer line, the latter requires a strictly larger continuous variance at every finite width. We determine the sharp large-width inflation, through its second term, uniformly over the position of the lattice relative to the center. Orthogonal products give an exact coordinate criterion, and the scalar lower bound transfers to any fixed lattice in primitive dual directions.

This is a comparison of standalone Gaussian probability measures. It neither constructs a discrete sampler nor prescribes parameters for a scheme. The [variance-matched moment comparison](lattice-gaussian-variance-matched-moment-crossings.md) treats fixed even polynomial moments at the **actual discrete variance**, not the minimal inflation past the nominal Gaussian parameter for all convex losses. The \(1/12\) in the present theorem is a stop-loss quadrature extremum, not a claim that rounding a continuous Gaussian produces the discrete Gaussian.

## 1. Main theorem

On \(a+\mathbb Z\), let \(X_{v,a}\) have mass proportional to \(e^{-x^2/(2v)}\), with nominal variance \(v>0\) and nominal center zero; write \(m=m_{v,a}=\mathbb E X_{v,a}\). For probability laws on \(\mathbb R\) of the same finite mean, set \(X\preceq_{\rm cx}Y\) if every convex function has no larger expectation under \(X\), whenever the expectations are defined. Equivalently, all call losses \(\mathbb E(X-t)_+\) are at most their counterparts under \(Y\), for every real \(t\). This equivalence follows by representing a convex function, up to an affine term, as a nonnegative integral of right and left calls using its distributional second derivative. Alternatively this is the usual convex order in [Strassen's Theorem 8](https://doi.org/10.1214/aoms/1177700153).

Define the optimal variance inflation
\[
 \Delta(v,a)=\inf\{w-v:\ w>0,\ X_{v,a}\preceq_{\rm cx}N(m,w)\}.
\]
The infimum is attained and \(\Delta(v,a)>0\) for all \(v>0,a\in\mathbb R\). Uniformly over \(a\) as \(v\to\infty\), it satisfies
\[
              \Delta(v,a)=\frac1{12}+\frac{13}{1440\,v}+O(v^{-2}).
 \tag{1}
\]
In particular allowing any phase or recentering the continuous target at the actual mean does not remove the correction. By the same equal-mean convex-order criterion, the least variance of a Gaussian final marginal in an abstract martingale coupling with this discrete initial marginal is \(v+\Delta(v,a)\). No coupling efficiency is claimed.

For comparison, when \(a=0\) the standard nominal subgaussian bound is exact at the level of the proxy: completing the square gives
\[
 \mathbb E e^{t X_{v,0}}
 =e^{vt^2/2}\frac{\sum_{j\in\mathbb Z}e^{-(j-vt)^2/(2v)}}
                       {\sum_{j\in\mathbb Z}e^{-j^2/(2v)}}
 \le e^{vt^2/2}
\]
by the positive Poisson coefficients of the periodized Gaussian. Thus this exponential-moment comparison alone cannot imply the corresponding convex order.

## 2. Exact call sums and the noncentral regimes

Write \(g_v(x)=(2\pi v)^{-1/2}e^{-x^2/(2v)}\) and \(Z_{v,a}=\sum_{x\in a+\mathbb Z}g_v(x)\). Poisson summation and its differentiated version give
\[
 Z_{v,a}=1+O(e^{-2\pi^2v}),\qquad
 |m_{v,a}|=O(v e^{-2\pi^2v})\qquad(v\to\infty)
 \tag{2}
\]
uniformly in \(a\): the derivative in \(a\) of \(Z_{v,a}\) is \(-m_{v,a}Z_{v,a}/v\). Let \(C_v(t)\) denote the call for \(N(0,v)\). Because the two means agree, their call difference at \(t<0\) equals the difference of their left-call values, which are right calls at threshold \(-t\) for the reflected variables. Reflection replaces \(a,m\) by \(-a,-m\). Thus the upper comparison need only handle \(t\ge0\), uniformly in \(a\).

For \(t\ge0\), put \(b=t/v\), and let \(\delta\in[0,1)\) be the distance from \(t\) to the first point of \(a+\mathbb Z\) at or above \(t\). The term at zero distance, if present, is zero. The exact discrete call divided by \(g_v(t)\) is
\[
 Z_{v,a}^{-1}\sum_{j\ge0}(j+\delta)
           e^{-b(j+\delta)-(j+\delta)^2/(2v)} .                       \tag{3}
\]
For the same-mean Gaussian \(N(m,v+\Delta)\) the call is \(C_{v+\Delta}(t-m)\).

For any **fixed** \(v>0\), domination at \(w=v\) fails, choosing reflection if needed so that \(m\le0\). For large \(x\in a+\mathbb Z\) take \(t=x-v/x\) and use the contribution of that single point in (3). It is at least \(c_v g_v(t)/b\) for all large \(x\), with a positive constant (depending on the fixed lattice phase if needed), while \(C_v(t-m)\le C_v(t)\le g_v(t)/b^2\) by integrating \(u e^{-bu}\). Thus some fixed finite threshold gives a strict failure. Gaussian call expectations are continuous and nondecreasing in their variance, so the minimum, if finite, exceeds \(v\). Finiteness follows by first taking any \(w_0>v\): its Gaussian dominates both tails for all sufficiently large nonnegative thresholds and both reflections, because at large \(t\) the discrete call is \(O_v(g_v(t)/b)\) by (3) and a continuous integral over \([0,w_0/(t-m)]\) bounds the continuous call below by a multiple of \(g_{w_0}(t-m)(w_0/(t-m))^2\). The Gaussian density ratio wins quadratically in \(t\). Increasing \(w\ge w_0\) then covers all thresholds in the remaining compact interval, since the normal call tends uniformly to infinity there. The feasible set is closed in this positive-variance interval, proving attainment.

We will compare variances \(v+\Delta\) with \(\Delta=1/12+O(1/v)\). Two threshold regimes have a strict margin:

**Regime \(b\) in a fixed compact subinterval of \((0,\infty)\).** In (3) the relative expression converges uniformly (with varying \(\delta\)) to
\[
 \sum_{j\ge0}(\delta+j)e^{-b(\delta+j)}
  =e^{-b\delta}\left(\frac{\delta}{1-e^{-b}}
                  +\frac{e^{-b}}{(1-e^{-b})^2}\right).
\]
The continuous call divided by \(g_v(t)\) converges uniformly to \(e^{b^2/24}/b^2\). Indeed factor out \(g_{v+\Delta}(t-m)\) from the continuous integral, apply dominated convergence to its exponential linear rate, and use (2) and the Gaussian density ratio at \(t-m\). The maximum over \(\delta\in[0,1]\) of \(b^2\) times the displayed geometric sum is attained at \(\delta=1/b-1/(e^b-1)\). This point is interior: the two endpoint values coincide and the derivative has a unique zero. With \(x=b/2\) the logarithm of the maximum is
\[
 \log\frac{x}{\sinh x}-1+x\coth x
  =\sum_{\ell\ge1}
    \left[-\log(1+u_\ell)+\frac{2u_\ell}{1+u_\ell}\right],
 \qquad u_\ell=\frac{x^2}{\pi^2\ell^2}.
 \tag{4}
\]
This is Euler's product for \(\sinh x/x\) and its logarithmic derivative. For \(u>0\) the bracket is strictly less than \(u\), as differentiating the difference from \(u\) gives \(-u(3+u)/(1+u)^2<0\) and the difference vanishes at zero. Summing gives a strict upper bound \(x^2/6=b^2/24\). By compactness the margin is uniform on the stipulated \(b\) range.

**Regime \(b\) sufficiently large.** For \(b\ge1\) the right side of (3) is at most \(K/b\) with an absolute \(K\) for all sufficiently large \(v\); use \(\delta e^{-b\delta}\le 1/(eb)\) and a geometric sum for \(j\ge1\). For \(v\) large and \(b\ge1\) the continuous call is at least \(c\,g_{v+\Delta}(t-m)/b^2\) by integration up to \((v+\Delta)/(t-m)\). Its density relative to \(g_v(t)\) has logarithm
\[
 -\tfrac12\log(1+\Delta/v)
   +\frac{\Delta v b^2}{2(v+\Delta)}
   +\frac{mvb}{v+\Delta}-\frac{m^2}{2(v+\Delta)} .
\]
For \(\Delta=1/12+O(1/v)\), this is at least \(c' b^2-C'\) for \(v\) large, uniformly in the phase, as the mean term is negligible compared with the quadratic term. Thus the discrete-to-continuous call ratio is \(O(b e^{-c' b^2})\), uniformly at the extreme thresholds, so no such threshold is an obstruction.

## 3. Central regime and the second-order extremum

We give estimates uniform for \(0\le b\le b_0\) with small fixed \(b_0>0\). Put \(A=b+v^{-1/2}\) and \(x=\delta-1/2\in[-1/2,1/2]\). In the unnormalized discrete call apply shifted Euler–Maclaurin to
\[
 F(u)=u g_v(t+u),\qquad u\ge0.
\]
The expansion is \(\sum_{j\ge0}F(j+\delta)-\int_0^\infty F(u)du
 =-\sum_{n=1}^5 B_n(\delta)F^{(n-1)}(0)/n!+R\), with
\[
 |R|\le C\left(|F^{(5)}(0)|+\int_0^\infty |F^{(6)}(u)|\,du\right).
\]
Here \(B_n\) are the Bernoulli polynomials. This version follows directly by using the jump derivative of \(B_1(\{\delta-u\})\) and integrating by parts through the bounded periodic sixth Bernoulli polynomial; it extends to the endpoint because \(F(0)=0\). For that usual Euler–Maclaurin remainder method see [NIST DLMF §2.10(i)](https://dlmf.nist.gov/2.10.i).

The relevant derivatives satisfy \(F'(0)=g_v(t)\), \(F''(0)=-2b g_v(t)\), \(F'''(0)=3(b^2-1/v)g_v(t)\), and \(F^{(4)}(0)=O(A^3 g_v(t))\). Also \(R=O(A^4 g_v(t))\). To see the uniform integrated bound, set \(u=y/A\). For Gaussian derivatives of order \(j\), the polynomial prefactor is at most \(C_j A^j(1+y)^j\) since \(b+u/v\le A(1+y)\) and \(v^{-1/2}\le A\). The Gaussian ratio is either at most \(e^{-y/2}\) or at most \(e^{-y^2/8}\), because \(b/A+(v^{-1/2}/A)=1\). Since \(F^{(6)}=6 g_v^{(5)}(t+u)+u g_v^{(6)}(t+u)\), its integral is \(O(A^4 g_v(t))\). The normalization in (2) adds only \(O(v e^{-2\pi^2 v}g_v(t))\): the sum in (3) before division by \(Z_{v,a}\) is \(O(v)\), uniformly for \(b\ge0\).

Use the explicit values
\[
 B_2(\delta)=x^2-\tfrac1{12},\quad
 B_3(\delta)=x^3-\tfrac{x}{4},\quad
 B_4(\delta)=\tfrac7{240}+O(x^2),\quad B_5(\delta)=O(|x|).
\]
Writing \(D(t)=\mathbb E(X_{v,a}-t)_+\), the resulting central expansion is
\[
 \frac{D(t)-C_v(t)}{g_v(t)}
  =\frac1{24}-\frac{x^2}{2}
    +\frac b3(x^3-x/4)-\frac7{1920}(b^2-v^{-1})
    +O\!\left((b^2+v^{-1})x^2+|x|A^3+A^4\right).
 \tag{5}
\]
The normal call obeys the heat identity \(\partial_v C_v(t)=g_v(t)/2\) (differentiate its integral or its explicit formula). Taylor expanding over a bounded positive \(\Delta\) gives, uniformly in this regime,
\[
 \frac{C_{v+\Delta}(t-m)-C_v(t)}{g_v(t)}
   =\frac\Delta2+\frac{\Delta^2}{8}(b^2-v^{-1})+O((b^2+v^{-1})^2).
 \tag{6}
\]
The shift by \(m\) changes the call by at most \(|m|\) times the largest tail probability at a threshold between \(t\) and \(t-m\). That probability is \(O(\sqrt v\, g_v(t))\) here by integrating the Gaussian ratio and using (2). Thus recentering is exponentially negligible relative to \(g_v(t)\). The remainder in the variance expansion follows from differentiating the Gaussian density twice in its variance over this bounded interval.

For all \(\Delta=1/12+O(1/v)\), the coefficient of \(b^2-v^{-1}\) in (5) minus (6) is \(-13/2880+O(1/v)\). Use \(|b x^3/3|\le b x^2/6\) and maximize the remaining expression in \(x\). The maximum of \(-[1/2-O(b+v^{-1})]x^2-(b/12)x+O(|x|A^3)\) is at most
\[
 \frac{b^2}{288}+O(b^3+b^2/v+v^{-2}),
\]
by bounding the linear coefficient by \(b/12+O(A^3)\) and completing the square. Also \(A^4\le C(b^4+v^{-2})\). Consequently
\[
 \frac{D(t)-C_{v+\Delta}(t-m)}{g_v(t)}
 \le \frac1{24}-\frac{\Delta}{2}+\frac{13}{2880 v}
      -\frac{b^2}{960}+O(b^3+b^2/v+v^{-2}).                           \tag{7}
\]
The negative \(b^2\) coefficient is essential to controlling thresholds growing with \(v\). First take \(b_0\) small enough and then \(v\) large enough to absorb the \(O(b^3+b^2/v)\) into it. Choosing
\(\Delta=1/12+13/(1440v)+K/v^2\) for sufficiently large fixed \(K\) makes (7) nonpositive uniformly. The two strict margins in §2 handle every \(b\ge b_0\), and reflection handles negative thresholds.

For the opposite inequality choose \(t\ge0\) a half-integer step before a lattice point and bounded by one, so that \(\delta=1/2\), \(x=0\), and \(b=O(1/v)\). Equations (5)–(6) now give \(1/24-\Delta/2+13/(2880v)+O(v^{-2})\) *as an equality*. Thus \(\Delta=1/12+13/(1440v)-K/v^2\) for sufficiently large fixed \(K\) gives a positive call difference for every phase. This proves (1).

## 4. Orthogonal products and a necessary bound on any fixed lattice

Scaling a step \(\ell>0\) to one gives, for a one-dimensional lattice of step \(\ell\) and arbitrary phase, threshold
\[
 \frac{\ell^2}{12}+\frac{13\,\ell^4}{1440v}+O(\ell^6/v^2)
\]
for the increase of the nominal variance \(v\), uniformly in the phase. On a rectangular lattice, the nominal spherical Gaussian restriction is a product of the scalar laws. A continuous Gaussian with diagonal covariance in this orthonormal lattice coordinate system dominates in multivariate convex order if and only if each coordinate satisfies its scalar threshold. Necessity uses coordinate convex tests; sufficiency uses independent one-dimensional martingale couplings (or successively applies the scalar inequality to slices of a convex function). This gives in particular the exact isotropic threshold on an orthogonal product as the maximum scalar threshold, without needing dimension growth assumptions on that equivalence.

More generally let \(\Lambda\) be any fixed full lattice in \(\mathbb R^d\), and restrict \(e^{-\|x\|^2/(2v)}\) to a translate of \(\Lambda\). For its true mean \(m\), any isotropic dominating Gaussian \(N(m,(v+\Delta)I)\) must satisfy, for large \(v\),
\[
 \Delta\ \ge\
 \frac{1}{12\lambda_1(\Lambda^*)^2}
 +\frac{13}{1440 v\,\lambda_1(\Lambda^*)^4}
 -O_\Lambda(v^{-2}) .                                                \tag{8}
\]
For the proof project in the unit direction of a shortest nonzero dual vector \(k\), which is primitive. The projected lattice has step \(\ell=1/\|k\|\). Every fiber is an orthogonal coset of \(\Lambda\cap k^\perp\); Poisson summation makes its Gaussian mass equal to the common continuous volume factor times \(1+O_\Lambda(e^{-c v})\), uniformly over the coset. Thus the projected law is multiplicatively \(1+O_\Lambda(e^{-c v})\) close to the scalar lattice Gaussian on that grid; their first moments differ by \(O_\Lambda(\sqrt v e^{-c v})\), since the scalar first absolute moment is \(O_\Lambda(\sqrt v)\). At the bounded half-cell threshold used for the scalar lower bound, perturbing probability law and matching true mean changes the stop loss by at most \(O_\Lambda(\sqrt v e^{-c v})\). This is negligible relative to the signed gap of order \(v^{-2}g_v(t)\). Hence the scaled scalar lower bound applies. No general skew-lattice upper bound matching (8) is asserted.

## Reproduction

Run \(\texttt{python3 verify-lattice-gaussian-convex-order.py}\) (uses mpmath). It checks the rational coefficients in (5)–(7), the geometric-sum maximization, and the high-precision half-cell inflation at several synthetic phases and variances. It is a check of the formulas, not the proof of the uniform all-threshold claim.
