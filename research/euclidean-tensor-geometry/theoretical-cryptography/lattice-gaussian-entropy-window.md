# Sharp Rényi-entropy errors at the lattice smoothing width

**Scope.** The random variable here is the discrete Gaussian on a single
lattice coset. We compare its entropy to the differential entropy of the
matching continuous Gaussian minus log covolume. This is a positive
statistical calibration for an abstract sampler, not a statement about a
cryptosystem or the hardness of a learning problem. It is not a comparison
of wrapped Gaussian divergence to uniform, and does not settle whether the
zero coset minimizes all Rényi orders at every width.

## 1. Statements

Let \(\Lambda\subset\mathbb R^n\) be full rank and \(v=\det\Lambda\).
Let \(D_{\Lambda+z,s}\) have mass proportional to
\(\exp(-\pi\|x\|^2/s^2)\) for \(x\in\Lambda+z\). Its width is \(s\), not
the standard deviation of the continuous comparison \(G_s\), whose
density is \(s^{-n}\exp(-\pi\|x\|^2/s^2)\). Logs and entropies below
are natural. Define the entropy deficit
\[
 B_\alpha(\Lambda,z,s)=h_\alpha(G_s)-\log v
                              -H_\alpha(D_{\Lambda+z,s}),
\]
where \(\alpha=1\) means Shannon entropy. The ordinary smoothing
condition \(s\ge\eta_\epsilon(\Lambda)\) means
\(\sum_{0\ne\xi\in\Lambda^*} e^{-\pi s^2\|\xi\|^2}\le\epsilon\).
Write \(M^+_{n,\epsilon}(\alpha)\) and \(M^{\rm abs}_{n,\epsilon}(\alpha)\)
for the suprema of \(B_\alpha\) and \(|B_\alpha|\), respectively, over all
these \(s,\Lambda,z\). Let \(b=\log(1/\epsilon)\).

* **Dimension-dominated window:** If \(n\to\infty\), \(b=o(n)\), and
  \(0<\epsilon\le\epsilon_0<1\), then for \(\alpha=1+u/n\), uniformly
  for \(u\) in any fixed compact interval,
  \[
    M^+_{n,\epsilon}(1+u/n)
     =n\,\frac{\log(1+\epsilon e^{u/2})-\log(1+\epsilon)}{u}
             +o(n\epsilon).
    \tag{1}
  \]
  At \(u=0\) the quotient is \(\epsilon/(2(1+\epsilon))\).
  If also \(\epsilon\to0\), the absolute supremum has the same
  leading term as the positive one:
  \[
    M^{\rm abs}_{n,\epsilon}(1+u/n)
       = n\epsilon \frac{e^{u/2}-1}{u} + o(n\epsilon),
    \tag{2}
  \]
  with the value \(1/2\) for the function of \(u\) at zero. In particular
  the worst Shannon error is asymptotic to \(n\epsilon/2\) in this
  vanishing-budget regime.
* **Budget-dominated window:** If \(b\to\infty\) and \(n=o(b)\)
  (including fixed \(n\)), then both the positive and absolute suprema,
  for \(\alpha=1+u/b\), are
  \[
      b\epsilon\,\frac{e^u-1}{u}+o(b\epsilon),
    \tag{3}
  \]
  uniformly on compact \(u\)-intervals, with value 1 at zero.

The lower bounds already hold with \(z=0\). The question of the sharp
constant when \(b\) and \(n\) have comparable order is not addressed.

**Comparison with prior work.**
[Ling–Luzzi–Belfiore–Stehlé, Lemma 7](https://arxiv.org/pdf/1210.6673)
and [Ling–Belfiore, Lemma 6](https://arxiv.org/pdf/1302.5906) estimate
the Shannon-to-continuous difference from flatness at a slightly
*narrower* width. The results here give the optimal error profiles
from the flatness budget at the **same** original width, for Shannon
and for adjacent Rényi orders. The
[Ling–Luzzi–Yan Rényi smoothing parameter, Definition 1](https://opencryptology.org/2025/986)
instead controls Rényi divergence of a periodized continuous Gaussian
from Haar on the torus. That is a different random variable and
a different entropy comparison.

## 2. Reduction to radial moments of the dual

Set \(T_\xi=\pi s^2\|\xi\|^2\), and write
\[
   \Theta_\alpha(z)=\sum_{\xi\in\Lambda^*}e^{-T_\xi/\alpha}
                     \cos(2\pi\langle\xi,z\rangle),\qquad
   R=\Theta_1(0)-1.
\]
These \(\Theta_\alpha(z)\) are positive by Poisson summation.
The smoothing condition is \(R\le\epsilon\). The partition sum
on \(\Lambda+z\) at width \(s/\sqrt\alpha\) is
\((s/\sqrt\alpha)^n\Theta_\alpha(z)/v\), by Poisson.
Subtracting the two entropy formulas gives the exact deficit
\[
 B_\alpha
  =\frac{\log\Theta_\alpha(z)-\log\Theta_1(z)}{\alpha-1}
    -\log\Theta_1(z).
 \tag{4}
\]
This includes \(\alpha=1\) by differentiation; in particular at \(z=0\)
the quotient at \(\alpha=1\) is
\(\big(\sum_{\xi\ne0}T_\xi e^{-T_\xi}\big)/(1+R)\).
The continuous baseline is
\(h_\alpha(G_s)=n\log s+(n/2)\log\alpha/(\alpha-1)\).
All the derivatives at a positive width can be taken termwise by
locally normal Gaussian convergence.

Let \(q\) be any budget with \(R\le q<1\). Define a probability
law \(\nu_q\) on \(T\ge0\) by putting mass \(e^{-T_\xi}/q\) at
\(T_\xi\) for \(\xi\ne0\), and padding with mass \(1-R/q\) at zero.
For \(0<t<1\), Poisson and the plain termwise monotonicity of
the *primal* unshifted mass as width increases imply
\[
 \frac{\sum_\xi e^{-(1-t)T_\xi}}{\sum_\xi e^{-T_\xi}}
 = (1-t)^{-n/2}
   \frac{\sum_{x\in\Lambda} e^{-\pi\|x\|^2/[(1-t)s^2]}}
        {\sum_{x\in\Lambda} e^{-\pi\|x\|^2/s^2}}
 \le(1-t)^{-n/2}.
\]
Consequently
\[
 \mathbb E_{\nu_q} e^{tT}\le\frac{1+q}{q}(1-t)^{-n/2},\qquad
 K(q,t)=\frac{\log((1+q)/q)+(n/2)\log(1/(1-t))}{t}.
 \tag{5}
\]
Put \(a=1-1/\alpha=(\alpha-1)/\alpha\). When \(0\le a\le t\)
Hölder gives \(\mathbb E_{\nu_q}e^{aT}\le e^{aK(q,t)}\).
For \(a<0\), Jensen first gives \(\mathbb E_{\nu_q} T\le K(q,t)\)
and then \(\mathbb E_{\nu_q}e^{aT}\ge e^{aK(q,t)}\).
Each term of \((e^{aT}-1)/(\alpha-1)\) is nonnegative,
including the limit \(T\) at order one. Thus, for all \(z\),
\[
 \left|\frac{\Theta_\alpha(z)-\Theta_1(z)}{\alpha-1}\right|
 \le q\,\frac{e^{aK(q,t)}-1}{\alpha-1}.
 \tag{6}
\]
The convention on the right at order one is \(qK(q,t)\).

An additional one-sided comparison does not use a small \(q\).
[Regev–Stephens-Davidowitz, Proposition 4.1](https://arxiv.org/pdf/1502.04796)
proves that the normalized shifted mass is nondecreasing in
the Gaussian width. Here that mass, at width \(s/\sqrt\alpha\),
is \(\Theta_\alpha(z)/\Theta_\alpha(0)\). Hence
\[
 \frac{\log\Theta_\alpha(z)-\log\Theta_1(z)}{\alpha-1}
 \le
 \frac{\log\Theta_\alpha(0)-\log\Theta_1(0)}{\alpha-1}. \tag{7}
\]
For \(\alpha<1\) both the logarithmic comparison and the sign
of the denominator reverse, so the displayed direction is unchanged.
The derivative limit gives the statement at \(\alpha=1\).
Since \(|\log\Theta_1(z)|=O_{\epsilon_0}(\epsilon)\), it suffices in
the leading one-sided bound to compute the centered quotient.
Inequality (7) does not itself compare the full \(B_\alpha\) of
two cosets.

## 3. Upper windows

When \(b=o(n)\), take \(q=\epsilon\) and
\(t=\sqrt{(b+\log(1+\epsilon))/n}\) in (5). Then
\(K(q,t)=n/2+o(n)\). This works for all \(|u|\le U\) at
\(\alpha=1+u/n\). In the regime \(\epsilon\to0\) also
\(|\Theta_\alpha(z)-1|=O_U(\epsilon)\) by (6). The logarithmic
quotient in (4), in absolute value, is at most
\(1+O_U(\epsilon)\) times the right side of (6), by integrating
the derivative of the log on the segment between the two theta
values. Dividing by \(n\epsilon\) gives
\((e^{u/2}-1)/u+o(1)\), uniformly at \(u=0\) as well. For the
uniformity, write the exponential quotient as
\(K/(n\alpha)\) times the continuous function
\((e^x-1)/x\) at \(x=aK\). This proves the upper bound in (2).

For the sharper positive bound even at nonvanishing \(\epsilon\),
use (7), and take \(q=R\) in (5)–(6); a full-rank lattice has \(R>0\).
For \(\alpha>1\), \(\Theta_\alpha(0)\le1+R e^{aK}\); for
\(\alpha<1\), \(\Theta_\alpha(0)\ge1+R e^{aK}\). Thus in both cases
the centered logarithmic quotient is at most
\[
 \frac{\log(1+R e^{aK})-\log(1+R)}{\alpha-1}
  \quad\left(\frac{RK}{1+R}\text{ at }\alpha=1\right).
 \tag{8}
\]
To make \(K\) uniform, let \(L=b+\sqrt{n(b+1)}+2\).
For \(R\ge\epsilon e^{-\sqrt{n(b+1)}}\), take \(t=\sqrt{L/n}\)
in (5); then \(K\le n/2+o(n)\) uniformly by \(L=o(n)\).
The right side of (8) increases in both \(R\) and \(K\):
for \(R\), the factor \((e^{aK}-1)/(\alpha-1)\) has nonnegative
sign; for \(K\), differentiate the numerator. We may therefore
replace \(R\) by \(\epsilon\), and \(K/\alpha\) by \(n/2+o(n)\).
Changing \(K/\alpha\) by \(o(n)\) costs \(o(n\epsilon)\)
uniformly by the log derivative in (8), including at \(u=0\).

If \(R<\epsilon e^{-\sqrt{n(b+1)}}\), take \(t=1/2\);
then \(K=O(n+\log(1/R))\). With \(|u|\le U\), the centered
quotient is bounded by
\(C_U R K \exp(C_U K/n)\), for example by (6) and positivity
of the centered theta values. Writing \(v_0=\log(\epsilon/R)\),
this is at most
\(C_U\epsilon(n+b+v_0)e^{-v_0/2}=o(n\epsilon)\)
uniformly for the indicated \(v_0\) and large \(n\).
Combining both branches and the \(O(\epsilon)\) error in (4)
gives the upper bound in (1).

When \(n=o(b)\), use \(q=\epsilon\) and \(t=1-\sqrt{n/b}\),
for sufficiently large \(b\). Equation (5) gives \(K/b\to1\)
because \((n/b)\log(b/n)\to0\).
For order \(1+u/b\), (6) gives
\(|\Theta_\alpha(z)-1|=O_U(\epsilon)\) and the absolute upper bound
in (3) by the same logarithmic comparison. This includes fixed rank.

## 4. Dimension-window sharpness from the lattice mean-square formula

Use the Haar probability law of a covolume-one **dual** lattice
\(\Gamma\subset\mathbb R^n\), and take \(\Lambda=\Gamma^*\).
Choose \(s^{-n}=\mu=\epsilon(1-1/n)\). For
\(T(x)=\pi s^2\|x\|^2\) use the nonnegative radial test functions
\[
 f_0(x)=e^{-T(x)},\qquad
 f_\alpha(x)=\frac{e^{-T(x)/\alpha}-e^{-T(x)}}{\alpha-1}
 \quad(\alpha=1:\ f_1=T(x)e^{-T(x)}).
\]
Here \(f_0\) is just a label, not Rényi order zero. The lattice
sums excluding zero give \(R\) and
\(D=(\Theta_\alpha(0)-\Theta_1(0))/(\alpha-1)\).
The [Siegel mean formula](https://doi.org/10.2307/1969027)
gives
\[
 \mathbb ER=\mu,\qquad
 \mathbb ED=\mu\,\frac{\alpha^{n/2}-1}{\alpha-1}.
 \tag{9}
\]
At order one the second mean is \(\mu n/2\).
For completeness, the nonnegative even \(f\) version of the
[Rogers mean-square formula, Theorem 4 with two slots](https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/5823-11511_2006_Article_BF02392493.pdf)
is
\[
 \operatorname{Var}\!\left(\sum_{0\ne x\in\Gamma} f(x)\right)
   =\frac{2}{\zeta(n)}
      \sum_{p,q\ge1}\int_{\mathbb R^n} f(px) f(qx)\,dx ,
 \qquad n\ge3 .
\]
The formula also follows by separating independent pairs of
vectors from those on one primitive line. For the Gaussian tests,
one may first restrict to a ball and then use monotone convergence
for both moments; the right side below is finite.

For \(f_0\), the integral is
\(\mu(p^2+q^2)^{-n/2}\). Uniformly for \(|u|\le U\), the mean-value
theorem in \(\alpha\) gives \(f_\alpha(x)\le C T(x)e^{-T(x)/(1+U/n)}\).
Therefore the integral of \(f_\alpha(px)f_\alpha(qx)\) is at most
\[
 C_U \mu\, n(n+2)\frac{p^2q^2}{(p^2+q^2)^2}
                                 (p^2+q^2)^{-n/2}.
\]
This is the ordinary Gaussian integral of the squared energy:
scaling gives \(n(n+2)/4\) and the stated denominator; the factor
\((1+U/n)^{n/2+2}\) is bounded. Also
\(\sum_{p,q\ge1}(p^2+q^2)^{-n/2}=O(2^{-n/2})\), because
\((2/(p^2+q^2))^{n/2}\le (2/(p^2+q^2))^2\) for \(n\ge4\)
and the latter series converges. Thus
\[
 \operatorname{Var}R=O(\mu\,2^{-n/2}),\qquad
 \operatorname{Var}D=O_U(n^2\mu\,2^{-n/2}).
\]
Since \(b=o(n)\), Chebyshev gives lattices with
\(|R-\mu|\le\epsilon/(2n)\) and \(|D-\mathbb ED|\le\epsilon\),
simultaneously. In particular \(R\le\epsilon\).

To evaluate the logarithmic quotient with no loss if \(u\) is
arbitrarily close to zero, write it as
\[
 D\int_0^1\frac{dv}{1+R+v(\alpha-1)D}.
\]
The denominator is at least 1 (it lies between the two centered theta
values). Replacing \(R,D\) by their means costs \(o(n\epsilon)\)
by the above error bounds. With (9), the resulting expression equals
\[
 \frac{\log(1+\mu\alpha^{n/2})-\log(1+\mu)}{\alpha-1}.
\]
Replacing \(\mu\) by \(\epsilon\) and \(\alpha^{n/2}\) by \(e^{u/2}\)
again costs \(o(n\epsilon)\) uniformly: the first change uses
the derivative with respect to the budget in (8), and the second
uses \((n/2)\log(1+u/n)=u/2+O_U(u^2/n)\).
Equation (4) now proves sharpness for (1) and hence (2).

## 5. Budget-window sharpness from two dual atoms

Take \(s=1\) and a rectangular dual lattice. The smallest nonzero
vectors lie on the first coordinate, with energy
\(T_1=b+\log 2+\sqrt\epsilon\) for its two signs.
For each of the other axes take the one-step energy
\(4b+\log(2n)\). The first pair contributes
\(\epsilon e^{-\sqrt\epsilon}\) to \(R\); its higher multiples
contribute \(O(\epsilon^4)\). The independent remaining coordinates
change the theta product by \(O(\epsilon^4)\) in total
(use \((n-1)e^{-4b-\log(2n)}\le\epsilon^4/2\)).
Hence \(R\le\epsilon\) for all sufficiently large \(b\).
At \(z=0\) the numerator quotient \(D\) is at least the first-pair
contribution
\(\epsilon e^{-\sqrt\epsilon}(e^{aT_1}-1)/(\alpha-1)\).
For \(\alpha=1+u/b\), this has the leading term in (3),
uniformly including the derivative at zero. The log quotient multiplies
\(D\) by \(1+O_U(\epsilon)\) as above; the remaining
\(\log\Theta_1(0)\) term in (4) is \(O(\epsilon)\).
This gives the matching positive lower bound and finishes the
absolute comparison as well.

**Replay.** Run `node verify-lattice-gaussian-entropy-window.js`.
It checks the exact partition/entropy identities on generated small
lattices, the derivative quotient including near order one, the radial
Gaussian integral, and the two-atom lower construction. The probabilistic
existence of high-dimensional extremizers in §4 uses the cited
mean and mean-square theorems, not numerical sampling.
