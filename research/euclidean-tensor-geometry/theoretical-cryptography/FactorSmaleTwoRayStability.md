# Quantitative stability for Smale's two-ray bound

Write \(S(f)=\min_{f'(c)=0}|f(c)/c|\) for a polynomial with \(f(0)=0\),
\(f'(0)=1\). Hinkkanen and Kayumov proved \(S(f)\le 2/3\) when the
critical points are on two rays through zero, including the equality cases;
see [Theorem 1.2, Constructive Approximation 32 (2010), 385–392](https://doi.org/10.1007/s00365-009-9079-6).
[Dubinin (2026)](https://doi.org/10.4213/im9704e) gives further inequalities
when the critical points are real. The claims here are quantitative stability
on the two-ray class and a locally uniform near-extremal polynomial
description, not the original \(2/3\) inequality or a claim for unrestricted
degree five or six. For the failure of the unrestricted conjecture and the
unrestricted constant, see [Adamczewski–Colbrook](https://arxiv.org/abs/2610.36158)
and [Goel](https://arxiv.org/abs/2611.17373).

## Statement

If all critical points are on one ray, \(S(f)\le1/2\). Otherwise rotate
and scale via \(f(z)\mapsto f(cz)/c\), so that the nearest critical
point on the ray having the smaller minimum radius is \(1\), and the
nearest on the other ray is \(u\zeta\), \(u\ge1,\ |\zeta|=1,\ \zeta\ne1\).
Delete these two critical points, each once. For the remaining multiset put
\[
 A=\sum_{\text{first ray}}\frac1{|c|},\quad
 B=\sum_{\text{second ray}}\frac1{|c|},\quad
 E=\sum_{\text{remaining }c}\frac1{|c|^2},\quad
 a=B-A,\quad b=\frac23(1-1/u),\quad D=1+\Re\zeta.
\]
Set \(\varepsilon=2/3-S(f)\). If \(u>2\), then
\(\varepsilon\ge5/3024\). If \(1\le u\le2\), then
\[
 \varepsilon\ \ge\ \frac5{3024}(u-1)^2
  +\frac5{128}\min\left(1,\frac{|a-b|}{8}+
                     \frac{E}{288}+\frac{D}{36}\right). \tag{1}
\]
The exponents in the separate consequences
\(u-1=O(\sqrt\varepsilon)\), \(|a-b|=O(\varepsilon)\),
\(E=O(\varepsilon)\) and \(D=O(\varepsilon)\) are all best possible.

Moreover, for every fixed \(R>0\), as \(\varepsilon\to0\) we have
\[
 \sup_{|z|\le R}|f'(z)-(1-z^2)|+
 \sup_{|z|\le R}|f(z)-(z-z^3/3)|=O_R(\sqrt\varepsilon). \tag{2}
\]
There is no bound on the degree in (1) or (2), and the exponent in
(2) is best possible. Equation (2) is a necessary structural
description, not a sufficient test on far critical values.

## Two endpoint envelopes

For a critical point \(c\), integrate \(f'(tc)\) over \(0\le t\le1\)
to get \(f(c)/c\). If the roots of \(f'\) are all on one ray, take the
nearest; the factor \(1-t\) and factors in \([0,1]\) prove the \(1/2\) bound.
For two rays, take either nearest endpoint \(c=1\) or \(u\zeta\). Let
\(L=|c|\), \(s=|c|/|c_{\rm other}|\), and
\(k=a\) at \(c=1\), or \(k=-ua\) at \(c=u\zeta\).
In the absolute-value integral each opposite-ray factor is bounded by
\(1+tL/|c_j|\); the same-ray factors are \(1-tL/|c_j|\).
For the two distinguished factors this gives
\((1-t)(1+st)\), and for the remaining factors the inequality
\(1+x\le e^x\) gives \(e^{kt}\). This is the antipodal majorization from
the Hinkkanen–Kayumov proof. In the distinguished opposite-ray factor
we can retain the exact multiplicative improvement
\[
 \sqrt{1-\frac{2stD}{(1+st)^2}}\ \le\
      \exp\!\left(-\frac{stD}{(1+st)^2}\right).
\]
In addition, for \(|x|\le1/2\),
\(\log(1+x)\le x-(2/9)x^2\), by the second derivative bound on this interval.

Use \(c=1\) if \(a\le b\) and \(c=u\zeta\) otherwise.
Then \(k\le b_s=(2/3)(1-s)\), and \(b_s-k\ge|a-b|\).
Define
\[
 W_s(t)=(1-t)(1+st)e^{b_st},\qquad
 \Phi(s)=\int_0^1 W_s(t)\,dt.
\]
The chosen endpoint has ratio at most \(\Phi(s)\).
If \(u\le2\), then \(s\in[1/2,2]\) and on \(I=[1/8,1/4]\) each remaining
\(|x|=tL/|c_j|\le1/2\), since \(L\le2\) and every \(|c_j|\ge1\).
Also \(\sum x^2\ge E/64\) and \(st/(1+st)^2\ge1/36\).
Consequently the chosen endpoint's majorant on \(I\) is at most
\(W_s(t)e^{-V}\), where \(V=|a-b|/8+E/288+D/36\).
Elsewhere \(W_s\) suffices. On \(I\), \(e^{b_st}\ge5/6\), hence
\(\int_I W_s\ge5/64\). Since \(1-e^{-V}\ge\min(V,1)/2\), this proves
the second summand of (1) in addition to the deficit \(2/3-\Phi(s)\).

## Radial deficit

Let \(w=(2/3)(s-1)\) and use the probability density proportional to
\(t(1-t)e^{-wt}\) on \([0,1]\), with normalizing integral \(Z_s\) and
mean \(\mu\). Differentiation gives
\[
 \Phi'(s)=\frac{Z_s}{3}(1-2s\mu).
\]
Integrating the derivative of \(t^2(1-t)^2e^{-wt}\) gives
\(1-2\mu=(w/2)\mathbb E[t(1-t)]\). Using \(t(1-t)\le t\) shows
\(\mu\ge[2+(s-1)/3]^{-1}\) for \(s\ge1\) and
\(\mu\le[2-(1-s)/3]^{-1}\) for \(s\le1\).
Thus \(\Phi\) increases up to \(s=1\) and decreases thereafter, and
\(\Phi(1)=2/3\). On \([1/2,2]\), \(Z_s\ge1/18\) and
\(|1-2s\mu|\ge(5/7)|s-1|\); therefore
\[
 2/3-\Phi(s)\ \ge\ (5/756)(s-1)^2.
\]
Here \(s\) is \(u\) or \(1/u\), so for \(u\le2\) one has
\(|s-1|\ge(u-1)/2\), and for \(u>2\) monotonicity gives the weaker
constant gap \(5/3024\). This completes (1).

## Complex first moment and local limit

The only new issue if the degree grows is cancellation of a complex
linear term from many individually distant critical points.
Put \(r=1/u\), \(\omega=-A-\bar\zeta B\), \(q=\Re\omega-b\) and
\(\beta=\Im\omega\). We can take \(\varepsilon\) sufficiently small;
(1) gives \(|r-1|+|1+\zeta|=O(\sqrt\varepsilon)\),
\(E=O(\varepsilon)\), and \(a-b=O(\varepsilon)\) in absolute value.
In particular \(q\le a-b=O(\varepsilon)\), since
\(\Re\omega=a-DB\). For \(t\in[0,1]\), the analytic logarithm of the
remaining product is \(\omega t+O(E)\), uniformly: all
\(|t/c_j|\le\sqrt E<1/2\), and the sum of the power-series remainders
is \(O(\sum |t/c_j|^2)\). Thus
\[
 f(1)=\int_0^1 W_r(t)e^{qt+i\beta t}\,\Xi(t)(1+O(E))\,dt,\qquad
 \Xi(t)=\frac{1-r\bar\zeta t}{1+rt},
\]
where errors inside an integral are uniform and may be complex.
Here \(|\Xi|\le1\) and \(|\Xi-1|=O(\sqrt\varepsilon)\).
If \(q\le0\), the loss \(\int W_r(1-e^{qt})\) is bounded below
by a positive absolute constant times \(\min(1,-q)\) (restrict to
\(I\)). But \(|f(1)|\ge2/3-\varepsilon\) and
\(\int W_r=\Phi(r)\le2/3\), so the loss is \(O(\varepsilon)\).
Together with the upper bound for \(q\), this gives \(|q|=O(\varepsilon)\).

Also \(1-|\Xi|=O(D)=O(\varepsilon)\), from
\(|\Xi|^2=1-2rtD/(1+rt)^2\). Let \(d\nu=W_r\,dt/\Phi(r)\);
replacing \(\Xi\) by \(\Xi/|\Xi|\) and deleting \(e^{qt}(1+O(E))\)
therefore changes the normalized integral by \(O(\varepsilon)\).
The unimodular variable \(T(t)=e^{i\beta t}\Xi(t)/|\Xi(t)|\)
satisfies \(|\int T\,d\nu|\ge1-O(\varepsilon)\).
For the unit complex number \(\eta\) in the direction of this mean,
\(\int|T-\eta|^2d\nu=2(1-|\int T\,d\nu|)=O(\varepsilon)\).
Since \(\Xi/|\Xi|\) differs from \(1\) by \(O(\sqrt\varepsilon)\),
we also have \(\int|e^{i\beta t}-\eta|^2d\nu=O(\varepsilon)\).
It follows that
\[
 O(\varepsilon)\ \ge\
 1-\left|\int e^{i\beta t}d\nu\right|^2
 =\iint[1-\cos(\beta(t-v))]\,d\nu(t)d\nu(v)
 \ \ge\ c\min(1,\beta^2)
\]
for some absolute \(c>0\). For the last inequality restrict both
variables to \([1/4,3/4]\), where the density has a fixed positive
lower bound. The uniform average of the integrand on this square is
\(1-(\sin(\beta/4)/(\beta/4))^2\), which has a positive quadratic
term at zero, is strictly positive elsewhere, and tends to one as
\(|\beta|\to\infty\). Hence \(\beta=O(\sqrt\varepsilon)\), and also
\(\Re\omega=q+b=O(\sqrt\varepsilon)\).

On \(|z|\le R\), for sufficiently small \(\varepsilon\) the same
logarithm estimate is \(\omega z+O_R(E)\); thus the remaining product
is \(1+O_R(\sqrt\varepsilon)\). The two distinguished factors
\((1-z)(1-r\bar\zeta z)\) differ from \(1-z^2\) by
\(O_R(\sqrt\varepsilon)\). Integrating the resulting derivative
estimate along a segment proves (2).

## Sharp orders

* **Radial deficit and local convergence:** take \(u=1+h\),
  \(\zeta=-1\), \(0<h\le1/10\), and
  \(f'(z)=(1-z)(1+rz)(1+bz)\), with \(r=1/u\) and
  \(b=(2/3)(1-r)>0\). The two near ratios are
  \(2/3-(s-1)^2/18\), \(s=r,u\). At \(-1/b\) the signed
  ratio is \(3/4-r/(12b^2)\), of absolute value \(>2/3\).
  Hence \(\varepsilon=h^2/18\) exactly. The coefficient of \(z^2\)
  in \(f\) is \((r-1)/6\), forcing an \(\Omega_R(h)\) difference
  from the limiting cubic on any radius-\(R>0\) disk by Cauchy's
  coefficient bound.
* **Angular deficit:** take just the two critical points \(1,\zeta\).
  Both squared ratios are \(4/9-D/6\). Taking \(\zeta\to-1\) off
  the real axis gives \(\varepsilon\asymp D\).
* **Remaining quadratic mass:** take
  \(f'(z)=(1-z^2)(1-z^2/M^2)\), real \(M\ge4\); the near ratios
  are \(2/3-2/(15M^2)\), and the far signed ratios are
  \(2/3-2M^2/15\). Thus \(\varepsilon=E/15\) exactly.
* **First-moment imbalance:** take
  \(f'(z)=(1-z^2)(1-z/M)\), real \(M\ge4\). The near ratios are
  \(2/3\pm1/(4M)\); the far signed ratio is \(1/2-M^2/12\).
  Thus \(\varepsilon=|a-b|/4\) exactly.

The companion verifier checks rational and Gaussian-rational polynomial
fixtures and the exact example formulas. It does not replace the analytic
inequalities or the local uniform proof.
