# An arbitrary one-prime-mark dual barrier for square-root \(P_3\)

Written research note, 2026-11-24. This rules out improving \(P_3\) just by changing the single-prime Richert penalty while paying every mark via the specified one-mark cap and suppressing rank four by angle size alone. It does not bound the true mark population below, and is not a barrier to Buchstab switching, two-prime weights, genuine rank geometry or stronger analytic caps.

## Normalization and continuous certificate

Take the literal square-root prime window \(p\in(a\sqrt N,b\sqrt N]\), \(L=\log N\), roughness \(z=N^\mu\), and \(B=2X S_N/L\) as in the current [square-root P3 target](PrimeOppositeSquareRootP3Target.md). Restore squarefree exceptions separately as in the original proof. Write \(t=\log q/L\) for a true prime marking the complement \(N-p\). Let an arbitrary integrable one-mark penalty \(w(t)\) assign to a complement the score \(1-\sum_{q\mid N-p}w(\log q/L)\). A size-only proof that no rank-four number can positively contribute must verify
\[
 w(t_1)+w(t_2)+w(t_3)+w(t_4)\ \ge 1
\]
on every admissible distinct rank-four angle tuple \(t_i\ge\mu,\ \sum_i t_i=1\) (or at all the corresponding nearby total sums). This necessary condition already suffices for the obstruction. We make no assertion that each abstract profile is realized by the actual prime-complement population for any one \(N\).

Suppose a true mark cap is used with normalized coefficient \(U(t)\) in units \(B/q\). The coefficient charged to \(B\) after summing true prime marks is \(\int w(t)c(t)\,dt\) for \(w\ge0\), where \(c(t)=U(t)/t\) by harmonic prime summation. This is the continuous budget for fixed/step angular windows or piecewise Riemann weights (for arbitrary measurable \(w\), it is the mathematical optimization with this budget). The argument does not claim a harmonic estimate uniform in arbitrary target-dependent fine sign oscillations.

Take \(x,y\) in \([\mu,1/4]\) and the test profile \((x,y,1/2-x,1/2-y)\). Apart from a null set the four angles are distinct. If \(F(x)=w(x)+w(1/2-x)\), then \(F(x)+F(y)\ge1\) almost everywhere. In fact \(F(x)\ge1/2\) a.e.: otherwise the product of a positive-measure sublevel with itself contradicts the two-point inequality. Consequently for nonnegative weights,
\[
 \int w(t)c(t)\,dt\ \ge\
 \frac12\int_\mu^{1/4}\min\{c(x),c(1/2-x)\}\,dx .
 \tag{1}
\]
If a continuous certificate is performed only at total \(\le1\) with a fixed strict collar, use mirrors \(1/2-\varepsilon-x\) and half-band endpoint \(1/4-\varepsilon/2\); letting \(\varepsilon\downarrow0\) recovers the same numerical gap. Standard finite approximating profiles admit the same limiting obstruction by taking interior points and distinct angles. At fixed \(N\), the actual prime complement has angle sum \(1-O(N^{-1/2}/L)\), an even smaller collar.

## What one-mark cap families are included

For the traditional conditional BV linear upper use maximal optimistic source test level \(N^{1/4}\), so residual exponent at mark \(t\) is at most \(1/4-t\). The upper linear numerator \(h(s)=s e^{-\gamma} F_{\rm lin}(s)/2\) is at least 1 by its initial interval and the positive delay equation. Thus this route has normalized cap density
\[
 c_{\rm BV}(t)\ge\frac1{t(1/4-t)}\qquad (t<1/4);
\]
it is not a candidate at or above \(1/4\). Shrinking the cutoff retains the bound. The switched affine upper, even using the exact positive asymmetric kernel \(J\), has
\[
 c_{\rm aff}(t)\ge\frac{2}{t(1/2-t)^2}\qquad (t<1/2).
\]
Indeed the asymmetric denominator cannot exceed the full two-root Selberg denominator at the same divisor cutoff \(K\le N^{(1/2-t)/2}\) (every squarefree factor is pointwise no larger). Equivalently the exact leading kernel obeys \(J(v)\le v^2/2\). Fixed shaves in the physical divisor level only worsen this floor. Therefore for the pointwise min of these two cap families, and for \(x\le1/4\), the integrand in (1) is bounded below by
\[
 \min\left\{\frac1{x(1/4-x)},\frac{2}{x(1/2-x)^2}\right\}.
 \tag{2}
\]
In particular the reflected mark \(1/2-x\) cannot give a smaller floor: its only candidate here is affine, with denominator \((1/2-x)x^2\le x(1/2-x)^2\).

For the actual target range \(.05\le\mu\le.07\), the already proved exact-LCM/compatible-support obstruction at the middle strip \(t\in[.20,.23]\), including its enlargement after joint \(s\)-orthogonality and prime local correlation, shows that the optimized two-label squares *under that existing support certification* cannot reduce the leading affine cap either. This allows (2) for the union of the two classical cap families and those existing square optimizations. It does not extend that optimized-square assertion to \(\mu<.05\); below .05 the conclusion below is only for the classical BV and actual exact-affine cap families. A signed residue improvement or an analytically different cap is not assumed.

## Explicit budget gap, including the tighter P4-kernel cutoff

On \(x\in[\mu,.20]\), (2) equals the first entry: its crossing occurs at \((\sqrt2-1)/2>.20\). On \([.20,.21]\), both entries are at least 100. On \([.21,.25]\) both are at least 108 (the affine expression has minimum 108 on the whole interval \(0<x<1/2\)). This gives the explicit lower charge
\[
    2\log\!\left(\frac{4(.25-\mu)}{\mu}\right)+2.66.
 \tag{3}
\]
The usual source-base linear lower coefficient is at most \(e^{-\gamma}/(2\mu)<.281/\mu\), since \(f_{\rm lin}(s)\le1\) (the standard lower-sieve function increases to 1; the same bound follows by applying the lower linear sieve to the integer model and making its rough-number density converge to the Mertens product). The gap between (3) and \(.281/\mu\) is positive for every \(.03\le\mu\le.07\): at .03 the comparison is \(2\log(88/3)+2.66>.281/.03\); its derivative is
\[
 \frac{.281}{\mu^2}-\frac{.5}{\mu(.25-\mu)}>0
\]
through .07. The [standalone certificate](check_p3_arbitrary_single_mark_dual.js) uses only directed rational arithmetic. For the Euler factor, \(H_{16}-\log16-1/32<\gamma\) by the first strict Euler–Maclaurin bound for harmonic numbers, and this lower bound exceeds .5768. The degree-eight exponential Taylor lower at .5768 exceeds \(500/281\). For the logarithmic endpoint, \(\log(88/3)=4\log 2+\log(11/6)\); atanh series with outward positive geometric tail give the exact comparisons. Thus even the new .0393 P4 rough cutoff cannot yield a \(P_3\) proof merely by arbitrary single-penalty retuning inside the classical caps.

## Even standard conditional lower credits do not rescue signed penalties on [.05,.07]

If \(w\) can have either sign but only upper caps are used, replace its negative part by zero: this increases all rank penalties, without any lower credit in the guaranteed cap objective. Stronger, suppose the usual conditional BV linear lower credits are also available at negative marks, with normalized density
\[
 c_-(t)=\sup_{\substack{d\le .25-t\\d/\mu>2}}\frac{g(d/\mu)}{td},
 \qquad g(s)=s e^{-\gamma}f_{\rm lin}(s)/2,
\]
and zero outside this range. The charge is then \(\int[c_+(t)w_+(t)-c_-(t)w_-(t)]dt\), where \(c_+\) is whichever existing upper density is selected. This still has no positive budget when \(.05\le\mu\le.07\).

Indeed \(c_-\) is supported on \(t\le .25-2\mu\le.15\), and \(g(s)=\log(s-1)\le\log3<1.1\) for the relevant \(2\le s\le4\). The ratio \(g(s)/s\) increases on that interval: its derivative numerator is \(s/(s-1)-\log(s-1)\ge4/3-\log3>0\). Thus
\[
 c_-(t)\le \frac{1.1}{t(.25-t)}
              \le\frac2{t(.5-t)^2}
\]
on its support, where the latter inequality follows from the quadratic check \(1.1(.5-t)^2\le 2(.25-t)\) on \([.05,.15]\). The value of \(c_-(t)\) is also at most the BV upper cap at the same maximal level by \(f_{\rm lin}\le F_{\rm lin}\); using smaller level or cutoff gives no smaller upper since \(F_{\rm lin}\) decreases to 1 and \(h(s)\) is nondecreasing. At the reflected point \(t'=1/2-t\ge.35\), its affine floor is at least \(2/(.35\cdot.15^2)>253\), whereas the unreflected lower credit is less than \(1.1/(2\mu^2)\le220\). The reflected cap therefore also dominates the other lower credit.

Hence the symmetric function \(\lambda(t)=\min(c_+(t),c_+(1/2-t))\) on \([\mu,1/2-\mu]\) (and 0 off this band) lies between the lower and upper densities at every point. Deducting signed credits cannot reduce the budget below \(\int\lambda w\). The same test \(w(x)+w(1/2-x)\ge1/2\) shows that this is bounded below by the right-hand side of (1); outside the band the lower credit is zero. So the quantitative gap persists for signed penalties with these standard lower credits. The assertion does not cover a genuinely improved joint lower/upper pairing or cancellation in the combined signed mark remainder.

Status: a finite-angle linear-programming dual witness, not an obstruction to general weighted-sieve or P3 methods.