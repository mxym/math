# An auxiliary-resultant gap above 1.624 in the uniform mod-three class

Let \(P\in\mathbb Z[x]\) be monic and reciprocal of even degree \(D\ge2\), with constant coefficient one and no cyclotomic root. Suppose that **every inner coefficient is \(2\bmod3\)**. Put
\[
 A=\left(\frac{3^{17}}{218}\right)^{1/24}=1.739903659\ldots,\qquad
 \rho=1.722083805\ldots,
\]
where \(\rho>1\) is the largest root of \(x^4-x^3-x^2-x+1\). Then:
\[
  M(P)>A\,3^{-1/(2D)},\qquad
  3\mid D\ \Longrightarrow\ M(P)>A.
\]
In particular \(M(P)>203/125=1.624\) at every degree in the stated class. At degree four the minimum is exactly \(\rho\). If any polynomial in this class improves upon that example, its degree must be an even integer \(8\le D\le52\) **not divisible by three**. We do not exhaust those remaining degrees.

This is the \(r=2,m=3\) case in [Jha–Thangadurai, Theorem 1.2](https://arxiv.org/abs/2610.33631), which obtains a smaller explicit bound by a different auxiliary calculation. The [previous periodic resultant estimate](FactorLehmerPeriodicResultantGap.md) gave a \(4/3\) bound in degrees \(D\ge6\) for the larger alternating class with even inner coefficient \(2\bmod3\). The improvement here exploits the **joint** unit-circle norm of three factors and full divisibility for one of them, not the norm of a single long cycle. Irreducibility is unnecessary when no root of unity is present. The unrestricted Lehmer problem is not addressed.

## 1. The auxiliary norm

Use
\[
                 F(z)=(z-1)^{12}(z+1)^2(z^2+z+1)^5.
\]
Its degree is 24. On the unit circle, with \(x=\operatorname{Re}z\),
\[
 |F(z)|^2=[2(1-x)]^{12}[2(1+x)]^2(1+2x)^{10}.
\]
This vanishes at \(-1,-1/2,1\). On the two open intervals separated by \(-1/2\), an interior critical point is a root of \(24x^2+17x-5\), by logarithmic differentiation. Both roots are enclosed, respectively, in
\[
 \left[\frac{-931893}{10^6},\frac{-931892}{10^6}\right],
 \qquad
 \left[\frac{223559}{10^6},\frac{223560}{10^6}\right].
\]
They are the only possible maxima. In each interval, bounding the three nonnegative factors independently by endpoint bounds gives a value strictly smaller than \(218^2\), using only rational comparisons. Thus \(\sup_{|z|=1}|F(z)|<218\).

For an arbitrary complex \(w\), the maximum-modulus principle applied to \(F\) on the disk and to the reversed polynomial \(w^{24}F(1/w)\) gives
\[
                  |F(w)|<218\max(1,|w|)^{24}.
\]
In particular, taking a product at \(w=\alpha^D\) over all roots \(\alpha\) of \(P\) yields
\[
             |\operatorname{Res}(P,F(x^D))| < 218^D M(P)^{24D}.       \tag{1}
\]
The extra factor \((z+1)^2\) requires no congruence for its resultant, but lowers the joint norm sufficiently relative to the total degree. This same construction can use other nonvanishing factors by keeping their divisibility and their contribution to the joint circle norm separately.

## 2. The congruence divisor

Let \(H_D=1+x+\cdots+x^{D-1}\). The coefficient hypothesis gives
\[
                         P\equiv(x+1)H_D\pmod3.
\]
The resultant of \(P\) with any polynomial \(Q\) divisible modulo three by a common monic factor of degree \(h\) is divisible by \(3^h\). In the Sylvester matrix, use the integral coefficient basis consisting of the first \(h\) monomials followed by the monomial multiples of that factor. The first \(h\) rows are then the remainders modulo that monic factor, all divisible by three. This proves the required divisibility even when the factor has repeated roots.

Since \(x^D-1=(x-1)H_D\), its nonzero resultant with \(P\) has a divisor \(3^{D-1}\). If \(3\mid D\), then \(P(1)\equiv2D\equiv0\bmod3\), so multiplicativity with the two factors \(H_D,x-1\) upgrades the divisor to \(3^D\). Meanwhile
\[
        x^{2D}+x^D+1\equiv(x^D-1)^2=(x-1)^2H_D^2\pmod3.
\]
Because \(D\) is even, \(x+1\mid H_D\), so this is divisible modulo three by \(P\bmod3\) itself. The resultant with \(x^{2D}+x^D+1\) is therefore divisible by \(3^D\) at **every** even degree. Each of \(x^D-1,x^D+1,x^{2D}+x^D+1\) has only roots of unity, so its resultant with \(P\) is a nonzero integer. It follows from the factorization of \(F(x^D)\) that
\[
      |\operatorname{Res}(P,F(x^D))|
        \ge 3^{17D-12}\quad\text{always}, \qquad
      |\operatorname{Res}(P,F(x^D))|\ge 3^{17D}\quad\text{if }3\mid D .
\]
Combine with (1) to obtain the claimed degree-dependent bounds.

At \(D=8\) the lower bound \(A3^{-1/16}\) already exceeds \(203/125\). It increases with \(D\), and \(D=6\) uses the stronger divisor. At \(D=54\) the lower bound \(A3^{-1/108}\) exceeds \(17221/10000>\rho\). Both are finite rational power comparisons, replayed by the companion checker. All degrees divisible by three already have \(A>\rho\).

## 3. Degrees two and four

In degree two write \(P=x^2+a x+1\). If \(M(P)\le\rho\) then \(|a|\le \rho+\rho^{-1}<2.304\), so \(a\equiv2\bmod3\) only allows \(-1,2\), both cyclotomic. Thus no degree-two example reaches \(\rho\).

For degree four write \(P=x^4+a x^3+b x^2+a x+1\) and \(Q(t)=t^2+a t+(b-2)\) with \(t=x+x^{-1}\). If \(M(P)\le\rho\), every trace root has \(|t|\le\rho+\rho^{-1}\), so by the coefficient congruences and Vieta,
\[
                  a\in\{-4,-1,2\},\qquad b-2\in\{-3,0,3\}.
\]
For \(b-2=0\), the possible trace roots \(0,-a\) either give cyclotomic factors or include \(4\), too large. For \(b-2=-3\), at \(a=-1\) the larger trace root is \((1+\sqrt{13})/2=\rho+\rho^{-1}\); the other lies in \((-2,2)\). The resulting quartic is \(x^4-x^3-x^2-x+1\), has measure \(\rho\), and has no root of unity: it is not cyclotomic, and has no possible degree-one or degree-two cyclotomic factor by the trace roots (these factors would require traces from \(\{-2,-1,0,1,2\}\)). At the other values of \(a\), take \(t\) of absolute value \(\rho+\rho^{-1}\) with sign opposite to \(a\). Then \(Q(t)<0\), so there is a real trace root of larger absolute value. For \(b-2=3,a=-4\), one trace root is 3. For \(b-2=3,a=-1,2\), the imaginary part of a trace root has absolute value at least \(\sqrt2\). But a trace from a reciprocal pair with outside radius at most \(\rho\) has imaginary part at most \(\rho-\rho^{-1}<\sqrt2\). This completes the low-degree classification.

The [standard-library verifier](verify_factor_lehmer_auxiliary_mod_three.py) independently checks the two rational isolations and circle bounds, the thresholds at degrees eight and 54, the rational bracket on \(\rho\), and the finite bounds used in the low-degree cases. No numerical root finding enters the proof.
