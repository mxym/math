# A large Mahler gap for periodic congruences

Research note, 27 November 2026. The test class in [Jha–Thangadurai, Theorem 7.1, arXiv:2610.33631v1](https://arxiv.org/pdf/2610.33631) consists of monic reciprocal polynomials \(P\) of even degree, without cyclotomic factors, with odd inner coefficients \(-1\bmod 5\) and even inner coefficients \(2\bmod5\). Their explicit lower bound was \((976/975)^{1/3}\).

**Theorem.** Every polynomial in that class satisfies
\[
 M(P)\ \ge\ \left(\frac{25+\sqrt{561}}{8}\right)^{1/3}
 \ >\ \frac95.
\]
Irreducibility is not needed. At even degree \(d\ge6\) the more informative lower bound is
\[
 M(P)\ \ge\
 \left(T_d+\sqrt{T_d^2-1}\right)^{2/d},
 \qquad T_d=\frac{(5/2)^{d/2}}5.
 \tag{1}
\]
The bound in (1) tends to \(5/2\), and \(M(P)>5/2\) when \(10\mid d\). This rules out the class from the search for measures below Lehmer's \(1.176280\ldots\), including at arbitrarily large degree. Neither the unrestricted conjecture nor an exact infimum for this class is claimed.

More generally, let \(m\ge2\), and let the odd inner coefficients be any single residue \(a\bmod m\), with every even inner coefficient \(2\bmod m\). Then \(M(P)>4/3\) for even \(d\ge6\) when \(m\ge3\), and for even \(d\ge12\) when \(m=2\). This uses the following resultant estimate.

## 1. Cycle-resultant estimates

Let \(P\in\mathbb Z[x]\) be monic and reciprocal of degree \(D\), with constant term \(1\) and no root of unity. Suppose a monic polynomial \(H\) of degree \(h\) divides both \(P\) and \(x^N-1\) modulo \(m\). Then
\[
 m^h\mid\operatorname{Res}(P,x^N-1),\qquad
 0<\big|\operatorname{Res}(P,x^N-1)\big|
 \ \le\ 2^D\cosh^2\!\left(\frac N2\log M(P)\right).
 \tag{2}
\]
Congruence-controlled resultants in Lehmer's problem go back at least to [Silverman](https://doi.org/10.5802/jtnb.820) and [Borwein–Dobrowolski–Mossinghoff](https://annals.math.princeton.edu/2007/166-2/p02). Here we use the long cycle divisor before estimating the resultant, and exploit reciprocity in its archimedean estimate instead of bounding each root independently.

The divisibility is elementary and works for composite \(m\). If a monic \(H\) divides two polynomials \(P,Q\) modulo \(m\), put \(L=\deg P+\deg Q\). Each column of their Sylvester matrix represents a monomial multiple of \(P\) or \(Q\), of degree less than \(L\). In the integral basis
\[
 1,x,\ldots,x^{h-1},H,xH,\ldots,x^{L-h-1}H
\]
the first \(h\) entries are coefficients of the remainder on division by \(H\), hence multiples of \(m\). The basis change is unimodular by monicity. Thus \(m^h\mid\operatorname{Res}(P,Q)\). For \(Q=x^N-1\), the resultant is nonzero by the hypothesis on \(P\).

Pair the roots of \(P\) as \(\alpha_i,\alpha_i^{-1}\), with \(r_i=|\alpha_i|\ge1\). Their contribution to the absolute resultant is bounded by
\[
 (1+r_i^N)(1+r_i^{-N})=4\cosh^2((N/2)\log r_i).
\]
For nonnegative \(x,y\), \(\cosh(x+y)\ge\cosh x\cosh y\), and \(M(P)=\prod_i r_i\). Multiplying yields the upper bound in (2). The same argument includes unit-circle pairs, for which \(r_i=1\).

There is also a prime-power variant. For a prime \(p\mid m\) and an integer \(k\ge1\),
\[
 m^h p^{kh}\mid\operatorname{Res}(P,x^{p^kN}-1).
 \tag{3}
\]
Indeed \(\Phi_{p^i}(x^N)\equiv(x^N-1)^{p^{i-1}(p-1)}\pmod p\) for \(i\ge1\), so each of their resultants with \(P\) is divisible by \(p^h\). Multiply these with the \(x^N-1\) resultant from (2). The upper bound in (2) applies with \(N\) replaced by \(p^kN\).

## 2. Applying the estimates to the alternating mod-5 class

For \(d\) even set
\[
 H_d=1+x^2+\cdots+x^{d-2}=\frac{x^d-1}{x^2-1}.
\]
The coefficient congruence in the theorem says exactly \(P\equiv (x^2-x+1)H_d\pmod5\). Thus \(\operatorname{Res}(P,x^d-1)\) is divisible by \(5^{d-2}\), and (2) proves (1). This treats all \(d\ge6\) thus far. If \(10\mid d\), then \(H_d(1)=H_d(-1)=d/2\equiv0\pmod5\), so \(5\mid P(1),P(-1)\). The \(H_d\) resultant already contains \(5^{d-2}\), and multiplying the two linear resultants gives \(5^d\) in the \(x^d-1\) resultant. Hence \(\cosh((d/2)\log M)\ge(5/2)^{d/2}\). Since \(\cosh((d/2)\log(5/2))<(5/2)^{d/2}\), this proves \(M>5/2\) in these degrees.

To compare all large-degree bounds to a single constant, put
\[
 U=\left(\frac{25+\sqrt{561}}8\right)^{1/3}.
\]
Then \(U^3+U^{-3}=25/4\), \(9/5<U<2\), and the ratio
\[
 \frac{2^d\cosh^2((d/2)\log U)}{5^{d-2}}
 =\frac{25}4\left[\left(\frac{2U}5\right)^d
                  +2\left(\frac25\right)^d
                  +\left(\frac2{5U}\right)^d\right]
\]
is exactly one at \(d=6\) and decreases with \(d\). It follows that \(M\ge U\) for every \(d\ge6\).

At degree \(2\), the odd coefficient is \(-1\bmod5\); if it is \(-1\) the polynomial is cyclotomic, and otherwise its absolute value is at least \(4\), giving \(M\ge2+\sqrt3\). At degree \(4\), write
\[
 P=x^4+A x^3+B x^2+A x+1,\qquad
 Q(t)=t^2+A t+(B-2),\quad t=x+x^{-1}.
\]
Here \(P(x)=x^2Q(x+x^{-1})\). Suppose \(M(P)\le2\). Each trace root has \(|t|\le M+M^{-1}\le5/2\), since a pair of reciprocal roots contributes its outside radius to \(M\). Thus \(A\in\{-1,4\}\) and \(B-2\in\{-5,0,5\}\) from the congruences and Vieta's formulas. For \(B-2=-5\), in either case there is a real trace root outside \([-5/2,5/2]\). For \(B-2=0\), \(A=4\) also gives a forbidden trace root \(-4\), while \(A=-1\) gives the cyclotomic product \((x^2+1)(x^2-x+1)\). For \(B-2=5\), the trace roots are nonreal conjugates with imaginary part at least \(1\). Their two reciprocal pairs have conjugate outside roots of equal modulus \(r\) with \(r^2=M\le2\). Writing \(x=r e^{i\theta}\) in \(t=x+x^{-1}\) gives \(|\operatorname{Im}t|\le r-r^{-1}\le1/\sqrt2<1\), a contradiction. Therefore \(M>2\) at degree \(4\), completing the proof of the uniform bound.

## 3. Any modulus with the even inner coefficient \(2\)

For the general congruence pattern the identity modulo \(m\) is \(P\equiv(x^2+a x+1)H_d\), so still \(h=d-2\). For \(m\ge4\), (2) gives a resultant divisor at least \(4^{d-2}\) at cycle length \(d\). For \(m=3\), (3) with \(p=3,k=1\) gives \(9^{d-2}\) at cycle length \(3d\). For \(m=2\), taking \(p=2,k=2\) gives \(8^{d-2}\) at cycle length \(4d\). For each pair \((B,s)\in\{(4,1),(9,3),(8,4)\}\), compare at \(M=4/3\):
\[
 \frac{2^d\cosh^2((sd/2)\log(4/3))}{B^{d-2}}
 =
 \frac{B^2}{4}\left[
 \left(\frac{2(4/3)^s}{B}\right)^d+
 2\left(\frac2B\right)^d+
 \left(\frac{2(3/4)^s}{B}\right)^d\right].
\]
All three bases are less than one. The ratio is strictly below one at \(d=6,6,12\), respectively, by raising the rational numbers in the formula to integer powers. It remains below one for every larger degree, which gives the asserted \(4/3\) bounds.

The [exact verifier](verify_factor_lehmer_periodic_resultant.js) uses integer multiplication matrices and fraction-free determinants on synthetic polynomials to check the congruence divisibilities. It also checks the rational starting thresholds and the numerical comparisons with \(9/5\) and \(2\). The proofs above are not based on numerical root-finding or the finite sample.
