# Limits of fixed polynomial and Pell-type constructions for Stewart's question

Research note, 27 November 2026. This is a restriction on explicit constructions, not the pointwise upper bound in Stewart's conjecture.

[Stewart's 2008 paper, §4](https://uwaterloo.ca/pure-mathematics/sites/default/files/uploads/documents/aa133-2-01.pdf) asks for infinitely many square–cube–fifth-power triples in \([N,N+\sqrt N]\), and conjectures that no sufficiently large such interval has four distinct perfect powers. The [existing construction](FactorStewartSquareCubeFifth.md) gives the three-power existence result, and the [endpoint supplement](FactorStewartAllStartsEndpoint.md) reaches length \(\sqrt{N/5}\). Here we prove:

1. **Four fixed-source powers are impossible.** Fixed polynomials for the integer bases, or balanced reciprocal-conjugate Laurent polynomials as used with a quadratic Pell unit, cannot give four distinct perfect-power values in square-root intervals at an unbounded sequence of parameters. In either model, any such unbounded family of three fixed-source values must have prime exponent types \(2,3,5\). In particular, looking for a fixed polynomial or reciprocal Pell source for a third nonsquare power cannot work within one common fixed-parameter model, even if the square is later supplied separately.
2. **The rationally rescaled binomial construction is exhausted.** For the binomial truncation used in the existing solution, allow arbitrary positive rational scalings, arbitrary rational parameters, and even choices varying from one example to the next. For an unbounded sequence of positive integer bases whose cube and fifth power lie together in square-root intervals, all sufficiently large pairs are exactly the original two-sign pairs. Consequently this ansatz gives no such pairs in intervals of length \(\lambda\sqrt N\) for any fixed \(\lambda<1/\sqrt5\).
3. **One natural Pell modification degenerates.** Replacing the sparse binomial pair by the lowest opposite-frequency Pell mode with odd Laurent exponents produces only an identity at the requisite scale, not two distinct powers.

## 1. Fixed-source obstruction by a derivative identity

Let \(A,B\) be nonconstant polynomials over a characteristic-zero subfield of \(\mathbb R\), and suppose
\[
 \deg A^p=\deg B^q=D,\qquad d=\deg(A^p-B^q)<D,\qquad A^p-B^q\ne0 .
\]
Both assumptions on degree and the equality of leading coefficients are forced if the positive values of the two powers at arbitrarily large positive parameters are within a sublinear power of their size. For \(m=\deg A=D/p\) and \(n=\deg B=D/q\),
\[
 \left(\frac{A^p}{B^q}\right)'=A^{p-1}B^{-q-1}(pA'B-qAB').
\]
At infinity the ratio is \(1+c t^{d-D}+O(t^{d-D-1})\), \(c\ne0\), so its derivative has leading exponent \(d-D-1\). The Laurent leading exponent of the prefactor is \(-(m+n)\). Thus the nonzero polynomial \(pA'B-qAB'\) has degree \(d-D+m+n-1\), and
\[
                  d\ge D(1-1/p-1/q)+1.
 \tag{1}
\]
There is no coprimality hypothesis. This is the familiar Davenport degree obstruction ([Beukers–Stewart, *Neighboring powers*, §§1, 7](https://uwaterloo.ca/pure-mathematics/sites/default/files/uploads/documents/1-s2.0-s0022314x09002534-main.pdf)); the derivative calculation records the nonprimitive case directly. For \(p,q=3,5\), it shows that \(D\ge30\) at square-root scale and \(D\ge45\) for a strict improvement in the degree exponent. If the square also comes from a fixed polynomial then \(D\) is even, so the first degree not excluded for strict improvement is \(60\). At \(D=30,d=15\) the displayed derivative numerator is a nonzero constant.

The polynomial obstruction also applies to fixed rational functions over \(\mathbb Q\) evaluated at unbounded positive integer parameters at which the bases are integers. Indeed, divide each rational function into its polynomial part, with coefficients of fixed common denominator \(M\), and a proper remainder tending to zero. For large integer parameters, the polynomial value lies on \((1/M)\mathbb Z\), and an error of magnitude \(<1/M\) cannot make it an integer unless the error is zero. Infinitely many such points force the proper remainder to vanish identically.

For the Pell variant let \(K/\mathbb Q\) be real quadratic with conjugation \(a\mapsto\bar a\). Suppose the bases are fixed Laurent polynomials \(A,B\in K[t,t^{-1}]\) satisfying \(\bar A(t)=A(\kappa/t)\), \(\bar B(t)=B(\kappa/t)\) for the same fixed \(\kappa\in\mathbb Q^\times\). Such polynomials have symmetric extreme exponents, and this symmetry is inherited by powers and their difference. Their integer values may for example be obtained along suitable quadratic-unit sequences; integrality is all we assume at the parameters considered. Let \(D\) be the common largest exponent of the two powers, and \(d<D\) the largest exponent of the nonzero difference. The extreme exponents at zero are \(-D,-d\), respectively. Taking \(t\,d/dt\) in the same ratio identity now gives a nonzero Laurent polynomial \(W=p(tA')B-qA(tB')\) with largest exponent \(d-D+m+n\) and smallest exponent \(D-d-m-n\), where \(m=D/p,n=D/q\). The nonzero powers \(d-D\) and \(D-d\) ensure that neither derivative-leading term vanishes. Hence
\[
                    d\ge D(1-1/p-1/q).
 \tag{2}
\]
In particular, the loss of \(1\) in this two-pole version is immaterial for what follows.

For any positive integer \(p\ge2\), two different \(p\)-th powers cannot be in \([N,N+\sqrt N]\): the gap above \(x^p\ge N\) is at least \(p x^{p-1}\ge2\sqrt N\). For any perfect-power representation choose a prime divisor of its exponent and absorb the complementary power into its base. This preserves either class of fixed-source expressions. Distinct integer values in the interval must have distinct chosen exponents. If one chosen odd prime is at least 7 and another is at least 3, then \(1/p+1/q\le1/3+1/7<1/2\); both (1) and (2) give a gap with exponent strictly larger than \(D/2\). This contradicts a square-root interval at unbounded parameters, since its length is at most the square root of either of the two values. Thus there can be at most two distinct odd-prime exponent sources, and the only possible pair of them is \(3,5\). This proves assertion 1.

## 2. Exact arithmetic classification of the sparse binomial ansatz

The \((3,5)\) case of the binomial truncation in [Beukers–Stewart, Lemma 3.3](https://uwaterloo.ca/pure-mathematics/sites/default/files/uploads/documents/1-s2.0-s0022314x09002534-main.pdf) has rescaled bases
\[
 U=a^3(x^6+b x),\qquad
 V=a^5(x^{10}+\tfrac53 b x^5+\tfrac59 b^2),
 \quad a>0,\ x\ne0,\ b\ne0,\quad a,x,b\in\mathbb Q.
 \tag{3}
\]
This includes rational affine changes of parameter by simply allowing arbitrary \(x\). Use
\(s=a x^2>0,\ t=a^3 b x,\ z=t^2/s=a^5b^2>0\). In fact we can work in the possibly larger class of arbitrary positive rational \(s\) and nonzero rational \(t\):
\[
             U=s^3+t,\qquad
             V=s^5+\tfrac53 t s^2+\tfrac59\,t^2/s .
 \tag{4}
\]
Suppose \(U,V\) are positive integers. Substitution of \(t=U-s^3\) gives
\[
                      9V=-s^5+5Us^2+5U^2/s .
 \tag{5}
\]
If a prime \(\ell\) occurs in the denominator of \(s\), with \(v_\ell(s)=-h<0\), then the three terms on the right have valuations \(-5h,\ \ge-2h,\ \ge h\), respectively. The unique lowest valuation is negative, impossible for \(9V\). Thus \(s\) is an integer, and so is \(t\).

From \(3V=3s^5+5ts^2+(5/3)z\) it follows that \((5/3)z\) is an integer. Since \(5t^2=3s\cdot(5z/3)\), one has \(3\mid t\); then \((5/9)z\) is an integer as well by (4). Therefore
\[
                    z=9h/5\quad(h\in\mathbb N).
 \tag{6}
\]
More explicitly, put \(t=3b_0\); all rational solutions of (4) with the stated integrality are obtained by \(s=5b_0^2/h\in\mathbb N\) when the resulting \(U,V\) are positive. Conversely these choices make both bases integral. For a fixed \(z=9h/5\), as \(s\to\infty\), the normalized gap converges to \(h^{3/2}/\sqrt5\), as we now check uniformly enough to handle variable \(h\).

Let \(w=t/s^3\), so that \(U>0\) gives \(w>-1\). Direct expansion gives the exact relation
\[
 \frac{|V^3-U^5|}{U^{5/2}}
   = z^{3/2}\frac{135+405w+396w^2+125w^3}{729(1+w)^{5/2}}.
 \tag{7}
\]
To see positivity of the numerator throughout this domain, the third derivative of \((1+w)^{5/3}\) is strictly negative for \(w>-1\). Hence its degree-two Taylor polynomial at zero minus the function has the sign of \(w^3\) for \(w\ne0\). Cubing each quantity preserves its order. This gives positivity of the factor multiplying \(w^3\) in the difference of the cubes. At \(w=0\) the numerator is 135. The factor of \(z^{3/2}\) in (7) is continuous and positive, tends to \(+\infty\) at both ends \(w\downarrow-1\) and \(w\to+\infty\), and thus has a positive absolute lower bound.

If a pair from (4) is in \([N,N+\sqrt N]\), (7) is at most \(\sqrt N/U^{5/2}\le1\). It follows that \(z\) is bounded by an absolute constant. Along any unbounded sequence of such pairs, \(U\to\infty\) as \(N\to\infty\), so \(s\to\infty\) by \(t^2=zs\). In particular \(w=O(s^{-5/2})\to0\) uniformly. As the possible \(h\) belong to a bounded finite set by (6), the limit of (7) on each \(h\) is
\[
                          \frac{h^{3/2}}{\sqrt5}.
\]
For every \(h\ge2\) this exceeds \(1\), excluding all such \(h\) for sufficiently large \(N\). When \(h=1\), \(s=5b_0^2,\ t=3b_0\), giving exactly
\[
              U=125b_0^6+3b_0,\qquad
              V=3125b_0^{10}+125b_0^5+1 ,
\]
the existing pairs with both signs of \(b_0\). Their limiting separation is \(1/\sqrt5\), so no fixed smaller coefficient is possible anywhere in (3) or (4) at unbounded scales. This proves assertion 2 without assuming that the rational coefficients or their denominators are fixed.

## 3. A low-harmonic Pell modification cannot improve the situation

It is natural to try to add the missing lower binomial terms through reciprocal-conjugate Laurent coefficients. Here is one exact obstruction in that direction. Let \(d_0\in\mathbb Q^\times\), \(a,u,v\in K\), and take
\[
 \begin{aligned}
 A(T)&=T^3+aT+d_0\bar a\,T^{-1}+d_0^3 T^{-3},\\
 B(T)&=T^5+uT^3+vT+d_0\bar v\,T^{-1}
                  +d_0^3\bar u\,T^{-3}+d_0^5T^{-5}.
 \end{aligned}
\]
Both satisfy reciprocal conjugation with \(\kappa=d_0\). If \(B^3-A^5=O(T^{15/2})\) at positive infinity, its highest Laurent exponent is at most 7 since only odd exponents occur. The leading term of \(A\) is \(T^3\), so \(B-A^{5/3}=O(T^{-3})\), by factoring the difference of the cubes. The coefficients of \(T^3,T,T^{-1}\) in \(A^{5/3}\) must therefore match those of \(B\), giving
\[
 u=\tfrac53 a,\qquad v=\tfrac53 d_0\bar a+\tfrac59 a^2,\qquad
 27d_0^3+18d_0a\bar a-a^3=27d_0^2a+9d_0\bar a^2 .
\]
If \(a=x+y\sqrt{\Delta}\) with \(x,y\in\mathbb Q,\ \Delta>0\) a rational nonsquare and \(y\ne0\), the irrational part of the last equality gives
\[
                     \Delta y^2=-3(x-3d_0)^2,
\]
a contradiction. For \(a\in\mathbb Q\) the same equality is \((a-3d_0)^3=0\). Then \(A=(T+d_0/T)^3\), \(B=(T+d_0/T)^5\) by the determined coefficients, and the powers coincide. Thus no distinct close pair is obtained in this low-harmonic sector; this does not classify general reciprocal Laurent pairs.

## Scope and verification

The derivative bounds are algebraic degree statements and do not apply when the integer bases are selected by nonpolynomial rounding, when the functions vary between parameters, or when an accidental fourth perfect power enters the interval. The integrality classification is uniform only for the specified binomial ansatz. In particular, it does not prove that \(1/\sqrt5\) is globally optimal or replace Stewart's pointwise integer conjecture. The latter is conditional on \(abc\) in Stewart's discussion and is not asserted here unconditionally.

[verify_factor_stewart_construction_obstructions.js](verify_factor_stewart_construction_obstructions.js) uses exact arithmetic to test the rational scaling deductions, binomial-square-root comparisons on both signs, the derivative-degree identity in sample pairs, and the low-harmonic Pell coefficient identities.
