# Sharp Smale mean-value bound for real sextics at real base points

**Theorem.** For every real-coefficient polynomial \(P\) of degree six, and every real \(x\) with \(P'(x)\ne0\), some critical point \(c\) (not necessarily real) satisfies
\[
 \left|\frac{P(c)-P(x)}{(c-x)P'(x)}\right|\le\frac56.
\]
The minimum over the critical points is \(5/6\) if and only if
\[
 P(x+h)=P(x)+P'(x)h+b h^6
\]
for a real \(b\ne0\). The proof below uses finite exact arithmetic on domains of at most four real parameters. It does not give the bound at nonreal base points or for unrestricted complex sextics.

## 1. Normalize and enumerate four compact domains

Translate the real base point to zero and replace the image by its affine normalization, so the polynomial \(f\) has \(f(0)=0\) and \(f'(0)=1\). Let \(w_0,\ldots,w_4\) be the reciprocals of the five critical points, counted with multiplicity; none is zero in degree six, and the critical points are nonzero since \(f'(0)=1\). We have
\[
 f'(z)=\prod_{j=0}^4(1-w_jz).
\tag{1}
\]
A transformation \(f(z)\mapsto f(sz)/s\) with real \(s\ne0\) multiplies the \(w_j\) by \(s\), without changing the secant ratios. We normalize \(\max_j|w_j|=1\) and may additionally reflect all \(w_j\).

The multiset is invariant under conjugation. If all five reciprocals are real, the \(2/3\) bound of [Hinkkanen and Kayumov](https://doi.org/10.1007/s00365-009-9079-6) is strict relative to \(5/6\). In addition, the [separate three-real-critical estimate](FactorSmaleSexticThreeRealCriticalPoints.md) gives a strict bound below \(81/100\) when at least three of the five critical points are real (counted with multiplicity). Otherwise there are one or two conjugate pairs, and a greatest-modulus reciprocal may be chosen real or nonreal. These four cases give the following closed domains for the certificate, listed with their executable shard numbers.

| Shard | Form of the five reciprocals | Parameters |
| --- | --- | --- |
| 0 | \(1,r,s,w,\overline w\) | \(r,s\in[-1,1]\), \(r\le s\), \(w\) in the closed upper unit half-disk |
| 1 | \(a,\overline a,r,s,t\) | \(r,s,t\in[-1,1]\), \(r\le s\le t\), \(a\) on the first-quadrant unit arc |
| 2 | \(1,w,\overline w,v,\overline v\) | \(w,v\) in the closed upper unit half-disk, \(\Re w\le\Re v\) |
| 3 | \(a,\overline a,w,\overline w,r\) | \(a\) on the first-quadrant unit arc, \(w\) in the closed upper unit half-disk, \(r\in[-1,1]\) |

In the real-anchor cases choose the overall sign so that its value is \(1\). In the other cases reflect if necessary to put the representative of the unit pair on the closed first-quadrant arc; the representative can be either member of the pair. This uses no rotation by a nonreal scalar. The arc is parameterized by \(a=(1-t^2+2it)/(1+t^2)\), \(0\le t\le1\), whose Euclidean speed is \(2/(1+t^2)\le2\). Boundary values with zero reciprocals, real limits of nonreal pairs, or multiple critical points need not be deleted from the boxes.

## 2. Strict certificates and the local region

For \(w_j\ne0\), put \(h_j=f(1/w_j)/(1/w_j)\). Termwise integration of \(f'\) along the segment from zero to \(1/w_j\) gives
\[
 G_j:=60w_j^4 h_j
 =30w_j^4-10e_1^{(j)}w_j^3+5e_2^{(j)}w_j^2-3e_3^{(j)}w_j+2e_4^{(j)},
\tag{2}
\]
where \(e_k^{(j)}\) is the elementary symmetric polynomial in the other four reciprocals. This follows from the integral of \((1-u)u^k\), equal to \(1/((k+1)(k+2))\) on \([0,1]\). Conjugate reciprocals have conjugate ratios, so one may check only one member per pair. A box is excluded strictly whenever an upper bound on \(|G_j|\) is less than \(50\) times a positive lower bound on \(|w_j|^4\).

The remaining two tests use the [local sextic estimate](FactorSmaleSexticLocalExclusion.md). Write \(E_k\) for the symmetric polynomials in all five reciprocals. If the box has positive lower bound \(l\) for \(|E_5|=\prod|w_j|\), take a fifth root \(s^5=E_5^{-1}\) and use the normalization of that estimate. In its notation
\[
 A=\sum_{k=1}^4 |E_k||E_5|^{-k/5}
 \le \frac{\sum_{k=1}^4|E_k|}{|E_5|},
\tag{3}
\]
since \(|E_5|\le1\) on the four domains. Thus if \(7\sum_{k=1}^4 \operatorname{upper}|E_k|\le l\), every point of the box belongs to the proven local region. There equality forces all the intermediate coefficients to vanish.

For the additional strict product test, let \(R(v)\) denote the determinant polynomial in the local estimate. The determinant identity holds with multiplicity even outside the local region: over distinct roots it is the product \(\prod_j(1+\sum v_k c_j^k)\), and the general identity follows by continuity. In the present normalization it is \(\prod_j (6/5)h_j\). Substitute
\[
 v_k=\frac{5-k}{5(k+1)}(-1)^k E_k s^k,\qquad s^5=E_5^{-1}.
\]
In every nonconstant monomial \(v^\alpha\) of \(R\) the weight \(\sum k\alpha_k\) is a multiple of five, at most twenty, as can be verified by the companion local script. Hence with \(D=E_5^4\) the expression \(Q=D(R-1)\) is a polynomial in \(E_1,\ldots,E_5\). The checker verifies
\[
 2\Re(\overline D Q)+|Q|^2<0
\tag{4}
\]
when its interval enclosures make that possible and \(l>0\). This is \(|D+Q|<|D|\), and hence \(|R|<1\), which again gives a critical ratio strictly below \(5/6\). The list of rational monomials comes from `python3 verify_smale_sextic_local.py --emit-reciprocal-terms`. No equality condition on the five moduli, and no existence theorem for special extremizers, is used by this cover.

There is also a cheaper signed quadratic test. Write \(R_2=30(v_1v_4+v_2v_3)\). The explicit homogeneous bounds in the local estimate give \(|R-1-R_2|\le H(A)E\), with \(H(1/4)<7\): the terms are bounded by \(18/4+31/16+23/64+1/256+1/1024+1/4096<7\), using the rational constants there. Thus if \(A\le1/4\), \(0<E\le1/100\), and \(\Re R_2\le-10E\), then
\[
 |R|^2-1\le2(-10+7)E+(15+7)^2E^2\le-\frac{29}{25}E<0.
\]
This also excludes the box strictly. To certify those hypotheses without fifth roots, put
\[
 B=E_5,\qquad C=12E_1E_4+15E_2E_3,\qquad
 N=400|E_1|^2+100|E_2|^2+25|E_3|^2+4|E_4|^2.
\]
Then \(R_2=-C/(25B)\) and \(E\le N/(2500|B|^2)\) since \(|B|\le1\). The tests \(4\sum_{k=1}^4\operatorname{upper}|E_k|\le l\), \(\operatorname{upper}N\le25l^2\), and \(\operatorname{lower}\Re(C\overline B)>(\operatorname{upper}N)/10\) imply the hypotheses, including \(E>0\) from the last strict sign. This is a sufficient shortcut, not an additional assumption about the polynomial.

## 3. Exact interval cover

The companion JavaScript program splits the four closed parameter boxes at integer dyadic midpoints. Endpoints, centers and radii are initially stored as integer multiples of \(2^{-17}\). If a very small box is inconclusive it is converted exactly to scale \(2^{-20}\), preserving its endpoints. When the arc rational numerator times the scale is too large for a safe integer, the code performs that product and integer division with arbitrary-precision integers. An outside-disk test uses the exact minimum squared norm of the rectangular box. Arc centers use the rational stereographic formula; the speed bound gives the radius error \(2\,\Delta t\), with a further two units for center rounding. Real and ordinary complex box centers have their radii rounded outward. When a conjugate pair is included in full in an elementary symmetric function, the generating factors are grouped as \(1+2\Re(w)X+|w|^2 X^2\), with the two real coefficients independently enclosed.

For a Gaussian disk with center \(c\) and radius \(r\), a product of two such disks lies in the disk with center \(c_1c_2\) and radius at most \(|c_1|r_2+|c_2|r_1+r_1r_2\). The checker rounds that radius up and also covers the two real-coordinate rounding errors when rounding the new center. All square-root upper and lower bounds are determined by integer square comparisons; the numerical square root is used only as a seed for a checked integer operation. If a scale coefficient has a non-dyadic rational denominator, the quotient candidate is checked by exact multiplication, as is its required outward correction. The fixed-power-of-two operations are exact on the integer ranges in the code; products and sums outside them fail instead of being used as a certificate. (Geometric endpoint squares are automatically below \(2^{41}\) at either scale.)

A split is performed only after every attempted proof test is inconclusive. The two closed children retain their common midpoint. On primitive calls the only positive outcome is `PASS` with an empty stack; any unfinished stack or unit-resolution cell is not a proof. No search over actual root approximations is substituted for the cover. The four shard results follow from executing `node verify_smale_real_sextic.js Infinity j` with \(j=0,1,2,3\).

| Shard | Visited boxes | Order/disk | Strict direct ratio | Local theorem | Strict product | Max depth |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | 469065 | 11652 | 222881 | 0 | 0 | 31 |
| 1 | 1857059 | 20765 | 907765 | 0 | 0 | 31 |
| 2 | 32081835 | 81724 | 14570183 | 133863 | 1255148 | 51 |
| 3 | 49863227 | 84047 | 22231033 | 341253 | 2275281 | 53 |

Every shard returned `PASS` with zero pending boxes and no need to promote the precision. The arithmetic tables underlying the local and product tests can be checked independently via `python3 verify_smale_sextic_local.py`; the reciprocal monomial array uses its optional generator. Full replay is a finite computation over 84,271,186 boxes, not a short sample or a floating-point optimization.

## 4. Equality

Every covering exclusion other than the local filter is strict relative to \(5/6\). By the local theorem a retained equality polynomial has all \(b_k=0\) in its sextic-leading coefficient normalization, and hence all corresponding intermediate coefficients of \(P(x+h)\) vanish. Conversely if just the linear and sextic terms remain after subtracting \(P(x)\), the critical equation gives \(h^5=-P'(x)/(6b)\), and substitution gives every normalized ratio \(1-1/6=5/6\). This proves the classification.
