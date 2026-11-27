# Completing the length-six Salem classification below 1.01

Here the **length** of an integral polynomial is the sum of the absolute values of its coefficients, not its degree. A Salem polynomial is the monic minimal polynomial of a Salem number, possibly multiplied by any product of cyclotomic polynomials, with multiplicity. This is the convention of [McKee–Smyth, *Short Salem polynomials*](https://arxiv.org/abs/2605.19013).

**Theorem.** If a Salem polynomial has length six, its Salem root is strictly greater than \(101/100\). Consequently the twelve infinite families and the 126 sporadic polynomials in McKee–Smyth's Theorem 2 and Tables 2–3 are an **unconditional complete classification** of length-six Salem polynomials. In particular the least Salem number that admits such a polynomial is Lehmer's number. This is not a claim about all Salem numbers, all reciprocal polynomials, or the unrestricted Lehmer problem.

The new part is the exclusion at \(1<\tau\le101/100\). It combines a uniform cyclotomic bound for arbitrary degree with exact finite arithmetic through degree 649. There is no numerical test of closeness of a complex root to the unit circle. The published \(>1.01\) catalogue is used as a theorem, not repeated as a new search.

## 1. Normalization and the norm inequality

Write \(N\) for the polynomial degree, \(D\) for the degree of its Salem root \(\tau\), and \(\epsilon=1\) or \(-1\) for its reciprocity sign. The polynomial is
\[
 F(z)=z^N+\epsilon-z^{N-s}-\epsilon z^s-z^{N-t}-\epsilon z^t
 \quad (0<s\le t\le N/2),
 \tag{1}
\]
where \(N,s,t\) are integers. The labels in (1) are retained if exponents tie. In reciprocity, \(F(1)\le0\) follows from the positive signs at \(1\) of cyclotomic factors other than \(\Phi_1\) and the two exceptional Salem conjugates. The two outer coefficients are \(1\), and any positive interior coefficients would have total mass at least two (the middle coefficient, if present, is even by parity of length), forcing \(F(1)>0\). In antireciprocity the leading centered hyperbolic sine is larger in absolute value than either of the other two at \(\tau>1\); both smaller pairs must be subtracted. They have positive centered magnitudes \(B=N/2-s\) and \(C=N/2-t\). The equation \(\sinh(Au)=\sinh(Bu)+\sinh(Cu)\), with \(A=N/2\) and \(u=\log\tau>0\), implies \(A<B+C\), hence \(2(s+t)<N\). This stricter inequality is used throughout for \(\epsilon=-1\).

Also \(\gcd(N,s,t)=1\): otherwise (1) is a proper power substitution and has several roots outside the unit disk. By definition a Salem polynomial has only the one outside root, with multiplicity one.

The [earlier norm calculation](FactorShortSalemNormGap.md) gives, with \(\eta=3\sqrt3/4\),
\[
                 \eta^{D-2}\le1024\,\tau^{7N}. \tag{2}
\]
Here is the short argument. After centering the six terms, use \(x,y,z\) for their three signed pairs, so that \(x+y+z=0\) at a root. Put \(U=(x^2+y^2+z^2)/2\) and \(V=xyz\). On the real hexagon \(x,y,z\in[-2,2]\), \(0\le U\le4\), and
\[
        27V^2\le4U^3,\qquad |V|\le8-2U .
\]
The first bound is the discriminant of \(X^3-UX-V\); the second follows from its signs at \(\pm2\). On \([0,3]\) the maximum after multiplying the first bound by \((U-2)^2(U-3)^2\) is \(16/27\) for \(V^2(U-2)^2(U-3)^2\): its nonzero stationary points are \(1,18/7\). On \([3,4]\) the second bound gives \(2w(1-w^2)\), \(w=U-3\). Consequently \(|V(U-2)(U-3)|\le1/\eta\).

At unit conjugates, the three signed pairs are real in reciprocity. In antireciprocity they are imaginary, and multiplication by \(i\) changes \(U\) to \(-U\). Thus
\[
 Q=V(U-2)(U-3)\quad\text{or}\quad Q=V(U+2)(U+3),
\]
respectively, has modulus at most \(1/\eta\) on the unit conjugates. Its square is an integer Laurent polynomial in the original root, including when the centered exponents are half-integral: changing the choice of square root changes only the common sign of the three signed pairs. As \(\tau\) is an algebraic unit, \(Q^2\) is integral. At \(\tau\), the leading positive pair equals the sum of the two positive magnitudes of the other pairs, so \(U\le x^2\) and \(|V|\le x^3/4\). In reciprocity \(x\ge4\), \(U\ge3x^2/4\ge12\), and \(|Q|\le x^7/4\le32\tau^{7N/2}\); in antireciprocity \(0<x<\tau^{N/2}\) gives \(|Q|\le3\tau^{7N/2}\). In each case \(Q\) is nonzero there and its absolute value at \(\tau^{-1}\) is the same. Taking the absolute norm of \(Q^2\) gives (2).

If \(\tau\le101/100\), then (2) implies
\[
              D < \frac{27}{100}N+29, \tag{3}
\]
because \(\eta^{27}\) is strictly larger than each of \(1024\) and \((101/100)^{700}\). The exact integer comparisons are in the companion.

## 2. The ten directions give exact phase counts outside order 60

Let \(\xi\) be a root of unity of order \(m\), and \(q=m/\gcd(m,30)\). Group the six labeled terms of (1) when their exponent difference is a multiple of \(q\). By [Mann's theorem on vanishing sums](https://doi.org/10.1112/S0025579300005210) every irredundant vanishing sub-sum of at most six rational-signed powers has ratios of order dividing \(30\). Therefore, if the full sum vanishes, every group vanishes separately and contains at least two terms.

The formal centered exponent labels are \(\pm e_1,\pm e_2,\pm e_3\), evaluated on \((N,N-2s,N-2t)/2\). If the same-group differences span rank three, their signed congruences force \(q\) to divide each of \(N,N-2s,N-2t\). To see this, connect the types using the same-group equalities. A self-pair forces divisibility of its doubled coordinate by \(q\). A sign-inconsistent cycle forces the same, since the congruences between two types are modulo \(2q\). If a component had neither, one could assign a free nonzero signed value to it, contradicting rank three. Divisibility propagates along each component. The gcd of the three doubled coordinates divides \(2\gcd(N,s,t)=2\), giving \(m\mid60\).

For \(m\nmid60\) choose a nonzero normal to the span of the differences. Every attained level on the six signed formal vectors must occur at least twice. Either one coordinate is zero and the other two have equal absolute values, giving six directions with groups of sizes \(2,2,2\); or all three absolute values coincide and are nonzero, giving four directions with groups \(3,3\). A pair or triple cannot be split further without a singleton. Each listed phase system thus suffices, as well as being necessary, to make \(F(\xi)=0\). A root in two different directions would have a rank-three collection of same-group differences, so the ten direction sets are disjoint outside order dividing 60. All such roots are simple: apply Mann to the vanishing hypothetical derivative \(zF'(z)\), now with coefficient weights equal to the original exponents. A pair of opposite phases can still cancel only with equal exponents, and three phases forming an equilateral triple can do so only if all weights are equal. Equal occurrences have the same coefficient signs in (1) and could not have formed opposite or equilateral phases. A zero derivative coefficient at exponent zero does not affect the argument.

The phase equations are indexed by the following ten rows. A pair row lists the exponents \(a,b\) and prescribed signs of \(\xi^a,\xi^b\). A triple row lists the exponents and the signs multiplying \(\omega,\omega^2\), in either orientation, with \(\omega=e^{2\pi i/3}\). Complementing the labels gives the other groups automatically by reciprocity. The displayed expressions follow by comparing the labels containing \(z^N\), and then the self-pair where present. For example, self-pairing the outer terms and pairing \(z^{N-s}\) with \(z^t\) gives row 1 (zero-based numbering).

| \(i\) | Type | \(a,b\) | Signs |
|---:|:---:|:---|:---|
| 0 | pair | \(N,t-s\) | \(-\epsilon,-1\) |
| 1 | pair | \(N,N-s-t\) | \(-\epsilon,-\epsilon\) |
| 2 | pair | \(N-2s,t\) | \(-\epsilon,1\) |
| 3 | pair | \(N-2s,N-t\) | \(-\epsilon,\epsilon\) |
| 4 | pair | \(N-2t,s\) | \(-\epsilon,1\) |
| 5 | pair | \(N-2t,N-s\) | \(-\epsilon,\epsilon\) |
| 6 | triple | \(s,t\) | \(-1,-1\) |
| 7 | triple | \(s,N-t\) | \(-1,-\epsilon\) |
| 8 | triple | \(N-s,t\) | \(-\epsilon,-1\) |
| 9 | triple | \(N-s,N-t\) | \(-\epsilon,-\epsilon\) |

For a pair set \(g=\gcd(a,b)\), \(a'=a/g,b'=b/g\). A unique sign \(y\) satisfies the whole system on \(\xi^g=y\) if and only if its powers with exponents \(a',b'\) give the specified signs; at least one exponent is odd. For a triple one also needs \(a'+b'=0\bmod3\) with neither zero modulo 3, and then the two conjugate choices give two phases \(y\) of common order 3 or 6. Each compatible phase \(y\) contributes \(g\) unrestricted roots, of which \(g_0=\gcd(g,60)\) belong to \(\mu_{60}\) exactly when \(y^{60/g_0}=1\). The two triple choices are distinct. This gives the exact ten counts \(r_i\) of roots outside \(\mu_{60}\).

Every count \(r_i\le N/2\). For pairs, a gcd greater than \(N/2\) would require equal positive exponents if both are nonzero. The outer exponent \(N\) cannot equal its paired exponent; rows 2 and 4 have \(t,s\le N/2\), respectively; row 3 would use opposite signs at the same exponent; row 5 cannot have equal exponents. A zero exponent can occur only on a boundary where its prescribed sign is \(-1\), so it is impossible. In a triple, a gcd greater than \(N/4\) requires the coprime quotients \(1,2\), since the quotients lie in \(\{1,2,3\}\) and neither may be zero modulo 3. The two signs then conflict with squaring for reciprocity. For antireciprocity the exponents must have one lower and one upper term, so \(2s=N-t\) or \(2t=N-s\), contradicting \(2(s+t)<N\).

## 3. A uniform cyclotomic bound and the cutoff \(N<650\)

**Orders dividing 60.** For each \(m\mid60\), test \(F\) in the exact coefficient basis of \(\mathbb Q[z]/(\Phi_m)\), reducing exponents modulo \(m\). If it vanishes, the first logarithmic derivative \((z\,d/dz)F\) gives a homogeneous linear system in \(N,s,t\). A nonzero row of rank one is tested against the convex triangle of \((s/N,t/N)\); the faces respect \(s>0\) and the strict antireciprocal inequality. If there are two independent rows then the kernel, when nontrivial, has at most one primitive integral vector meeting the cone, and its residues can be tested. A root has multiplicity at most five by the Vandermonde matrix on the distinct supported exponents, using the first six logarithmic derivatives. The small exact checker loops through the primitive residue triples modulo 60 and upper-bounds the multiplicity contribution by adding \(\varphi(m)\) when \(F\) vanishes, and another \(4\varphi(m)\) when a repeated root is not excluded by this linear test. The maximum resulting bounds are **40** for reciprocity and **60** for antireciprocity.

**Pairs of directions.** Write \(X=(N,s,t)\) and \(L_i=(a_i,b_i)\) for the integral coefficient vectors in the phase table, so \(g_i=\gcd(a_i\cdot X,b_i\cdot X)\). For two different directions \(i,j\), the two rational row planes meet in the line generated by a primitive integral vector \(h\). Let \(m_i,m_j\) be the least positive integers that put \(m_i h,m_j h\) in the two integer row lattices. They are obtained by clearing denominators after a two-by-two solve. Then both gcds divide \(\operatorname{lcm}(m_i,m_j)h\cdot X\). Furthermore \(\gcd(g_i,g_j)\) divides the gcd \(d_{ij}\) of the three-by-three minors of the four coefficient rows: apply the adjugate identity to any three rows and use \(\gcd(N,s,t)=1\). When the shared linear value does not vanish, these two divisibilities give
\[
 r_i r_j \ \le\ c_{ij}N,\qquad
 c_{ij}=w_i w_j\,d_{ij}\operatorname{lcm}(m_i,m_j)
              \max_{\text{corners}}\big|h\cdot(1,s/N,t/N)\big|,
\]
where \(w_i=1\) for pairs and \(w_i=2\) for triples.

The two boundary cases \(s=t\) or \(2t=N\) have zero roots outside \(\mu_{60}\): in the table all gcds are at most two by primitivity, except tied triple exponents (incompatible cube phases) or zero pair exponents with sign \(-1\). For the strict cone, the companion computes all possible zero shared linear values. The only reciprocal cases are:
* \(N=2s+2t\) for two of rows \(1,2,4\). Each of the three rows on its own gives contradictory signs upon squaring the shorter phase.
* \(N=2s+t\) for rows \(2,7\), and \(N=s+2t\) for rows \(4,8\). In each case the pair row prescribes opposite signs at the same exponent.
* \(t=2s\) for rows \(3,6\); row 3 again prescribes opposite signs at the same exponent.

The last case is also the only antireciprocal possibility, with the same contradiction. These are all sign-plane intersections in the interiors of the normalized triangles; the exact checker uses the linear form's signs at the three corners. Thus the product bound is valid whenever both counts are positive.

In both signs, \(c_{ij}\le4\), every row sum is at most \(24\), and at each nonzero row breakpoint \(c\), the checker verifies \((c+\sum_j\min(c,c_{ij}))^2\le225c\). If \(r_i=r>0\) is the largest count, then \(\sum_j r_j\le r+\sum_{j\ne i}\min(r,c_{ij}N/r)\). On each piece between breakpoints \(r=\sqrt{c_{ij}N}\) this function is convex, so its maximum is at a breakpoint or an endpoint. The exact inequality at a breakpoint bounds it by \(15\sqrt N\); at \(r=N/2\), for \(N\ge16\), it is at most \(N/2+48\). This also covers the degeneracies mentioned above. Including orders dividing 60,
\[
              N-D\le60+\max(15\sqrt N,N/2+48)\qquad(N\ge16).
\]
By (3) a putative counterexample would need \(N-D>0.73N-29\). For \(N\ge650\), \(0.73N-89\) exceeds both \(15\sqrt N\) and \(N/2+48\), already at 650 and with larger slope thereafter. This proves \(N<650\).

## 4. Finite exact exclusion

By [Mossinghoff–Rhin–Wu, *Minimal Mahler Measures*](https://doi.org/10.1080/10586458.2008.10128872), a Salem number \(\tau\le1.01\) has \(D\ge56\). This is the only imported bounded-degree computation. In reciprocity the centered leading pair at \(\tau\) is at least four, so \(N\ge260\): at \(N=259\),
\[
 (101/100)^N+(100/101)^N<14
\]
by an integer power comparison, whereas the square of the leading pair at a root is at least \(16\). Smaller \(N\) cannot satisfy it either.

For each \(N=56,\ldots,649\) (or \(260,\ldots,649\) in reciprocity), the finite checker finds the greatest even \(d\ge56\) consistent with (2) at \(\tau=101/100\). It compares \((27/16)^{(d-2)/2}\) directly to \(1024(101/100)^{7N}\) by integer powers. If such a \(d\) exists it examines every permitted primitive \(s,t\) in (1). It computes the exact sum outside \(\mu_{60}\) from the ten phase systems. Only if this plus 60 is at least \(N-d\) does it determine the **actual** remaining cyclotomic multiplicities, now by the full sequence of logarithmic derivatives modulo \(\Phi_m\).

| Sign | Primitive triples examined | Could supply \(N-d\) using the bound 60 | Could do so with exact multiplicities |
|:---|---:|---:|---:|
| Reciprocal | 8,908,829 | 410 | 0 |
| Antireciprocal | 4,708,172 | 16,382 | 0 |

There is no candidate left to test for irreducibility or to isolate any root. As an independent control, the checker confirms all its cyclotomic counts on small cases by literal long division through all possible cyclotomic orders, using \(\varphi(m)^2\ge m/2\). The full-degree loop does not rely on that control or on input coefficient tables.

## 5. The published list and its least entry

McKee–Smyth already prove completeness above the cutoff in Theorem 2. Combining this with §4 makes their full list unconditional. For the least entry, an additional exact check reads the integer parameters of their 126 sporadic polynomials and twelve family starts. Let \(L\) be the degree-ten Lehmer polynomial and \(\lambda\) its root outside the unit disk. The checker verifies \(L(1177/1000)>0\), hence \(\lambda<1177/1000\). Each of the sporadic polynomials and family starts is either divisible by \(L\), or gives a negative value at \(1177/1000\), so its Salem root is strictly larger than that rational number. The sign test is valid because a Salem polynomial is negative on \((1,\tau)\) and positive to the right of \(\tau\). For a family \(z^jP(z)+\epsilon P^*(z)\), \(P(\lambda)<0\): its base polynomial is increasing for \(z\ge1\) and negative at the rational point just used. The family value at \(\lambda\) therefore strictly decreases with \(j\). The initial entry bounds the entire family from below. In the exact published data, thirteen sporadic entries and two initial family entries give equality.

### Reproduction

Run `python3 verify_length_six_salem_cutoff.py` (without `-O`) and `node verify_length_six_salem_classification.js`. Both use only their standard libraries. The two routines check respectively the universal cutoff and the finite exclusion. The latter also checks the exact least entries of the published catalogue; it does not regenerate the catalogue for \(\tau>1.01\). The earlier norm note's \(N<7200\) result did not exhaust its remaining candidates. The new phase counts and pair-lattice divisibilities are what make the exact exclusion short.
