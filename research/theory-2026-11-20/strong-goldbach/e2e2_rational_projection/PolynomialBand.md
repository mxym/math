# Deleting a polynomial rational band in the true balanced semiprime covariance

Keep \(R,\mathcal V,\lambda_N,g,A,U,V,T,S,N=x,L\) and the genuine disjoint prime-label intervals of [the companion same-quotient theorem](Proof.md). In particular the two short prime labels have size \(x^{.4875}\), the opposite prime slots have size \(x^{.5125}\), and the short prime label masks may be arbitrary. This is a fixed-even-target theorem about part of the centered covariance. It is not an asymptotic for \(R\) and does not establish a representation by two semiprimes.

On each line \(t=t_0+vj,\ s=s_0-uj\), intersect \(t,s\) physical grid bins of length \(Z=x^{.5105}\), clipped by the original windows. Retain their actual common cells \(C\) with \(q_C=\#C\ge x^{.02295}\). Put \(H=x^{.0114}\), and, for any fixed \(D>0\), use the common orthogonal projector \(\mathcal Q_C\) onto the span of the reduced rational modes \(j\mapsto e(kj/h)\) with either
\[
h\le L^D,\qquad\text{or}\qquad
x^{.001}\le h\le H,\quad (h,N)\le h^{.01}.
\tag{1}
\]
The \(0/1\) mode is included. Uniformly for the actual windows and label masks,
\[
R=\mathfrak S(N)\mathcal V+
 \sum_{u,v}\log u\log v\sum_C
  \left\langle (1-\mathcal Q_C)A(t_0+v\,\cdot),
                 (1-\mathcal Q_C)A(s_0-u\,\cdot)\right\rangle_{\ell^2(C)}
 +o(x\mathfrak S(N)).
\tag{2}
\]
The **entire signed contribution** of the second band of (1) is \(O(x^{1-c_0})\) for an absolute \(c_0>0\); its individual coefficients are not claimed small. This signed statement uses the fixed-\(N\) phase, not a separate equidistribution statement for each long leg. The band omits negligibly many of the primitive rational modes counted by dimension up to \(H\), but its full dimension is \(O(x^{.0228})\), smaller than the actual cell lengths. There is no bound here on the surviving covariance.

## 1. Cells, joint orthogonalization, and the two large moduli

The geometric/mixed evaluation (10) of the companion is independent of grid scale. In the new grid each fixed \((u,v)\) has \(O(T/Z+S/Z+1)\) cells. Each \(t\)-bin meets only \(O(1)\) \(s\)-bins on a given physical line, because \(ds/dt=-u/v\asymp-1\). Dropping all the small cells, before any projection, changes the weighted centered sum by at most
\[
 O(UV(T/Z+1)x^{.02295}L^4)=O(x^{1-.00005}L^4).
\tag{3}
\]
For each remaining cell the physical progression interval \(J_t\) may be taken half-open of exact length \(v q_C\) (one unit lattice step after the largest included point). It lies in the \(O(V)\)-padded \(t\)-bin; the analogous \(J_s\), increasing in the physical variable despite decreasing in \(j\), has length \(u q_C\) in an \(O(U)\)-padded \(s\)-bin. Possible integer endpoint conventions affect the continuous lengths by \(O(1)\) and can equivalently be fixed exactly using half-open intervals.

The combined mode set of (1), including low-to-high pairs, has circle separation \(\gg H^{-2}\) for large \(x\). For the unit \(\ell^2(C)\) vectors \(q_C^{-1/2}e(kj/h)\), the Gram off-diagonal entries are \(O(1/(q_C\|\theta-\theta'\|))\). In the sorted list of distances from any one mode, the \(r\)-th distinct mode has distance \(\gg rH^{-2}\) (up to two directions). The sum along the row is therefore \(O(H^2\log x/q_C)\). Thus the Gram matrices are \(I+O_{\rm op}(x^{-.00015}L)\) and the sum of the paired mode coefficients equals the projection inner product up to \(O(x^{1-.00015}L^5)\) on summing the cells: the total weighted physical \(A\)-norm squared on either side is \(O(xL^4)\). No independent orthogonalization on the two legs is used.

For a fixed \(h\le H\), expand the actual \(t\)-array in residue classes \(a=N\bar u\bmod v\), \(b\bmod h\) before forming the Fourier coefficient. Keep the principal and nonprincipal multiplicative characters **modulo the large short-label prime \(v\)** separate. The latter have the bound (13) of the companion, hence their maximal squared error, summed over \(v,a,b\) in a padded bin, is \(O((ZV+Z^2/V)L^{C_1})\). This statement is independent of \(h\), because \(b\bmod h\) enters only in disjoint supports of the large-sieve input. It applies to \(\lambda_N\) and \(g\) separately with \(\|F\|_\infty\ll L\). For each \(a\) there are \(O(1)\) possible \(u\)'s in the actual short-label range at fixed \(v\). Additive Parseval in \(b\) costs \(h/q_C\), not \(h/L^B\) or a relative error against a smaller count. Thus the total error energy in the actual common mode coefficients, including the true short-log weights, is
\[
 \ll L^{C_2}\frac{H^2}{x^{.02295}}(TV+TZ/V)
 \ll x^{1-.00015}L^{C_2}.
\tag{4}
\]
The reflected orientation interchanges \(u,v\) and uses the same argument. Cauchy against the \(O(xL^4)\) energy of the original mode coefficients makes (4) negligible in their paired products. Small mode denominators \(h\le L^D\) can now be replaced by the companion's local means (14). The principal short Siegel–Walfisz error is relative to \(|J_t|\) or \(|J_s|\) here, since each is \(\gg x^{.51045}\), and the energy is \(O_A(xL^{-A})\) after the log-sized \(h\)-sum. The complete numerator calculation (16)–(17) of the companion gives \(o(x\mathfrak S(N))\) on that band.

## 2. The short-modulus character matrix in the polynomial band

Since \(\log W=O(L/\sqrt{\log L})\), no \(h\ge x^{.001}\) divides \(W\) for large \(x\). For the \(g\)-array, after taking the principal large-\(v\) character, the unrestricted \(h\)-class mean is the periodic function \(G_{\gcd(h,W)}\) in (11) of the companion, so its primitive \(k/h\) Fourier coefficient is zero. Opening \(g\) gives floor error \(O((W/\varphi(W))\tau(W))=x^{o(1)}\) in each unrestricted class; removing multiples of \(v\) costs \(O((Z/V+1)W/\varphi(W))\). Divide by \(\varphi(v)\) as required for the principal large-\(v\) character. Summed over \(C,h,k\), the squared error is
\[
 \ll L^{O(1)}\frac{T}{Z}\frac{H^3}{x^{.02295}}
        \left(x^{o(1)}+O(Z/V)\right)^2,
\tag{5}
\]
where \(UV/\varphi(v)^2\ll1\) and Parseval in \(b\) was used. The exponent in (5) is at most \(.002+.0342-.02295+2(.023)+o(1)<.06\). Thus all remaining \(g\) terms in this band are negligible in the paired product. There is no direct per-cell floor estimate for the nonprincipal large-\(v\) characters; those were treated by (4).

Write \(S_t(\chi_f;J_t)=\sum_{n\in J_t}\lambda_N(n)\chi_f(n)\), with analogous notation for \(s\). Every true long prime is larger than \(h\) and than the opposite short-label prime, so no unit correction for divisors of either modulus arises in the prime arrays. Let \(\chi\bmod h\) be induced by the primitive \(\chi_f\), and write
\(\tau_h(\xi)=\sum_{a(h)^*}\xi(a)e(a/h)\).
Using the expansion of \(e(-k\bar v n/h)\) in multiplicative characters on the unit group modulo \(h\), the large-\(v\) principal part of the normalized \(t\)-coefficient is
\[
 e(k\bar v t_0/h)\sum_{\chi\bmod h}\frac{\chi(k)}{\sqrt{\varphi(h)}}\,z_t(\chi),
 \qquad
 z_t(\chi)=
 \frac{\chi(-\bar v)\tau_h(\bar\chi)}{\sqrt{\varphi(h)}\,\varphi(v)\sqrt{q_C}}\,
       S_t(\chi_f;J_t).
\tag{6}
\]
For \(s\) the phase is \(e(-k\bar u s_0/h)\), the factor is \(\chi(\bar u)\), and the normalizing \(\varphi(v)\) is \(\varphi(u)\). The endpoints, phases, and moments in (6) are those of the literal common \(C\); no independence or matching between different physical intervals is assumed. In the complete numerator pairing, the diagonal multiplier left between the two unitary character transforms is \(e(k\overline{uv}N/h)\). The paired matrix in character variables is unitary, and each entry is bounded in modulus by
\[
 \frac1{\varphi(h)}
   \left|\sum_{k(h)^*}\xi(k)e(k\overline{uv}N/h)\right|
 \ll x^{o(1)}h^{-.495},
\tag{7}
\]
where \(\xi\) is a product of two characters and the last bound uses \((N,h)\le h^{.01}\).

Here is the Gauss-sum justification, including nonsquarefree \(h\) and target-nonunit frequency. If \(\xi\bmod h\) has inducing conductor \(f\), write \(h=f b\). Expand the extra unit restriction by \(\sum_{d\mid(n,h),\,(d,f)=1}\mu(d)\). In each term \(n=dm\) with \((d,f)=1\), summing over a full period of length \(h/d\) gives zero unless \(h/(df)\mid a\) for additive numerator \(a\). When nonzero its modulus is bounded by \((h/(df))\sqrt f\), using the primitive Gauss sum after summing the lifts. Putting \(r=h/(df)\), one has \(r\mid h/f\) and \(r\mid a\), hence \(r\sqrt f\le\sqrt{h(a,h)}\). There are at most \(\tau(h)\) terms. This proves (7) by the subpower divisor bound and \((\overline{uv}N,h)=(N,h)\). In addition for unit additive numerator there is at most the single term \(d=b\); thus
\[
 |\tau_h(\bar\chi)|^2\le f
 \quad\text{and}\quad
 \sum_{\substack{h\le 2d_0\\ f\mid h}}\frac f{\varphi(h)}
   \ll L\,\frac f{\varphi(f)}
 \qquad(f\le 2d_0\le 2H).
\tag{8}
\]
For the last inequality use \(\varphi(fb)\ge\varphi(f)\varphi(b)\) and the elementary harmonic mean of \(1/\varphi(b)\). These formulas also cover the principal character via \(f=1\).

## 3. Good and rare character vectors, uniformly on every actual interval

On a dyadic block \(d_0<h\le 2d_0\) put \(d_0=x^\nu\). Truncate the block to the exact band (1) if necessary. Then \(\nu\in[.001-O(1/L),.0114]\). Set
\[
 Y=x^{.0035+\nu},\qquad
 \delta=\frac{.006+2\nu}{.5125}.
\tag{9}
\]
A primitive nonprincipal conductor \(f\le 2d_0\) is called bad, more precisely its primitive character is bad, if it has a nontrivial zero \(\beta\ge1-\delta,\ |\gamma|\le Y\). Count the \(f=1\) principal as bad separately. The classical hybrid density estimate in the near-one range of Montgomery, Theorem 12.2, (12.14), in the usual Montgomery–Huxley formulation [as recorded in Koukoulopoulos, (1.2) and immediately below](https://arxiv.org/pdf/1405.6592#page=2), gives at most
\[
 1+x^{b(\nu)+o(1)},\qquad
 b(\nu)=2.41(3\nu+.0035)(.006+2\nu)/.5125,
\tag{10}
\]
primitive bad characters. Indeed this estimate counts zeros, with multiplicity, over all primitive \(f\le 2d_0\) at height \(Y\); here \(1-\delta>.94>5/6\). The density estimate is \((Q^2Y)^{(12/5+\varepsilon)\delta}\) times fixed logarithmic powers, and \(2.41=12/5+.01\) suffices. Do not count induced bad characters as if they were primitive in that estimate. At each individual \(h\), a primitive character with \(f\mid h\) induces at most one character, so (10) bounds the number of bad coordinates at a given \(h\) without alteration.

For other nonprincipal primitive characters, take the difference of [Koukoulopoulos, *The Distribution of Prime Numbers*, Theorem 11.3, (11.5)](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf#page=125) at the two endpoints of any \(J\) in a padded bin. The formula uses \((X^\rho-1)/\rho\), so the endpoint difference is exactly \(\int_J t^{\rho-1}dt\), even for a zero very near the origin. There is no pole for these nonprincipal primitive characters. The formula at \(Y\le X\) has endpoint error \(O(TL^2/Y)\); integer endpoints with half weights, if used, cost \(O(L)\) each, already absorbed. The uniform \(O(Y\log(fY))\) zero count and \(\Re\rho\le1-\delta\) give
\[
 |S_t(\chi_f;J)|\ll L^{O(1)}\bigl(Z\,Y x^{-.5125\delta}+x^{.5125}/Y+x^{.25625}\bigr)
       \ll Z x^{-\nu-.0015} L^{O(1)} .
\tag{11}
\]
Proper prime powers cost \(O(x^{.25625}L^2)\) by ignoring interval localization; excluding the target-dividing true primes costs \(O(L)\). The first term gains \(\nu+.0025\) relative to \(Z\), the second gains \(\nu+.0015\), and the last is polynomially smaller. This proof is uniform over all actual bin endpoints, not in measure over a moving interval. It likewise holds on the \(s\) side. Any exceptional nontrivial zero in the near-one region is in the bad class.

Including all characters, the maximal primitive large sieve in each padded bin gives
\[
 \sum_{f\le 2d_0}\frac f{\varphi(f)}\sum_{\chi_f\ {\rm primitive}}
   \max_{J\subset I}|S_t(\chi_f;J)|^2
 \ll (Z+d_0^2)Z L^{O(1)};
\tag{12}
\]
include \(f=1\), or bound it trivially by \(Z^2 L^2\). For the maximum use the dyadic subdivision as in (13) of the companion. Combine (12) with (8). For each physical bin and denominator, at most \(O(UV)\) cells have a possible maximizing moment, and their short stride and actual \(q_C\) normalization in (6) give \(O(UV/(V^2 x^{.02295}))\). Thus, with all logarithmic short-prime weights included, the total squared norms in any dyadic \(h\)-block are
\[
 E_t,E_s\ll L^{O(1)}\frac{T}{Zx^{.02295}}(Z+d_0^2) Z
             \ll x^{1+.00005} L^{O(1)}.
\tag{13}
\]
For just the good coordinates, use (11) in place of (12); by (8) the effective coordinate count is \(O(d_0^2 L^{O(1)})\), reaching
\[
 E_{t,\mathrm{good}},E_{s,\mathrm{good}}
             \ll x^{1-.00295} L^{O(1)} .
\tag{14}
\]
Equations (13)–(14) include all induced characters, with their actual \(\tau_h\)-normalization. They do not use pointwise progression equidistribution at polynomial modulus \(h\).

The norm-one property before (7) and (13)–(14) give a power saving for all products involving at least one good vector. On the bad×bad block the operator norm is at most its largest entry times the number of bad coordinates (by the Hilbert–Schmidt norm, even if the two bad index sets differ). By (7), (10) and (13), its total signed contribution in a dyad is therefore bounded by
\[
 x^{\,1+.00005-.495\nu+b(\nu)+o(1)}.
\tag{15}
\]
The margin \(.495\nu-.00005-b(\nu)\) is concave. At \(\nu=.001\) it is exactly \(41097/205000000>.000200\), and at \(\nu=.0114\) it is \(2497309/5125000000>.000487\). The \(O(1/L)\) clipped dyadic endpoint in \(\nu\) is harmless. Summing \(O(L)\) blocks, (15), the mixed energy bounds, and (3)–(5) prove the asserted power savings in deleting the polynomial rational band (for instance a sufficiently small \(c_0<.00004\)). For the low-log band one needs only the companion's \(o(x\mathfrak S(N))\) bound. Off-projector/on-projector cross terms in (2) vanish *exactly* on each cell, by the common orthogonal projection.

For clarity about the stated fraction by dimension, on a dyad \(h\asymp d_0\) the number of omitted large-gcd integers is
\[
 \ll d_0\sum_{d\mid N,\ d\ge c d_0^{.01}}\frac1d
 \ll d_0^{1-.0025}x^{o(1)} .
\]
Use a Rankin exponent \(1/4\) in the divisor sum and
\(\sum_{d\mid N}d^{-3/4}=x^{o(1)}\), proved by the Euler product over \(p\mid N\) (split \(p\le L\) from \(p>L\)). This bounds the omitted reduced modes on the top dyads by \(o(H^2)\), as does the entire range \(h<x^{.001}\). It does not imply the remaining spectral contribution is small: the full cell space is larger still and many unselected frequencies, including nonrational ones as a spanning intuition, can carry the original covariance. No distribution statement for targets averaged in \(N\) is used. The character-matrix good/bad argument adapts the earlier fixed-target complete-numerator method in [Complete Polynomial Denominator Blocks](../CompletePolynomialDenominatorBlocks.md), which treats binary prime circle/zeta packets. The new transfer here is the common quotient projection for the actual determinant equation, where the large-prime-stride large sieve and interval/floor reconciliation are needed before applying that method.

For geometric context, [Kontorovich, *Levels of Distribution and the Affine Sieve*, §3.6.1, (3.30)](https://sites.math.rutgers.edu/~alexk/files/Kontorovich2014.pdf#page=23) discusses all-prime \(2\times2\) determinants through the **difference** of two exact semiprimes. His bounded-gap application supplies an unspecified small fixed nonzero difference, not the present macroscopic positive-summand equation at a given large even \(N\). Neither that result nor an affine-sieve prime-pair assertion is needed for (2).
