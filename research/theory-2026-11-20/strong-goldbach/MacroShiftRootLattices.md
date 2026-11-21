# Primitive root counts after dividing the determinant by the target

This note treats one geometric input to a proposed large-shift Type II estimate. It proves an arithmetic root count with congruence decorations at macroscopic shift, and an exact obstruction to literally reusing the fixed-shift small-angle estimate. It does not estimate the actual Möbius/Mangoldt covariance or the Goldbach residual.

## 1. The exact lattice and nonunit disposal

Let \(N\) be an even target of order \(x\). Suppose a factorized covariance has a common cofactor \(h\) on the reflected side:
\[
 N-mn=Ah,\qquad N-rs=Bh .
\]
Then \(P=(Bm,s)\), \(Q=(Ar,n)\) satisfy
\[
 \det(P,Q)=N(B-A).
 \tag{62}
\]
This includes the large-shift analogue of the root pairing in [Hu–Lü–Wang–Wu, arXiv:2611.12756v1, Lemma 4.1](https://arxiv.org/html/2611.12756#S4.SS1). Their small fixed shift proof uses bounded \(|T|/Y\) and a bounded change in local geometric complexity, which do not apply literally to (62).

In the application to [MixedCarrierTypeISeparation.md](MixedCarrierTypeISeparation.md), a signed weight on a factorized integer \(t=mn\) has bounded log-power loss times \(d(t)^C\) for fixed \(C\), and its reflected support \(N-t\) is \(Z\)-rough, at worst \(Z=\exp(L^{1/4})\). Any common prime divisor \(p\mid(t,N)\) is therefore \(\ge Z\). For each such \(p\), writing \(t=pv\) and using \(d(pv)\le2d(v)\), the absolute sum is \(\ll xL^{O(1)}/p\), by the ordinary fixed divisor moment bound. There are \(O(L)\) such divisors, so deleting nonunit terms in the original signed sum costs \(O(xL^{O(1)}/Z)=o(M_N)\). This deletion is done before squaring, not by estimating the paired covariance by a one-point bound.

For pairs in the remaining unit part, \(m,n,r,s,A,B\) are all units modulo \(N\). Equation (62) gives a common slope \(t\) in \((\mathbb Z/N)^*\), and \(P,Q\) lie in
\[
 \Lambda_t=\{(u,v)\in\mathbb Z^2:u\equiv tv\pmod N\},\qquad
 \det\Lambda_t=N .
\]
The oriented basis \(((N,0),(t,1))\) shows that the two coordinates of each vector in the lattice are integers and their determinant **in lattice coordinates** is \(j=B-A\). Equivalently, if \(P=(u,v)\) is primitive in \(\mathbb Z^2\), take
\[
 w\equiv N\bar u\pmod v,\quad 0\le w<v,\qquad
 W=((u w-N)/v,w).
\]
Then \(W\in\Lambda_t\) and \(\det(P,W)=N\), so \((P,W)\) is an oriented basis of \(\Lambda_t\). All lattice vectors with determinant \(Nj\) relative to \(P\) are exactly \(Q=bP+jW\), \(b\in\mathbb Z\).

For the auxiliary marked-version with \(0<|B-A|<Z_1\) and both second coordinates \(s,n\) \(Z_1\)-rough, \(P,Q\) are automatically primitive: any common prime of its coordinates divides \(N(B-A)\), cannot divide \(N\), and as a factor of its second coordinate is at least \(Z_1\). This recovers the primitivity step even though the actual determinant \(N(B-A)\) is large. The main carrier in the previous note is \(x^\varepsilon\)-rough and not naturally marked by the subpower factors of the fixed-shift papers. No existence of that mark structure is assumed here.

## 2. Uniform root matrix count

Let \(I_1\subset[U,2U]\), \(I_2\subset[V,2V]\) be intervals, \(U,V\ge2\), and \(J\subset[0,1)\) an interval. Let \(S\ge1\) be coprime to \(N\), and fix a class
\[
 G_0=\begin{pmatrix}a&c\\b&d\end{pmatrix}\pmod S,\qquad
 (b,S)=1,\quad \det G_0\equiv N\pmod S .
\]
Count primitive \(P=(u,v)\in I_1\times I_2\cap\mathbb Z^2\) with \((uv,N)=1\), \(w/v\in J\), and \((P,W)\equiv G_0\bmod S\), with \(W\) defined above. For any fixed \(\eta>0\) the count is
\[
 \frac{|I_1||I_2||J|}{S^3}\left(\frac{\varphi(N)}{N}\right)^2
       \prod_{p\nmid NS}(1-p^{-2})
   +O_\eta\!\left(\tau(N) V^{1/2+\eta}(U+V)\right).
 \tag{63}
\]
Lengths in the main term are real lengths. The error is absolute, so the statement also applies to short or empty intervals. For \(U,V\asymp x^{1/2+O(.01)}\) and \(S=x^{o(1)}\), the error is polynomially smaller than \(UV/S^3\); this remains true after summing over all residue classes, or a subpower number of rectangles. This is an analogue, on the unit-second-coordinate part, of the basis-position count (4.87) used in [Lü–Wang–Wu, arXiv:2610.20242v2](https://arxiv.org/html/2610.20242v2). It is not the full operator estimate from that paper.

### A completed inverse sum

For each fixed \(v\), \(v\equiv b\pmod S\), \((v,N)=1\), the last coordinate \(w_1=(u w-N)/v\) has its prescribed residue automatically when \(u\equiv a,w\equiv d\pmod S\), since \(v\) is a unit modulo \(S\). We need count \(u w\equiv N\pmod v\) in two intervals and two such progressions. To impose \((u,N)=1\), expand \(\sum_{g\mid (u,N)}\mu(g)\). The progression step for \(u\) is then \(Sg\), and that for \(w\) is \(S\); both are units modulo \(v\).

For completeness, for any two finite arithmetic progressions \(\mathcal A,\mathcal B\) of lengths \(A_0,B_0\) and steps invertible modulo \(v\), and \(C\) invertible modulo \(v\), completion gives
\[
 \#\{(u,w)\in\mathcal A\times\mathcal B:uw\equiv C\bmod v\}
 =\frac{\varphi(v)A_0B_0}{v^2}
 +O_\eta\!\left(v^{1/2+\eta}\left[1+\frac{A_0+B_0}{v}\right]\right).
 \tag{64}
\]
To see the dependence explicitly, the nonzero Fourier frequencies \((k,\ell)\) yield complete Kloosterman sums \(S(k,\ell C;v)\). Their classical Weil bound is \(\tau(v)v^{1/2}(k,\ell,v)^{1/2}\) because \(C\) is a unit. For a nonzero frequency \(k\), the progression Fourier transform is bounded by the smaller of its length and \(O(v/\|k\,\mathrm{step}\|_v)\), where \(\|\cdot\|_v\) is least absolute residue. For any \(e\mid v\), the sum of its absolute values over nonzero multiples of \(e\) is \(O((v/e)\log(2v))\): invertible multiplication permutes that set. Use
\((k,\ell,v)^{1/2}\le\sum_{e\mid(k,\ell,v)}e^{1/2}\).
The both-nonzero terms then sum with \(\sum_e e^{-3/2}\ll1\). When just one frequency is zero, its factor is \(A_0\) or \(B_0\), and \(\sum_{e\mid v}e^{-1/2}\ll_\eta v^\eta\). This proves (64) after adjusting \(\eta\) to absorb the divisor and log factors. In particular applying (64) with \(C=N\) loses no factor \(|N|\) in the Kloosterman bound.

Now \(A_0=|I_1|/(Sg)+O(1)\), \(B_0=v|J|/S+O(1)\). Summing over \(g\mid N\) yields, at this \(v\),
\[
 \frac{|I_1||J|}{S^2}\frac{\varphi(N)}N\frac{\varphi(v)}v
 +O_\eta\!\left(\tau(N)V^{1/2+\eta}[1+U/V]\right),
\]
where the elementary floors are smaller. The remaining \(v\)-sum is
\[
 \sum_{\substack{v\in I_2,\ v\equiv b\bmod S\\(v,N)=1}}\frac{\varphi(v)}v
 =\frac{|I_2|}{S}\frac{\varphi(N)}N
        \prod_{p\nmid NS}(1-p^{-2})
    +O(\tau(N)\log(2V)).
\]
Expand \(\varphi(v)/v=\sum_{e\mid v}\mu(e)/e\). Only \((e,NS)=1\) contribute. Inclusion-exclusion over divisors of \(N\) and CRT give the main term, with the \(O(1)\) floors summing to \(O(\tau(N)\log(2V))\) and the tail \(e>2V\) bounded by \(\sum_{e>2V}e^{-2}\). This proves (63).

## 3. Cusp accounting and scope

For \(t\in(\mathbb Z/N)^*\), take a centered rectangle of half-sides \(U,V\) and put \(Y=UV/N\). Write \(U'=\delta U/\sqrt Y,\ V'=\delta V/\sqrt Y\), and assume \(U',V'<N\). The number of unit slopes whose lattice contains a nonzero vector in \([-U',U']\times[-V',V']\) is at most
\[
 4U'V'\sum_{g\mid N}\frac1g=4\delta^2 N\sigma_{-1}(N).
 \tag{65}
\]
Indeed if one coordinate vanishes, the other must be a multiple of \(N\) by the unit slope and the coordinate bounds, so only the zero pair occurs. If \(g=(v,N)\) for nonzero coordinates, both coordinates are nonzero multiples of \(g\); there are at most \(2\lfloor U'/g\rfloor\,2\lfloor V'/g\rfloor\) pairs, **zero** when either side is too short to contain such a multiple. Each pair gives at most \(g\) slopes by division modulo \(N/g\). This counts short vectors whether primitive or not. The bound applies at all composite \(N\) and is not a Hecke equidistribution assertion.

A single lattice has \(O(Y+1)\) primitive lattice points in the original centered rectangle: if it has no two independent vectors there it has at most two primitive vectors; otherwise the two successive minima are at most one, and the standard lattice point bound and Minkowski's second theorem give \(O((\lambda_1\lambda_2)^{-1})=O(UV/N)\). In particular all bad slopes together support \(O(\delta^2 N\sigma_{-1}(N)(Y+1))\) primitive single roots. This does **not** bound an arbitrary pair covariance at the necessary scale; a pair count can cost an extra factor \(Y\). An ambient primitive vector is lattice primitive. Conversely, if the two ambient coordinates are each units mod \(N\), a nonprimitive ambient vector would be a multiple by a factor coprime to \(N\) of a smaller vector in the **same** lattice and so not lattice primitive.

The normalized coordinate box for a single lattice has area comparable to \(Y\). The exact reconstruction of \(Q\) from \(P,W\), writing \(\theta=w/v\), is
\[
 Q_1=(b+j\theta)u-jN/v,\qquad Q_2=(b+j\theta)v .
\]
Thus when \(UV\asymp NY\), the displacement term in the first box coordinate has size \(jN/(UV)\asymp j/Y\); it need not tend to zero. In contrast the fixed-shift proof has raw determinant \(O(Y)\) in a raw box of area \(\asymp xY\), hence a projective angular difference \(O(1/x)\). Dividing the determinant by \(N\) does not recover that angular scale. Literal transfer of the published box/path estimates is therefore not justified, even though (63) handles a decorated primitive-root count. Recent [arXiv:2611.15558v1](https://arxiv.org/html/2611.15558v1) gives qualitative Hecke results for invariant positive-entropy measures, not the arithmetic quotient-weighted covariance here; effective primitive-rational equidistribution, e.g. [Einsiedler–Luethi–Shah](https://arxiv.org/abs/1901.03078), concerns smooth tests of the homogeneous-space point, not the missing Möbius/prime factor weights.

In particular the count (63) does not license substituting uniform independent weights in (60) or (61) of the mixed-carrier note. A possible follow-up would be a genuinely signed graph estimate on this union of lattice fibers, keeping the quotient factors or controlling the resulting operator before applying them. No such estimate is proved here.
