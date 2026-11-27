# A sharp Gaussian-mass comparison through rank 41, and through rank 64 for even unimodular lattices

**Theorem.** Let \(L\) be a positive-definite integral unimodular lattice of rank \(1\le n\le41\). For every \(t>0\),
\[
 \Theta_L(t)=\sum_{x\in L}e^{-t\|x\|^2}\le
 \Theta_{\mathbb Z^n}(t),
\]
with equality at even one \(t>0\) only for \(L\cong\mathbb Z^n\). If \(L\) is even unimodular, the strict comparison holds for every positive rank \(n\le64\).

[Kominers, arXiv:2606.01347](https://arxiv.org/abs/2606.01347), proved the uniform result through rank 32, and the even result through rank 40. His §7 identifies the next missing inputs: an upper bound on the first free shadow coefficient in the odd case, and control of an extra cusp coefficient in even rank 48. We use the same modular forms, and supply the missing bounds by geometry of the relevant short shells. The geometric input is useful for both parts: **the largest exceptional angular adjacency in a shell is witnessed by a norm-two root, so it can be counted per vector instead of disallowed**. This is a comparison for integral unimodular lattices in the stated ranges, not a proof of the general stable-lattice conjecture.

## 1. Spherical certificates and exceptional adjacencies

For \(n\ge3\) let \(Q_j^{(n)}\) be normalized spherical Gegenbauer polynomials. They are specified by \(Q_0=1,\ Q_1=x\), and
\[
 (j+n-2)Q_{j+1}(x)=(2j+n-2)xQ_j(x)-jQ_{j-1}(x).
 \tag{1}
\]
The spherical harmonic addition theorem makes each \(Q_j(\langle u,v\rangle)\) a positive semidefinite kernel on the unit sphere; see [Delsarte–Goethals–Seidel, §4](https://doi.org/10.1007/BF03187604). Hence for an even polynomial \(F=1+\sum_{j\ge1}c_{2j}Q_{2j}\), with \(c_{2j}\ge0\), and a set of \(M\) unit representatives of distinct lines,
\[
 M^2\le\sum_{u,v}F(\langle u,v\rangle).
\]
Suppose \(F\le0\) on all allowed off-diagonal absolute inner products except a single value \(s\), and each line has at most \(d\) other lines at \(|\langle u,v\rangle|=s\). Then
\[
 M\le F(1)+d\max(0,F(s)).
 \tag{2}
\]
This follows by counting oriented pairs on the right. In the usual case with no exceptional value, set \(d=0\).

Here is a convenient degree cap for roots. In an integral lattice every reflection in a norm-two vector preserves the lattice; the norm-two roots form a simply laced ADE system \(R\). For each irreducible component of rank \(r_i\), writing \(h_i=|R_i|/r_i\), its sum of outer products is \(2h_i\) times the identity on its span. Indeed this symmetric operator commutes with the irreducible reflection representation; its trace is \(2|R_i|\). Thus
\[
 \sum_{\alpha\in R}\langle x,\alpha\rangle^2\le 2h\|x\|^2,\qquad
 h=\max_i h_i.
 \tag{3}
\]
The empty root system has \(h=0\). The ADE counts give \(h\le2(n-1)\) for \(n\ge16\), and \(|R|\le hn\) by summing. In particular, by the \(\pm\) pairs, the number of roots satisfying \(\langle x,\alpha\rangle=1\) is at most \(h\|x\|^2\).

For any antipodal shell whose pairwise differences are in the lattice, fix \(x\) of squared norm \(a\). If a distinct line in its shell has absolute inner product \(a-1\) with \(x\), orient \(y\) on that line so the inner product is \(+a-1\). Then \(x-y\) is a root and \(\langle x,x-y\rangle=1\). This is an injection, so (3) bounds these exceptional neighbors by \(ha\). The argument applies just as well when \(x\) is in a translate of the lattice.

The following are fixed exact certificates, with \(Q_j=Q_j^{(n)}\) in each row. The last column is an upper bound, not a numerical approximation. The accompanying integer-rational replay verifies all signs via (1).

| Rank \(n\) | \(F\) | Absolute inner products where \(F<0\) | Upper bound on \(F(1)\) | Exceptional value and upper bound |
|---:|:---|:---|---:|:---|
| 38 | \(1+8Q_2+3300Q_6\) | \(0,1/3\) | 3309 | none |
| 39 | \(1+140Q_4+21400Q_8\) | \(1/7,3/7\) | 21541 | none |
| 41 | \(1+7400Q_4+72500Q_8\) | \(1/9,1/3\) | 79901 | \(5/9:\ <473\) |
| 48 | \(1+16Q_4+3800Q_6+201000Q_{10}\) | \(0,1/4,1/2\) | 204817 | \(3/4:\ <5146\) |
| 56 | \(1+\frac{178}{25}Q_2+\frac{48211}{10}Q_6+368346Q_{10}\) | \(0,1/4,1/2\) | 373176 | \(3/4:\ <10590\) |
| 64 | \(1+\frac{1253}{100}Q_2+\frac{26071}{5}Q_6+748230Q_{10}\) | \(0,1/4,1/2\) | 753458 | \(3/4:\ <23195\) |

## 2. Odd unimodular lattices in ranks 33–41

Assume first that \(L\) has no norm-one vectors, so its minimum squared norm is at least two. Use the same nome and notation as Kominers:
\[
 q=e^{-t},\qquad u=\Delta_8/\vartheta_3^8,\quad 0<u\le1/64,\qquad
 \Theta_L/\vartheta_3^n=\sum_{j=0}^{\lfloor n/8\rfloor}a_j u^j .
\]
Here \(\Delta_8=\vartheta_2^4\vartheta_4^4/16\). The standard theta expansion and absence of norm-one vectors give
\[
 a_0=1,\qquad a_1=-2n,\qquad a_2=N_2+2n^2-46n,
 \tag{4}
\]
where \(N_2=|R|\). These are Kominers's Lemmas 2.1, 2.3 and 3.1.

Let \(L_0\) be the index-two even sublattice and \(S=L_0^*\setminus L\) the shadow. It is one coset modulo \(L\), so \(S=-S\), every \(2y\) with \(y\in S\) is in \(L\), and any two shadow vectors have difference in \(L\). In fact \(L\subset L_0^*\) has index two by covolumes. The shadow theta identity (Kominers's Lemma 3.3; see also [Elkies](https://arxiv.org/abs/math/9906086)) is
\[
 \Theta_S=\sum_j(-1)^j 16^{-j}a_j
                  \vartheta_2(q)^{\,n-8j}\vartheta_4(q^2)^{8j}.
 \tag{5}
\]
For \(n=40,41\), the only possible degree-five coefficient \(a_5\) vanishes: its leading shadow term would count vectors of squared norm \(0\) or \(1/4\), respectively. There are no such vectors: \(0\notin S\) and \(2y\in L\) would have norm one in the latter case. Thus the odd range 33–41 always has degree at most four.

Let \(a=(n-32)/4\) be the squared norm of the candidate first shadow shell and \(B\) its number of vectors. From the first term and the next term of (5),
\[
 B=2^{n-48}a_4,\qquad
 a_3\le\frac{n-96}{4096}a_4 .
 \tag{6}
\]
For clarity, the \(j=4\) summand starts at \(q^a\); its relative \(q^2\) coefficient is \((n-32)-64=n-96\), since
\(\vartheta_2(q)=2q^{1/4}(1+q^2+O(q^6))\) and \(\vartheta_4(q^2)=1-2q^2+O(q^8)\).
The \(j=3\) summand starts at \(q^{a+2}\) with coefficient \(-2^{n-36}a_3\). Nonnegativity of that shadow coefficient proves (6).

### Bounding \(B\)

Distinct lines in the antipodal shadow shell have \(|\langle x,y\rangle|\le a-1\), because both \(\|x-y\|^2\) and \(\|x+y\|^2\) are squared norms of nonzero lattice vectors. Furthermore \(\langle x,y\rangle=a-\|x-y\|^2/2\) lies in \(a+\tfrac12\mathbb Z\).

- **Ranks 33–36.** When \(n=33\), \(a=1/4\) is impossible by \(2y\in L\). For \(n=34,35\), \(a<1\), so there can be at most one antipodal line. When \(n=36\), \(a=1\), lines are orthogonal. The bounds on \(B\) are respectively \(0,2,2,72\).
- **Rank 37.** The normalized lines have absolute inner product \(1/5\). The rank-one symmetric projectors onto the lines are independent: their matrix of trace inner products is \((1-1/25)I+(1/25)\mathbf1\mathbf1^T\), positive definite. There are at most \(n(n+1)/2\) lines, giving \(B\le1406\).
- **Ranks 38–39.** The possible normalized absolute inner products are exactly contained in the sets in the corresponding certificate rows. From (2), \(B\le6618\) and \(B\le43082\), respectively.
- **Rank 40.** Now \(a=2\). The shadow comprises two cosets modulo \(L_0\). If one contains a norm-two vector \(y\), then \(L_0+\mathbb Z y\) is integral, since \(y\in L_0^*\) and \(y^2=2\); it also contains the entire coset. Each such lattice has at most \(2n(n-1)\) roots by (3). Thus \(B\le4n(n-1)=6240\).
- **Rank 41, no large \(D\)-component.** Suppose no root component of type \(D_r\) has \(r\ge32\). Then \(h\le60\) by the ADE counts: \(D_r\) has \(h_i=2(r-1)\), \(A_r\) has \(h_i=r+1\le42\), and the exceptional cases have \(h_i\le30\). Thus \(N_2\le41\cdot60\). Here \(a=9/4\), and the normalized absolute inner products lie in \(\{1/9,1/3,5/9\}\). The largest value is a root adjacency, with degree at most \(60\cdot9/4=135\) by (3). The rank-41 certificate gives \(B\le2(79901+135\cdot473)=287512\).
- **Rank 41, a \(D_r\)-component with \(r\ge32\).** Orthogonally project the shell onto this root space. Since \(S\subset L_0^*\) and \(D_r\subset L_0\), the projection belongs to \(D_r^*=\mathbb Z^r\cup(\mathbb Z+1/2)^r\) in the standard orthonormal realization. The half-integer part would have squared norm at least \(r/4>9/4\). The projection is therefore integral with squared norm 0, 1, or 2. The complementary dimension is \(d'\le9\).
  * Projection norm two: there are at most \(2r(r-1)\le3280\) projections, each allowing at most one lift, since residual vectors have norm \(1/2\) and a nonzero difference would have norm less than \(\sqrt2\).
  * Projection norm one: there are at most \(82\) projections. Residuals have squared norm \(5/4\), and any distinct residual inner product equals \(5/4-j/2\) for \(j=2,3,4,5\). For each residual \(x\), the polynomial \(\prod_{j=2}^5(\langle x,v\rangle-5/4+j/2)\) vanishes on all other residuals and not at \(x\). These polynomials are independent in the polynomials of degree at most four on the complement, giving at most \(\binom{d'+4}{4}\le715\) residuals per projection.
  * Projection zero: the same three line angles \(1/9,1/3,5/9\) are confined to the complement. On unit representatives \(x\), use homogeneous separating polynomials \(\prod_{\theta\in\{1/9,1/3,5/9\}}(\langle x,v\rangle^2-\theta^2\|v\|^2)\). There are at most \(\binom{d'+5}{6}\le3003\) lines (none if \(d'=0\)).
  The total is at most \(3280+82\cdot715+2\cdot3003=67916\).

### Passing from shell counts to every Gaussian width

Use \(A_2\) for the upper bound on \(a_2\) obtained by (4), taking \(N_2\le2n(n-1)\) except in the low-root-density rank-41 case above. All these \(A_2\) are positive. By (6) and \(0<u\le1/64\),
\[
 \begin{aligned}
 \frac{\Theta_L/\vartheta_3^n-1}{u}
 &\le -2n+\frac{A_2}{64}
        +a_4u^2\left(u-\frac{96-n}{4096}\right)\\
 &\le -2n+\frac{A_2}{64}+B(n-32)2^{24-n}.
 \end{aligned}
 \tag{7}
\]
The quantity subtracted from zero on the last line, using the upper bounds on \(B\), is strictly positive. The exact margins for ranks \(33,\ldots,40\), consecutively, are
\[
 363/16,\quad5439/256,\quad20157/1024,\quad2295/128,\quad
 62789/4096,\quad48441/4096,\quad48893/16384,\quad2365/256 .
\]
For rank 41 they are \(12421/16384\) in the low-root-density case and \(99093/32768\) in the large-\(D\) case. This proves the required strict inequality for every positive \(t\) in this odd range.

## 3. Even unimodular lattices in ranks 48, 56, 64

Write \(n=8m\), with \(m=6,7,8\). In level-one weight \(4m\), the modular-form ring gives the theta expansion
\[
 \Theta_L=E_4^m+c_1 E_4^{m-3}\Delta+c_2 E_4^{m-6}\Delta^2 .
\]
The basis has precisely these three elements in these weights. Let \(r=N_2\), and \(N_4\) the number of squared norm-four vectors. Since \(E_4=1+240q^2+2160q^4+\cdots\) and \(\Delta=q^2-24q^4+\cdots\), comparison of the first two nonconstant coefficients gives
\[
 c_1=r-240m,\qquad
 c_2=N_4+m(28800m-151920)-(240m-744)r .
 \tag{8}
\]

**Norm-four bound.** Distinct lines in the norm-four shell, normalized to unit vectors, have absolute inner products in \(\{0,1/4,1/2,3/4\}\) by integrality. Only the last is exceptional in the table, and its degree is at most \(h\cdot4\le8(n-1)\) by (3). From (2) one obtains
\[
 \begin{array}{c|rrr}
 n &48&56&64\\ \hline
 N_4\ \text{upper bound}&4279426&10065552&24887476 .
 \end{array}
 \tag{9}
\]
Importantly, the \(r\)-dependent terms in (8) must be kept together rather than maximized independently.

**All widths.** Put \(e=E_4/\vartheta_3^8=1-16u\in[3/4,1)\), so \(\Delta/\vartheta_3^{24}=u^2\). The full ratio is \(e^m+c_1e^{m-3}u^2+c_2e^{m-6}u^4\). Its coefficient on \(r\) from (8) is
\[
 e^{m-6}u^2\bigl(e^3-(240m-744)u^2\bigr)>0,
\]
as \(e^3\ge27/64>1176/4096\). Thus substituting \(r=2n(n-1)\) is an upper bound, along with the respective bounds on \(N_4\) from (9). This results in
\[
 U_m(e)=e^m+A e^{m-3}u^2+C e^{m-6}u^4,\qquad
 A=128m(m-2),
\]
with \(C=1264354,4647552,16032052\), respectively. At \(e=3/4\) these upper bounds are
\(4779377/8388608,\ 360351/524288,\ 66678453/67108864\), all strictly below one.

For the full interval use
\[
 \frac{1-U_m(e)}{1-e}=
 \sum_{j=0}^{m-1}e^j
 -\frac{A}{256}e^{m-3}(1-e)
 -\frac{C}{65536}e^{m-6}(1-e)^3 .
\]
This is increasing on \(e\in[3/4,1)\). The derivative of the first term is at least \(1+2e+3e^2\ge67/16>4\). The derivative of the middle subtracted term before its minus sign is decreasing there, since its derivative's sign of change is that of \((m-4)-(m-2)e<0\); it is less than 4 at \(3/4\) for all three \(m\). The last term before subtraction is decreasing because \((m-6)(1-e)-3e<0\); here \(C>0\). The positive endpoint values therefore prove the strict inequality at all widths.

## 4. Assembly, scope, and exact replay

An integral unit vector splits off an orthogonal \(\mathbb Z\), since every lattice projection coefficient onto it is integral. Iterate, leaving a unimodular lattice with no norm-one vectors, or the zero lattice. Gaussian masses multiply on orthogonal sums. Using Kominers's proved lower-rank ranges together with §§2–3 gives the stated full range and equality condition. Even unimodular ranks are divisible by eight, so the even range ends at 64 and has no other omitted ranks below it.

In addition to Kominers, compare [Shi–Dai–Solé, arXiv:2611.19749 v2](https://arxiv.org/abs/2611.19749), which proves a pointwise result for *extremal* Type II lattices and uses a separate genus-average result; this note does not impose extremality or average over a genus. [Bollauf–Lin](https://arxiv.org/abs/2403.16932) give another analytic criterion. No classification of the individual unimodular lattices in the new ranges is required here.

The accompanying JavaScript replays 167 exact rational assertions, including the Gegenbauer signs, root-count/adjacency totals, every odd margin, and the even endpoint and interval-derivative tests. The proof uses standard modular and spherical identities stated explicitly above. No floating-point optimizer is required to reproduce any certificate.
