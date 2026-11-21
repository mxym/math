# Actual reflected-prime mass on the long-marker overlap

This note treats the entire part of the low residual in [CenteredMarkerHighRows.md](CenteredMarkerHighRows.md) with an eligible marker prime \(P\ge x^{49/100}\). Its signed discrepancy is **not** bounded at the scale required for Goldbach.

Use \(x=N/2,\ I=(x/2,x],\ L=\log x,\ M_N=\mathfrak S(N)x/(2L)\), \(a(n)=\log(N-n)1_{N-n\ {\rm prime}}\), and the subpower-rough reference \(b(n)\) of [SinglePrimeRoughRowCriterion.md](SinglePrimeRoughRowCriterion.md). Set \(\alpha=31/200,\ \varepsilon=e^{-s/2},\ \delta=(s+2)\varepsilon,\ y=x^\varepsilon,\ D=x^{1/2-\delta}\) and
\[
 F(n)=\sum_{\substack{d\mid n,\ d\le D\\ P^-(d)\ge x^\alpha}}\mu(d).
\]
At sufficiently large fixed \(s\), let \(\mathcal L\) be the part of the low residual with \(y\le P^-(n)<x^\alpha\) and at least one prime label \(P\mid n\) in \([x^{49/100},D]\). Write \(A,B\) for the sums of \(a,b\) over **labelled** pairs \((P,n)\) in this family. Define the following unlabelled sums:
\[
 A_-=\sum_{\substack{n\in\mathcal L\\ F(n)<0}}a(n),\qquad
 R_{\mathcal L}=\sum_{n\in\mathcal L}F(n)(a(n)-b(n)).
\]
All limits take \(N\to\infty\) through even targets at fixed \(s\), then \(s\to\infty\). The bounds are uniform in the even target:
\[
 \lim_{s\to\infty}\limsup_N\left|
    \frac{\varepsilon B}{M_N}-e^{-\gamma}\log(50/49)\right|=0,\qquad
 \liminf_{s\to\infty}\liminf_N\frac{A_-}{B}>.39,\qquad
 \limsup_{s\to\infty}\limsup_N\frac{R_{\mathcal L}}{B}<.52.
 \tag{42}
\]
The summands of \(A_-\) all lie on the macro-radical \(m(n)>D\) support of the overlap. This shows a substantial genuinely favorable contribution \(-a(n)|F(n)|\) on a complete subfamily, rather than discarding it. The normalization is \(B\asymp M_N/\varepsilon\), not the \(M_N\) of the final criterion.

## 1. Exact decomposition

Take \(\delta<.005,\ \varepsilon<\alpha\). Repeats \(p^2\mid n\) with \(p\ge y\) have total \(a+b\) mass \(O(x^{1-\varepsilon}L)\); the number of labels is at most two and \(|F|\) is bounded by \(2^{\lfloor1/\alpha\rfloor}\) even without squarefreeness. These errors divided by \(M_N\) vanish at fixed \(s\).

Fix a remaining label \(n=Pv\). Call a prime eligible if it lies in \([x^\alpha,D]\). No eligible product of two factors involving \(P\) is retained since \(49/100+\alpha>1/2\). Put \(u=1-\log_x P\), so \(.5+\delta\le u\le .51\). The cofactor \(v\) has at most three other eligible primes since \(4\alpha>.51\). If it has three, every pair is retained because its exponent sum is at most \(.51-\alpha<.5-\delta\). Consequently
\[
 F(n)=-1+1_{\rm bad}(P,n)-1_{\rm double}(P,n).
 \tag{43}
\]
Here \({\rm bad}\) means no eligible prime in \(v\), or three eligible primes with product \(>D\). The case \({\rm double}\) means exactly two eligible primes with product \(>D\). This follows by counting the empty set, the singleton \(P\), and the eligible subsets of \(v\) with alternating signs. In particular \(F\le0\) on this entire class. Two long labels have total exponent at least .98, so all remaining factors are \(<x^\alpha\); then \(F=-1\). Finally, if the product \(m(n)\) of all distinct eligible primes lies in \((1,D]\), every divisor of \(m(n)\) is retained and \(F=0\).

## 2. Total labelled mass, by ordinary Type I

Apply the ordinary two-sided dimension-one sieve separately to the nonnegative \(a\) and \(b\) sequences on \(P\mid n\), temporarily dropping the upper least-factor cutoff. The sieve level is \(y^s\). Every physical modulus \(P\ell\le Dy^s=x^{1/2-2\varepsilon}\), with a unique label \(P\) since all prime factors of \(\ell\) are \(<y\). Thus the divisor-weighted Type I discrepancies of (3) in the original criterion are summable with arbitrary log-power saving. The common main term is
\[
 \frac{x}{2} V_N(y)\sum_{x^{49/100}\le P\le D}g_N(P),\quad
 V_N(y)=\prod_{p<y}(1-g_N(p)),\quad
 g_N(d)=\frac{1_{(d,N)=1}}{\varphi(d)}.
\]
Here \(V_N(y)=(1+o_s(1))e^{-\gamma}\mathfrak S(N)/(\varepsilon L)\) by Mertens and the local factors, with \(o_s(1)\) denoting \(N\to\infty\) at fixed \(s\) throughout. The missing large factors of \(N\) cost \(O(L/y)\) relatively. Also \(\sum_P g_N(P)=\log((1/2-\delta)/(49/100))+o_s(1)\), by prime reciprocals; primes in this band dividing \(N\) cost \(O(Lx^{-.49})\). Nonreduced rows are already included in the Type I error. The relative sieve enclosure is \(1+O(e^{-s})+o_s(1)\). Removing \(P^-(n)\ge x^\alpha\) costs \(O_\alpha(M_N)\) on both sides: this is a bounded-rank product class with label multiplicity at most two, to which (35) of the high note applies (even upon dropping the label condition for the bound). This proves the normalization of \(B\) in (42), and
\[
 \lim_{s\to\infty}\limsup_N|A/B-1|=0.
 \tag{44}
\]

## 3. Reference ratios and a true-prime upper bound

Let \(B_b,B_d,B_t\) be the labelled reference sums restricted to \({\rm bad},{\rm double}\), and having two labels, respectively. The exact unlabelled reference mass in the last case is \(B_t/2\).

At fixed \(s\), every \(y\)-rough product has bounded rank and prime logarithmic exponents at least \(\varepsilon\). The two estimates (35) in the high note apply with fixed \(\varepsilon\) as minimum exponent: partition products into finitely many fixed exponent boxes, allow bounded label selectors on coincident bins, and take the mesh to zero after \(N\to\infty\). All the event boundaries are finitely many affine walls; the corresponding thin wall error is small by bounded simplex density at fixed \(\varepsilon\). In particular, \(b\) mass is \(\mathfrak S(N)\) times ordinary product counts, up to additive \(o_s(M_N)\). This uses BV at the scale of a final prime factor with subpower moduli for the reference, not joint prime and factorization independence. The \(a\) upper bounds from ordinary full-product BV use [Liu–Park–Song, Theorem 3.2](https://link.springer.com/article/10.1007/s40993-017-0089-3#Sec3) and the dimension-one Selberg sieve at the full product scale. They give
\[
 A_b\le 4B_b+o_s(M_N),\qquad
 A_{t,\mathrm{unlabelled}}\le 2 B_t+o_s(M_N),
 \tag{45}
\]
in the normalized limsup sense, sending the fixed sieve level exponent to \(1/2\) at fixed \(s\).

For fixed \(P\) let \(X=x/P=x^u\). The ordinary rough count of \(v\) in \((X/2,X]\) is asymptotic to \(X\omega(u/\varepsilon)/(2\varepsilon L)\) at fixed \(s\), by the Buchstab–de Bruijn uniform formula (e.g. [Fan, arXiv:2306.03347](https://arxiv.org/abs/2306.03347)), with \(\omega(t)\to e^{-\gamma}\). Inserting an unordered set of \(j\) prescribed additional prime factors with exponents \(t_i=\log_xq_i\ge\alpha\) changes the limiting ratio by integration against
\[
 \frac1{j!}\frac{dt_1\cdots dt_j}{t_1\cdots t_j},\qquad \sum_i t_i\le u,
 \tag{46}
\]
on any symmetric exponent region. Indeed fix those primes and count the remaining rough cofactor in \((X/(2q_1\cdots q_j),X/(q_1\cdots q_j)]\). Away from the boundary \(\sum_i t_i=u\), the ratio of Buchstab functions converges uniformly to one as \(s\to\infty\); the prime reciprocal sums give (46). Within a fixed margin \(h\) of the boundary, the upper bound \(\Phi(T,y)\ll T/\log y+1\) for \(T\ge y\) controls the first term at relative \(O(h)\) by reciprocal sums and bounded density. The additive 1, over all possible marked tuples of product \(\le X\), costs \(O_\alpha(X/L)\) for each \(P\): fix all but the last factor and use its prime upper bound at scale at least \(x^\alpha\), then bounded reciprocal sums. This also handles \(T<y\) where the only possible rough cofactor is 1. Its relative cost is \(O_\alpha(\varepsilon)\). The arguments are uniform across the label band; finally let \(h\downarrow0\). Repeats, including tuples involving \(P\) again, were discarded above; their effect when tuple-counted stays negligible because rank is fixed. Removing the \(x^\alpha\)-rough high class has a vanishing relative cost \(O_\alpha(\varepsilon/\log(50/49))\), so the ratios may start from the whole labelled rough count.

If \(v\) has no eligible prime, either it is \(x^\alpha\)-smooth or it contains a prime \(>D\). The first ratio is \(\rho(u/\alpha)\) in this iterated limit, by finite inclusion-exclusion using (46). Indeed, with \(I_0(U)=1\) for \(U\ge0\) and
\[
 I_j(U)=\int_{t_i\ge1,\ \sum_i t_i\le U}\prod_i\frac{dt_i}{t_i},
\]
the alternating sum \(\sum_j(-1)^jI_j(U)/j!\) solves \(U\rho'(U)=-\rho(U-1)\), \(\rho=1\) on \([0,1]\). To compute \(U I'_j(U)\), write \(U=\sum_i t_i\) on the boundary, use permutation symmetry, and project onto \(j-1\) coordinates to get \(j I_{j-1}(U-1)\). The second ratio is at most \(\log(.51/.5)\) by the one-mark formula and \(\delta\to0\). Three eligible factors cost at most the full three-mark region, of volume \((.51-3\alpha)^3/3!\), divided by \(3!\) for unordered marks and with integrand bounded by \(\alpha^{-3}\).

For \({\rm double}\), use just the unordered pair with \(t_i\ge\alpha\) and \(.5-\delta<t_1+t_2\le .51\). Its strip area is at most \((.01+\delta)(.51-2\alpha)\). A second long label is covered by the one-mark bound on \(.49\le t\le .51\). Therefore
\[
 \begin{split}
 \limsup_s\limsup_N B_b/B&\le C_b:=\rho(100/31)+\log(51/50)+\frac{(.51-3\alpha)^3}{36\alpha^3},\\
 \limsup_s\limsup_N B_d/B&\le C_d:=\frac{.01(.51-2\alpha)}{2\alpha^2},\\
 \limsup_s\limsup_N B_t/B&\le C_t:=\log(51/49).
 \end{split}
 \tag{47}
\]
All ratios were transferred to actual \(b\) by the fixed-\(s\) comparison before taking \(s\to\infty\). Monotonicity and \(U\rho(U)=\int_{U-1}^U\rho(t)\,dt\) give \(\rho(U)\le\rho(U-1)/U\); use this twice at \(U=100/31\) and \(\rho(U-2)=1-\log(38/31)\).

## 4. Actual negative mass, signed discrepancy, and limits

The true labelled mass with \(F<0\) is \(A-A_b\) by (43). Correcting for double labels subtracts \(A_{t,\rm unlabelled}\) exactly. By (44)–(47) the iterated normalized liminf for \(A_-\) is at least \(1-4C_b-2C_t\). The labelled discrepancy is
\[
 -(A-B)+(A_b-B_b)-(A_d-B_d)\le |A-B|+3B_b+B_d+o_s(M_N).
\]
Passing to the unlabelled discrepancy costs at most \(A_{t,\rm unlabelled}\), since \(F=-1\) there and \(b\ge0\). Thus its iterated normalized limsup is at most \(3C_b+C_d+2C_t\). The [exact rational checker](check_long_overlap.py) certifies the strict bounds \(>.39\) and \(<.52\).

This gives no \(O(.010M_N)\) bound on \(R_{\mathcal L}\): the bounds are relative to \(B\asymp M_N/\varepsilon\). In particular the upper on the actual \({\rm bad}\) class (smooth cofactor or ineligible long prime, plus the three-marker exception) does not give an \(M_N\)-scale margin. Neither does this cover positive overlap with all marks below \(x^{.49}\). An injection preserving the exact reflected prime \(p=N-n\) at fixed \(N\) fixes \(n\); it cannot shift different sign classes into each other. For example, exponents near \((.110,.125,.135)\) below the macro cutoff and \((.190,.200,.240)\) above it give \(F=1-3+3=1\) for sufficiently large \(s\). There are actual occurrences with reflected prime across even targets: choose a squarefree prime product in small fixed neighborhoods of these exponents, independently choose a prime \(1.2n<p<1.8n\), and set \(N=n+p\). Then \(n\in I\), and replacing the original exponent denominator by \(\log(N/2)\) changes each exponent by \(O(1/\log n)\). This obstructs a label-only injection, not an analytic comparison among different reflected primes.
