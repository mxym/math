# A subpower-width unit rectangle in the double Möbius identity

Fix \(B>0\) and a compact interval \(J\subset(0,1)\) of positive length. Write \(L=\log N\), and suppose \(N\) is a sufficiently large individual integer with \(\operatorname{rad}(N)\leq L^B\). There exist fixed \(\zeta,\eta>0\), depending only on \(B,J\) and the fixed comparison parameters chosen in the proof, such that, uniformly for \(1\leq H\leq\exp(L^\zeta)\) and arbitrary complex sequences \(|c_a|,|d_b|\leq1\),
\[
 \left|\sum_{1\leq a,b\leq H}c_a d_b\log a\log b
   \sum_{\substack{am+bn=N,\ am\in NJ\\(am,N)=1}}\mu(m)\mu(n)\right|
       \ll_{B,J} N L^{-\eta}.
 \tag{1}
\]
The arithmetic arguments \(a,b,m,n\) are positive integers. The threshold and implied constant can be ineffective. This estimate has a much wider simultaneous cutoff than [the absolute polylogarithmic rectangle](GrowingDoubleMobius.md), but takes an absolute value **after** aggregation with separable masks, and only asserts the **target-unit** version. Arbitrary joint \((a,b)\) masks and an absolute sum over cells do not follow.

Taking \(c_a=d_b=1\) controls one literal simultaneous short-cofactor rectangle of the exact identity
\[
 \sum_{\substack{x\in NJ\\(x,N)=1}}\Lambda(x)\Lambda(N-x)
   = \sum_{a,b\geq1}\log a\log b
   \sum_{\substack{am+bn=N,\ am\in NJ\\(am,N)=1}}\mu(m)\mu(n).
 \tag{2}
\]
The compact central prime pairs, if any, are on the unit support for large \(N\), since a nonunit prime divides \(N\) and is at most \(L^B\). We do not estimate the complement of the rectangle of (2), remove the unit mask in (1), or infer a binary lower bound.

We use the [affine reflected proof](Proof.md) and the moving scale and first-active construction in [GrowingDoubleMobius](GrowingDoubleMobius.md). The steps needing a different argument are the weighted endpoint removal, the physical grouped coefficients in the projector, and its long-slot and square bounds. Throughout, write \(W=1+\log H\). All log-power budgets of the comparison may be fixed for \(0<\zeta\leq1/2000\) before choosing the final smaller width.

## 1. Weighted endpoints and mesh

For a sequence \(|c_a|\leq1\) define
\[
 C_H(t)=\sum_{\substack{a\mid t\\a\leq H}}c_a\log a\,\mu(t/a),
 \qquad
 D_H(t)=\sum_{\substack{a\mid t\\a\leq H}}\log a.
\]
Use \(B_H(t)\) for the coefficient with \(d_b\) in place of \(c_a\). The sum in (1) is exactly the target-unit sum of \(C_H(x)B_H(N-x)\) on \(NJ\). We have \(|C_H|,|B_H|\leq D_H\). For each fixed positive integer \(r\),
\[
 \sum_{t\leq X}D_H(t)^r\ll_r X W^{r+2^r-1}\qquad(X\geq1).
 \tag{3}
\]
Indeed opening the \(r\) divisors gives at most \(X/[a_1,\ldots,a_r]\) per tuple, without a floor error. Bound the \(r\) logs by \(W^r\) and allow all positive divisor tuples supported on primes \(\leq H\). The Euler product at such a prime is
\[
 1+\sum_{j\geq1}\frac{(j+1)^r-j^r}{p^j}
       =1+(2^r-1)/p+O_r(p^{-2}),
\]
so (3) follows from Mertens' product bound. In particular the second and fourth moment exponents are \(5\) and \(19\). For \(x,y=N-x>0\), Cauchy on these actual correlated arguments, not a local independence assumption, gives
\[
\begin{split}
 \sum_{x=1}^{N-1}D_H(x)D_H(y)&\ll N W^5,\\
 \sum_{x=1}^{N-1}D_H(x)D_H(y)^2&\ll N W^{12},\\
 \sum_{x=1}^{N-1}D_H(x)^2D_H(y)^2&\ll N W^{19}.
\end{split} \tag{4}
\]
The first two follow by pairing second moments or second and fourth moments, and the last by pairing fourth moments.

Put \(\varepsilon=L^{-1/100}\). Use the exact identity
\[
 \mu(m)\log m=-\sum_{p^e\mid m}(\log p)\mu(m/p^e).
\]
For \(m=x/a\) on the central support, \(\log m=L+O_J(W)\). Discard \(e\geq2\) and primes outside
\(\mathcal P_\varepsilon=[N^\varepsilon,N^{1-\varepsilon}]\).
For any \(m>1\) the omitted log mass divided by \(\log m\) is between \(0\) and \(1\), since \(\sum_{p^e\mid m}\log p=\log m\). Let \(E_H(x)\) be the sum of these omitted masses over \(a\leq H,\ a\mid x\), weighted by \(\log a\). Then \(0\leq E_H(x)\leq D_H(x)\). Uniformly for all these \(a\), summing over \(m\leq N/a\) with \(x=am\in NJ\) bounds the summed omitted masses by \(O_J((N/a)(\varepsilon+L^{-1}))\). For a given power \(p^e\), use at most \(N/(ap^e)\) multiples, and use
\[
 \sum_{p,e\geq2}\frac{\log p}{p^e}\ll1,\qquad
 \sum_{p<N^\varepsilon\ {\rm or}\ N^{1-\varepsilon}<p\leq N}
                    \frac{\log p}{p}\ll \varepsilon L+1.
\]
The second estimate follows for both end ranges by Chebyshev and partial summation; the upper end does not use a lower bound for primes in any progression. Thus \(\sum_{x\in NJ} E_H(x)\ll_J \varepsilon N W^2\). The contribution against the actual opposite coefficient is at most
\[
 \sum_{x\in NJ} E_H(x)D_H(y)
 \leq \Big(\sum E_H(x)\Big)^{1/2}
             \Big(\sum D_H(x)D_H(y)^2\Big)^{1/2}
 \ll_J N\sqrt{\varepsilon}\, W^7.
 \tag{5}
\]
Next replace \(1/\log m\) by \(1/L\) in the retained derivative. The absolute sum at each \(m\) changes by \(O_J(W/L)\), since the undivided absolute log mass is at most \(\log m\). The resulting error against the opposite coefficient is \(O_J(N W^6/L)\), by (4). What remains on the source side is **exactly** the coefficient
\[
 \widetilde C_H(x)=-\sum_{\substack{p q=x\\p\in\mathcal P_\varepsilon\ {\rm prime}}}
                    \frac{\log p}{L}\,C_H(q).
 \tag{6}
\]
This groups the actual \(a\)-sum into \(q=a(m/p)\), preserving a literal prime. Its absolute value is at most \(D_H(x)\), because \(D_H(q)\leq D_H(x)\) and the sum of the distinct \(\log p\)'s is at most \(\log x\leq L\). This inequality also holds with all absolute coefficients before grouping.

The first-active construction of §2 of [GrowingDoubleMobius](GrowingDoubleMobius.md) with affine slopes \(1,1\) counts integer rows in \(NJ\) with no active bank by \(O_{B,J,K}(NL^{-\kappa_K})\) for a fixed \(\kappa_K>0\). It uses independent mod-prime residues only for that count, with literal integer CRT and truncation errors already included. Restricting to those rows loses at most
\[
  O_{B,J,K}(N L^{-\kappa_K/2} W^{19/2})
  \tag{7}
\]
in the actual weighted sum, by Cauchy and the last bound of (4).

Use product boxes with multiplicative mesh \(1+L^{-F}\) in \(p,q\) after (6), for any required fixed \(F\). Their number is a fixed power of \(L\). A product box crossing an endpoint of \(NJ\) lies in strips of total \(O_J(N L^{-F}+1)\) integers, since each product varies by \(1+O(L^{-F})\). Dropping these terms, even if not all factorizations of the boundary integers are dropped, costs \(O_J(N L^{-F/2} W^{19/2}+\sqrt N W^{19/2})\), by (4) and the absolute version of (6). Factor packet lengths have logs at least \(\tfrac14 L^{.99}\): \(p\geq\exp(L^{.99})\) and \(q=x/p\gg_J \exp(L^{.99})\). The larger fixed-ratio boxes used for the operator can carry the narrower actual coefficient supports as zero-extended weights. The auxiliary main comparison requested log powers absorb all these fixed meshes and box counts.

## 2. Exact tag removal with short-divisor weights

Expand the first-success identity (6) of [GrowingDoubleMobius](GrowingDoubleMobius.md). In a nonempty term choose its designated bank \(j\) and tag \(u\), with one prime from each of its \(K\) colors. At most \(2^s\leq L\) terms occur. Before the negligible square corrections, the source avoids all primes of each bank occurring in the term, and the opposite integer \(y\) equals \(u h\). On rows with no square at the chosen bank primes, \((u,h)=1\). Every divisor \(b\leq H\) of \(u h\) already divides \(h\): all the tag primes exceed \(\exp(cL^{.1})\), while \(H\leq\exp(L^\zeta)\), \(\zeta<.1\). Hence the exact signed transformation is
\[
       B_H(uh)=(-1)^K B_H(h).
 \tag{8}
\]
The reciprocal hit-count weight is \(\prod_\nu(1+\omega_{j,\nu}(h))^{-1}\); other selected banks are disjoint and their hit tests for \(uh\) are just the tests for \(h\). These are bounded functions of \(h\) alone, independent of the selected tag. Source avoidance conditions are separate for \(p,q\); the retained prime \(p\) is larger than every bank prime.

One can restore all rows after replacing the coefficients by their residual formulae. The only possible differences occur on \(O(N\exp(-cL^{.1}))\) square rows: for each bank prime \(r\) such a row has \(r^2\mid y\), and the sum of \(r^{-2}\) above the minimum bank scale is \(O(\exp(-c L^{.1}))\). There are at most \(O_K(L^K)\) tags per row, because each distinct prime factor of \(y\) is at least two. The absolute source and residual coefficients in the replacement, as well as the original ones, are bounded by \((H W)^2\) per row before tag counting; divisibility of \(h\) into \(y\) also gives \(D_H(h)\leq D_H(y)\). Thus the correction, including all expansions, has more than any fixed log saving, since \(\zeta<.1\). In particular no nonseparable square restriction has to be imposed in the mean-square operator.

For tags \(u\asymp Y\) the actual \(h\)-range is at most \(C_J N/Y\). The residual coefficient \(\mathcal B(h)\) after (8), including all bounded tests, obeys
\[
       \sum_{h\leq C_J N/Y}|\mathcal B(h)|^2
                  \ll_J (N/Y) W^5
 \tag{9}
\]
by (3), not a pointwise polylogarithmic bound. This is the norm needed by the final Cauchy inequality for any one tag shell.

## 3. Checking the weighted projected packet

For clarity, the elementary input into the [projected comparison](../target_slope_switch/Proof.md) now has **actual** source physical slots \(p,q\), with prime coefficient bounded by one and \(q\)-coefficient \(C_H(q)\) plus interval and unit/avoidance masks. Both are at the moving packet scales of §1 of [GrowingDoubleMobius](GrowingDoubleMobius.md). The physical bank primes still divide neither slot. Thus the fibre-constancy and primitive endpoint test of §1 of the [affine reflected proof](Proof.md) hold unchanged: the lattice pair gcd after stripping labels contains the literal prime slot on each side, whereas a nonzero \(k/N\) has absolute value at most \(5Y\), smaller than that prime. The possibility \(k=0\) is excluded by exact divisibility of the coprime tag remainders and source avoidance. No new factor \(a\) is an endpoint coordinate by itself.

**Minor trace and bad pieces.** In the notation of [Jiang, Lau and Lü, v2, (5.14)–(5.16)](https://arxiv.org/html/2611.12467v2), the norm of the input vector \(F\) is estimated by summing its ordered label tuples first. If \(\Pi\) is the full label product on a first-coordinate fibre of scale \(U\), a nonzero source weight requires \(U/\Pi\) comparable to the first factor scale \(M_1\). By (3) each long-slot square sum below a fixed multiple of a scale \(M_i\) is \(O(M_i W^5)\); the prime-slot square sum is \(O(M_i)\). In particular for a weighted first factor this is \(O((U/\Pi)W^5)\), and for a weighted second factor it is \(O(VW^5)\). The ordered reciprocal tuple sums are exactly the old ones. The resulting bound is \(\|F\|^2\ll_K UV L^{O(1)}\), with a log exponent which can be selected uniformly for \(\zeta\leq1/2000\).

For the maximum norm in the Hölder–McCarthy step, used before taking the \(1/T\) power with \(T\asymp L^{1/2}\), the bound \(|C_H(q)|\leq HW\) multiplies the former maximum by at most \(\exp(O(L^\zeta))\). Its \(2/T\) power is bounded. All unweighted labelled paths, lattice reach bounds and the moving frame arithmetic-to-model error \(\exp(-c L^{.8})\) are those already checked in [GrowingDoubleMobius](GrowingDoubleMobius.md). The bad-separation bound before the coefficient supremum is \(\exp(-cL^{.1})\) by JLL Lemmas 6.12–6.13; the bad common/repeated-label bound has the same type of saving by their Proposition 6.15 and the lower bound on the smallest bank prime. In these exceptional pieces even multiplying the old absolute estimates by \((HW)^4\) retains arbitrary log saving. This justifies applying the moving projected minor moment to the present weights. Its requested log power and hence the needed fixed \(K\) are independent of the final choice of the sufficiently small \(\zeta\).

**Projected Parseval and the Fourier cutoff.** For arbitrary separated coefficients with the given masks and bounded real or character twists, the actual product coefficient \(A(t)\) of the two source slots satisfies
\[
\begin{split}
 \sum_{t\ll_J N}|A(t)|^2
 &\ll L^{.01} \sum_{p,q}|\beta_p|^2D_H(q)^2
 \ll_J N L^{.01} W^5 ,
\end{split}
 \tag{10}
\]
where \(|\beta_p|\leq1\) with \(p\) a retained prime and the sum is in a packet of product scale \(\asymp_J N\). Indeed each \(t\ll_J N\) has at most \(O_J(L^{.01})\) distinct prime divisors at least \(N^\varepsilon\); then use (3) and the two numeric scales. Bound (10) also holds for the completely absolute product coefficients, by replacing \(C_H\) with \(D_H\). At the rational major arcs the character modulus divides \(N d\), \(d\leq L^{A_0}\), and in the projection (12)–(13) of the [small-radical major proof](../small_radical_projection/Proof.md) the orthogonality is at \(N d_1\) after the literal \(d_0\) separation of the affine proof. Within the integer size \(O_J(N)\), each class modulo \(N d_1\) occurs \(O_J(1)\) times. Thus (10) gives the full projector Parseval bound with at most the existing polylogarithmic losses, preserving \(1/\varphi(N)\) in its normalization. For the smooth Fourier separation cutoff use the same absolute square bound before expansion: with the two tags and one integer product fixed, the exact unit congruence determines the other product modulo \(N\), allowing \(O_J(1)\) possibilities. Cauchy over the products then gives \(O_J(N L^{.01}W^5)\) per tag pair before the chosen small Fourier-tail factor. No factor \(H\) is inserted into these steps.

**Long cancellation on the exceptional characters.** The Iwaniec moving distinct-character Gram bound and the two tag-exception cardinalities in §1 of [GrowingDoubleMobius](GrowingDoubleMobius.md) are unchanged; the tags have not been regrouped. Bessel is now used on the bounded literal prime slot. For the other slot, open \(q=a v\) in \(C_H(q)\) after the prescribed rational split. On a literal class \(q\equiv r\bmod d_0\), put \(e=(a,d_0)\); it is empty unless \(e\mid r\), and otherwise imposes
\[
 v\equiv(r/e)\overline{a/e}\pmod {d_0/e}.
\]
Reduce a nonunit class by its gcd with this last modulus as in §1 of the affine proof. Characters of \(q\) and real powers \(q^{it}\) separate multiplicatively in \(a,v\); all inducing conductors still divide \(Nd\), as the additional residue modulus divides \(d_0\). Opening \(a\) does not add it to the character modulus. The target and bank exclusions on \(v\), plus those from dividing out the nonunit part, are still on primes \(\leq\exp(2L^{.2})\). Uniformly \(q/a\geq \exp(cL^{.99})\) on the retained intervals, even after a further fixed polylogarithmic division. Hence the same small-radical reciprocal and Perron argument gives arbitrary fixed log cancellation for the remaining genuine \(\mu(v)\) coefficient, for either endpoint. Summing the extracted terms over \(a\) costs only
\(\sum_{a\leq H}(\log a)/a\ll W^2\). Factors from dividing by a nonunit class do not worsen that estimate, and its fixed residue-expansion and polylog-height costs are already absorbed. Therefore the long-slot estimate at scale \(Q\) is \(O_A(Q L^{-A})\) for every prescribed fixed \(A\).

This verifies both parts of the projected major proof: off the two small exceptional sets apply (10); on them use the long-slot cancellation just proved and the restricted Gram/Bessel bound on the actual prime slot. Together with the minor comparison this gives \(O_R(NY L^{-R})\) for the actual projected packet mean square for each required fixed \(R\), with a sufficiently large fixed \(K\). The fixed packet budgets may overestimate all \(W^5,W^2\) factors using \(\zeta\leq1/2000\); separation errors beat the stated pointwise maxima on that entire width range. By (9) and Cauchy, a packet and tag shell contributes \(O_R(N W^{5/2}L^{-R/2})\). These arbitrary fixed log savings pay the box, shell and \(\leq L\) first-active expansions.

## 4. Order of parameters and scope

Fix \(B,J\), the mesh precision and sufficient requested comparison exponents, taking the preceding upper bound \(1/2000\) for the width parameter. This fixes the graph parameters and \(K\), then \(\kappa_K\) from first-active removal. Choose any sufficiently small positive \(\zeta\leq\min(1/2000,\kappa_K/100)\), and only then take \(N\) large. Since \(W\ll L^\zeta\), the endpoint loss (5) has exponent \(-.005+7\zeta\leq-.0015\), and (7) has exponent at most \(-.405\kappa_K\). The log-denominator loss is smaller. Choose the mesh and projected savings above with fixed spare log power; all remaining errors are smaller than \(N L^{-\eta}\), for example with \(0<\eta<\min(.001,\kappa_K/4)\). This proves (1) without treating a graph parameter as moving.

The low-cofactor square in (2) is not the term in which one of the two cofactors is genuinely polynomial in \(N\). With such a cofactor, (8) need not hold, as the cofactor can absorb bank primes; loss of factor support in the long character sum and weighting of the rows missed by all banks also require new estimates. The present theorem is about an aggregated physical unit-supported double Möbius rectangle only. It supplies no sign for the original prime-pair count.
