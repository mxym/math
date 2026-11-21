# A quotient-divisor transfer removes two positive triprime profiles but creates a new debit

This note establishes an equality at each fixed even target, not a signed upper bound. Two genuine quotient-triprime profiles from [AdjustedTriprimePositiveBudget.md](AdjustedTriprimePositiveBudget.md) disappear at the natural scale in a different globally equivalent ordered sum. It is **not** a free gain: in that same new sum a different explicit physical positive part averages more than \(.044\) at the same normalization. The missing datum is a signed comparison in the new complement.

## Setup and the exact whole null

Let \(N=2x\), \(L=\log x\), \(H=e^{L^\sigma}\) for fixed \(0<\sigma<1\), and
\[
U=\sqrt{x}/H^4,\quad V=H,\quad Q_0=\sqrt{x}/H^2,\quad B=x^{.501}.
\]
Use prime \(s\in(x^{.10},x^{.14})\), integer \(q\), \(n=sq\in(x/2,x]\), \(m=N-n\in[x,3x/2)\), and \((n,N)=1\). Write
\[
 C(m)=\sum_{d\ell\mid m,\ d>U,\ \ell>V,\ d\ell>Q_0}\mu(d)\Lambda(\ell),
 \qquad W_s(q)=(1-t)(1-2t)^2,\quad t=\frac{\log s}{\log(sq)}.
\]
Keep the actual \(D_B(q)\) from the long-free reverse Vaughan opening in the cited note, and put \(M_N=\mathfrak S(N)x/(2L)\). The whole true \(q\)-prime row equals the sum of \(W_s(q)C(m)D_B(q)/\log q\) over physical \((s,q)\), with error \(O_A(xL^{-A})\) for every fixed \(A\).

For arbitrary fixed log-power bounded weights \(a_{s,d}\), and any intervals \(I_{s,d}\) in the physical \(m\)-range, one has
\[
 \sum_{\substack{s\text{ as above},\ d\ge1\\ sd<x^{.499}}}
 a_{s,d}\!
 \sum_{\substack{sq=N-m\in(x/2,x]\\d\mid q,\ m\in I_{s,d},\ (m,N)=1}}
 W_s(q) C(m)=O_A(xL^{-A}).
 \tag{1}
\]
The inner sum is over **all eligible gates**, not only when \(q\) has a prescribed shape. The estimate allows tests multiplying \(W_s((N-m)/s)\) of uniformly log-power bounded sup norm and total variation on each interval. No signed correlation on a selected subset of \(q\) is used.

Indeed for \(v=sd\) the true reduced progression is \(m\equiv N\pmod v\), and a nonunit \(v\) cannot occur. Use the exact reassembly
\[
 C=\Lambda-\mu_{\le U}*\log
     +\mu_{\le U}*\Lambda_{\le V}*1
     -\!\!\sum_{\substack{d'\ell\mid m\\d'>U,\ell>V,\ d'\ell\le Q_0}}\mu(d')\Lambda(\ell).
 \tag{2}
\]
The last notation denotes a function of \(m\). The usual isolated \(\Lambda_{\le V}\) is zero here. The divisor argument \(a\) of every short summand is at most \(Q_0\), since \(UV=\sqrt{x}/H^3<Q_0\). Write \(m=ah\); \((a,vN)=1\) is forced. Expand \((h,N)=1\) over \(f\mid N\); each \(f\mid h\) leaves one reduced class for \(h/f\bmod v\), so the exact density in the \(m\) variable is \(\phi(N)/(Nav)\), with endpoint error \(O(\tau(N))\) per \(a\). The coefficients of the short divisor arguments are log-bounded, and keeping the smooth \(\log(m/a)\) loses at most log powers by partial summation. Summing floors, including multiplicity over the factorizations \(v=sd\), costs \(x^{.999+o(1)}\).

The uniform finite coprime Mertens estimates of [SwitchedLongFreeReverseColumns.md](SwitchedLongFreeReverseColumns.md), (8), apply with polynomial mask \(vN\) and endpoints at least \(U=x^{.5-o(1)}\). The first logarithmic harmonic sum is \(Nv/\phi(Nv)+O_A(L^{-A})\) and cancels the \(1/\phi(v)\) density of \(\Lambda(m)\); here \((v,N)=1\). The other two short main terms are log-small: for each fixed \(\ell\) the \(d'\)-range is either an initial interval through \(U\) or a nonempty interval with both endpoints at least \(U\), and \(\sum_\ell\Lambda(\ell)/\ell\) is log-bounded. An excluded \(m\) of nonzero \(\Lambda(m)\) is a prime power of a prime dividing \(N\), and costs at most \(x^{o(1)}\) summed over divisors of \(N-m\). The remaining \(\Lambda\) discrepancy uses ordinary maximal Bombieri–Vinogradov up to \(x^{.499}\). Divisor-power weighting follows by Cauchy from an arbitrarily log-small unweighted sum and the trivial bound \(xL^{O(1)}/v\) for each discrepancy, with harmonic divisor moments. All arguments work on subintervals before partial summation. This proves (1).

Define
\[
 F_1(q)=\sum_{d\mid q,\ x^{.010}<d<x^{.070}}\mu(d),\qquad
 F_2(s,q)=\sum_{d\mid q,\ d>x^{.142},\ sd<x^{.499}}\mu(d),\qquad
 B_*(s,q)=D_B(q)/\log q+F_1(q)/3+2F_2(s,q)/3 .
 \tag{3}
\]
The first modulus satisfies \(sd<x^{.210}\), and the second is genuinely \(sd<x^{.499}\). By (1), the true row is also the whole sum with multiplier \(B_*\), with arbitrary log reserve. In particular (3) has not inserted a contribution supported on actual prime \(q\): for prime \(q\asymp x/s\), the two \(F_i\) vanish, and so does \(D_B(q)\).

## Exact selected profiles and fixed-target neck estimate

Use the two disjoint profiles from the prior positive budget. In \(\mathcal Q_1\), \(q=aPQ\) is a product of distinct primes with \(x^{.010}<a<x^{.070}\), \(P,Q<B\), and \(aP>B\). Here \(P\) is the unique mark, since \(a q\le x^{.97}<B^2\) excludes \(aQ>B\) as well. Central support gives
\[
 P>x^{.431},\qquad Q>\tfrac12 x^{.289},\qquad sQ=n/(aP)<x^{.499}.
\]
Thus the only divisor contributing to \(F_1\) is \(a\). In \(F_2\), \(1,a\) are below the lower cutoff; \(Q\) is counted; \(P,aP,PQ,q\) are all excluded since \(sP>x^{.531}\); and \(aQ>x^{.142}\) can contribute if and only if \(saQ<x^{.499}\). As the original multiplier is exactly \(1\),
\[
 B_*=(2/3)1_{saQ<x^{.499}}\qquad(\mathcal Q_1).
 \tag{4}
\]
No negative or flipped \(\mathcal Q_1\) row is created. On \(\mathcal Q_2\), \(q=PQR\) is a product of three distinct primes each \(<x^{.358}\). Each prime is \(>x^{.144}/2\) and each pair is \(>x^{.502}/2\) from \(n>x/2\), so all singles, and no pairs, qualify in \(F_2\); no divisor qualifies in \(F_1\). The original multiplier is exactly \(2\), hence
\[
 B_*=0\qquad(\mathcal Q_2).
 \tag{5}
\]
The old exact \(D_B\) evaluations include all artificial composite columns as in §2 of the prior budget.

On the remaining support in (4), the strict physical endpoint gives \(P=n/(saQ)>B/2\). In particular this is a true fixed-relative cap \(B/2<P<B\), not an independent extra prime-range hypothesis. Let \(\mathcal N\) denote the whole subset in (4). The product sequence \(s\times q\) on \(\mathcal N\) is of full scale \(x\). Generalized BV, in the exact form of [FullScaleConvolutionBV.md](FullScaleConvolutionBV.md), §§1–3, applies to the three short parts in (2). To see independence, the actual marked \(P\) is unique and can be recovered from \(q\); all remaining shape conditions are on \(q\) alone except \(sq\in(x/2,x]\) and \(s(q/P)<x^{.499}\). Freeze \(s\) on relative \(L^{-F}\)-meshes for these tests, preserving its SW interval sequence, and keep the remaining weight on \(q\) arbitrary bounded. In addition to the ordinary central endpoints, a changed row must have the true divisor \(s(q/P)\) of \(n\) within \(O(x^{.499}L^{-F})\) of \(x^{.499}\). The number of integers \(n\) on such an endpoint is at most
\[
 \sum_{a=x^{.499}+O(x^{.499}L^{-F})} O(x/a)
          \ll x(L^{-F}+x^{-.499}).
\]
Physical divisor moments and Cauchy make all weighted errors log-small; the principal uses the same measure with a log-bounded harmonic divisor sum. There are only log-power many rectangles and dyads. Each short modulus in (2) lies below \(Q_0\), which fits \(\sqrt{x}/L^C\) for every fixed \(C\). All actual residues are reduced on the unit domain. Fixing physical \(n\) in the principal gives masks \(Nn\) and exactly the finite \(\mu/\phi\) moments of the cited proof. The logarithmic short term gives \(\mathfrak S(Nn)\); the other two have zero principal up to arbitrary log reserve, with the local equality \(\phi(d)\phi(\ell)/\phi(d\ell)=1-1_{p\mid d}/p\) for \(\ell=p^j\). Therefore
\[
 \sum_{\mathcal N}W_s(q)C(m)
   =\sum_{\mathcal N} W_s(q)[\Lambda(m)-\mathfrak S(Nn)]
             +O_A(xL^{-A}).
 \tag{6}
\]

Fix \(s,a,P\) and put \(b=saP\), \(Y=x/b\gg x^{.289}\). The last actual prime \(Q\) lies at scale \(Y\), so PNT upper bounds the unweighted source by \(O(Y/L)\). Since \(P\in(B/2,B)\), its reciprocal harmonic mass is \(O(1/L)\) by ordinary PNT, while the sums of \(1/s,1/a\) in their respective fixed exponent bands are \(O(1)\). Thus the count in (6) is \(O(x/L^2)\), and \(\mathfrak S(Nn)\ll\mathfrak S(N)\) uniformly since its (at most four) additional factors are all polynomially large. For prime \(m\), use the standard two-linear-form upper sieve on actual \(Q\) and \(N-bQ\), as in [AdjustedFirstTaperAllRank.md](AdjustedFirstTaperAllRank.md). The two forms have distinct roots at primes not dividing \(Nb\); at primes dividing \(N\) or \(b\) exactly one class is removed, including one root at 2, because \((N,b)=1\). Its bound is \(O(\mathfrak S(Nb)Y/L^2)\), since \(\log Y\gg L\). After the factor \(\log m\ll L\) and the above harmonic sum this is \(O(\mathfrak S(N)x/L^2)\). Proper prime powers of \(m\) occur at \(O(\sqrt{x}L)\) physical values and have bounded representation multiplicity in this profile. These terms are negligible even with the log weight. Consequently (6) is \(o(M_N)\) uniformly in the actual fixed target. This proves removal of the **new ledgers** on \(\mathcal Q_1\) and \(\mathcal Q_2\), not cancellation of their old individually restricted sums.

## A genuine new positive chamber exceeds the former budget

For a disjoint explicit packet take \(q=aP\) with distinct primes \(x^{.010}<a<x^{.070}\), and the same central \((s,n,m)\) conditions. Then \(P>\tfrac12 x^{.790}>B\). The actual \(D_B\) is identically zero: its factors containing a true prime \(>B\) have been removed in the exact long-free opening, and if \(P\) is free, the remaining single \(a\) cannot support both \(r>U_q\) and \(k>V_q\). Here \(F_1=-1,F_2=0\), so the new multiplier is exactly \(-1/3\). In particular a formerly zero packet now contributes positively whenever \(C(m)<0\).

For concreteness take true \(m=pR\) with distinct primes \(x^{.10}<p<x^{.40}\) and \(R=m/p\). Then \(p<U<R\) and \(p>V\) for large \(x\), so the only \((d,\ell)\) in \(C(m)\) are \((R,p)\). Thus \(C(m)=-\log p\) exactly. The newly introduced physical positive weight is \(W_s(q)\log p/3\). It is not claimed that a fixed-target signed mass equals this packet. Its true dyadic averaged normalized mass is
\[
 I_{\rm new}\log(3/2),\qquad
 I_{\rm new}=\frac13\int_{.10}^{.14}\frac{W(\alpha)}\alpha
      \int_{.010}^{.070}\frac{da'}{a'(1-\alpha-a')}\,d\alpha ,
 \quad W(\alpha)=(1-\alpha)(1-2\alpha)^2 .
 \tag{7}
\]
Indeed apply the exact independent prime-product counting argument of §3 in [AdjustedTriprimePositiveBudget.md](AdjustedTriprimePositiveBudget.md): on fixed relative intervals of the scaled product \(n/X\), fix \(s,a\) and apply PNT to \(P\) at polynomial scale. For \(m/X\) fix \(p\) and apply PNT to \(R\) at polynomial scale; its normalized density with weight \(\log p\) is \(\int_{.10}^{.40}dt/(1-t)=\log(3/2)\). Both factor labels are unique. Distinctness and removal of common factors cost power-small from the square/CRT estimates in that argument (all prime factors exceed \(X^{.009}\)). A pair \((n,m)\) determines actual \(x=(n+m)/2\), integer since the products are odd. The same area \(3/2\), central half-open endpoints, and mean \(2\) of \(\mathfrak S(2x)\) give (7) on dividing by the actual sum \(\sum_{X\le x\le2X} M_{2x}\). These are not separately sampled targets. In particular the averaged packet exceeds \(.044\): the lower bound
\[
 \frac{.86}{3\cdot .89}\,
 \underbrace{\left(2(1/6+(1/6)^3/3)-.160+.0192\right)}_{<J}
 \underbrace{2(3/4+(3/4)^3/3)}_{<\log 7}
 \underbrace{2/5}_{<\log(3/2)}
 \ >\ .044
\]
uses only rational inequalities and the positive atanh series. Exact arithmetic is included in the small companion script.

Other outside signs do not simply go away: for example a genuine distinct four-prime \(q\) with \(\log_xs\) near \(.12\) and each factor exponent near \(.22\) has all singles but no pairs below \(q/B\); each single is in \(F_2\), and \(F_1=0\). Its exact \(D_B=3\log q\), from the squarefree divisor expression in the companion derivation below, gives \(B_*=1/3\). It still contributes positively on the near-equal genuine reflected triprimes with \(C=\log m\). Both examples have open physical exponent support and require real coupled signs, not just nonnegative upper sieves.

For that last evaluation let \(z\) denote the cofactor of the long free value. If \(q\) is squarefree and all its prime factors exceed \(U_q\), the genuine uncorrected high reverse coefficient is \(\Lambda(q)-\log q\). Using the exact formulas for \(P_B,H_B\), the difference from that coefficient is
\[
 \sum_{z\mid q,z<q/B}\left[
 (\mu*\Lambda_{>V_q})(z)+(\mu_{>U_q}*\Lambda)(z)
             -\mu_{>U_q}(z)\log(q/z)\right].
 \tag{8}
\]
Here no product of two long free values occurs since \(q<B^2\); after grouping, the forgotten unrestricted cofactor gives the two indicated convolutions. For the four-prime packet the possible \(z\) are 1 and its four prime factors. The contribution at 1 is zero; at a prime \(r\) it is \(\log r+0+\log(q/r)=\log q\). This proves the claimed \(-\log q+4\log q\) without approximate logs.

This transfer shows why deleting these selected triprimes is not in itself budget progress: an upper argument taking the positive part of every remaining grouped row in the new ledger would already fail at the original \(.010\) scale on the explicit packet (7), for infinitely many actual targets. There is no assertion that the positive debit can be added to an old obstruction in a different ledger, that the whole signed complement is large, or that a pointwise signed estimate is impossible. No Goldbach conclusion is obtained.
