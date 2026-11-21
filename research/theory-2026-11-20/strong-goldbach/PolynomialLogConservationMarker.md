# Polynomial log markers remove the whole smooth low carrier and control the edge

This is an unconditional cancellation and suppression result for a new marker on two disjoint parts of the fixed-target low residual. It does not establish the sign of the full residual or prove strong Goldbach.

Use the notation \(N,x,I,L,M,a,b,w,\alpha,\varepsilon,\delta,\beta,y,z,D,F_T,F=F_D\) of [LogConservationEdgeMarker.md](LogConservationEdgeMarker.md), in particular \(\alpha=31/200\), \(\beta=1/2-\delta\), and \(w=a-b\). Put \(u_q=\log q/\log n\) for primes dividing \(n\), and \(t_q=\log_xq\). For a polynomial \(P(X)=\sum_{j=1}^m c_j X^j\) of degree at most three define
\[
 K_P(n)=F(n)-
   \sum_{j=1}^m c_j
   \sum_{\substack{q_1,\ldots,q_j<x^\alpha\\ q_i\mid n,\ q_i\ {\rm prime}}}
   u_{q_1}\cdots u_{q_j}\,
   F_{D/\operatorname{rad}(q_1\cdots q_j)}(n).
 \tag{53}
\]
The tuples are **ordered**, allowing repeats. The radical in the physical divisor cutoff is essential. We use the two polynomials
\[
 \begin{split}
 P_2(X)&=3X-2X^2=1-(1-X)(1-2X),\\
 P_3(X)&=5X-8X^2+4X^3=1-(1-X)(1-2X)^2.
 \end{split}
\]
Both have \(P_i(1)=P_i(1/2)=1\), \(P_i(0)=0\). For either choice \(P_i\), the following hold uniformly through even targets at each fixed large \(s\):

1. The rough total \(\sum_{n\in I}H_y(n)w(n)K_{P_i}(n)\) is \(O_\alpha((e^{-s}/\varepsilon+o_s(1))M)\). On \(H_{x^\alpha}=1\) it is the **same pointwise marker** \(K_{P_i}=F\). Thus neither the high estimate nor the \(z\)-rough extraction in [CenteredMarkerHighRows.md](CenteredMarkerHighRows.md) changes.
2. On **every squarefree \(x^\alpha\)-smooth \(n\)** in \(I\), i.e. \(P^+(n)<x^\alpha\), \(K_{P_i}(n)=0\). The nonsquarefree \(y\)-rough part has \(o_s(M)\) actual and reference mass. The labelled and normalization conventions are not needed for this smooth class: it has ordinary low reference mass \((e^{-\gamma}\rho(200/31)+o(1))M/\varepsilon\) in the iterated limit \(N\to\infty\), then \(s\to\infty\).
3. For \(2\delta\le\Delta\le .005\) let \(\mathcal E_\Delta\) be the entire low class with a prime label in \([x^{1/2-\Delta},D]\), counted unlabelled as in the prior edge note. Then
   \[
    \left|\sum_{n\in\mathcal E_\Delta} w(n)K_{P_i}(n)\right|
       \ll_\alpha \left(\frac{\Delta^2}{\varepsilon}+\Delta+
           \frac{e^{-s}\Delta}{\varepsilon}+o_{s,\Delta}(1)\right) M.
    \tag{54}
   \]
   In particular, with \(\Delta=\varepsilon^{2/3}\), this is \(o(M)\) in the iterated sense on a class with labelled reference mass asymptotic to \(2e^{-\gamma}(\Delta/\varepsilon)M\).

The full smooth class in item 2 is genuinely fixed and does not shrink in logarithmic exponent as \(s\) grows. For the original \(F\), the same smooth class had \(F=1\) identically. For the linear-log modification \(G\) in the old edge note, it had \(G=-1\) identically. Neither observation alone bounded its signed discrepancy at the required scale.

## 1. Divisor moduli and exact all-smooth identity

For the discrepancy one can replace every \(u_q\) in (53) by \(t_q\) at a total cost \(O_\alpha(M/(\varepsilon L))=o_s(M)\). Indeed \(\tau=\log_xn=1+O(1/L)\) on \(I\), \(u_q=t_q/\tau\), \(\sum_{q\mid n}t_q\le1\), and the integer-valued \(|F_T|\) is uniformly bounded for all \(T\) used. Then the unmarked rough sieve upper \(O(M/\varepsilon)\) controls the absolute error.

For a physical modulus let \(e=\operatorname{rad}(\prod q_i)\), group its \(k\le j\le3\) distinct small primes, and expand \(F_{D/e}\) over eligible \(d\). All physical moduli \(de\) are at most \(D\). In the rough comparison only \(q_i\ge y\) survive, so \(d,e\), and the ancillary squarefree \(y\)-sieve divisor have disjoint prime ranges and their product is at most \(D y^s=x^{1/2-2\varepsilon}\). An ordered tuple of length at most three contributing to a fixed \(e\) has bounded multiplicity, and its weight is at most \(\prod_{q\mid e} t_q\). The absolute sum of coefficients against the Type I main terms is bounded since
\[
 \sum_{d\ {\rm eligible}}\mu^2(d)g_N(d)\ll_\alpha1,\qquad
 \sum_{y\le q<x^\alpha} \frac{t_q}{q-1}\ll_\alpha1 .
\]
Apply the ordinary linear sieve separately to \(a,b\) in these moduli, as in (49) of the prior note, with main zero for any noncoprime modulus. Divisor-weighted BV errors are \(o_s(M)\) at fixed \(s\). This proves item 1, including the stated \(e^{-s}/\varepsilon\) coefficient bound. The pointwise high equality is immediate from the absence of small prime marks.

If \(n\) is squarefree and \(x^\alpha\)-smooth, \(F=1\) and every \(F_{D/e}=1\) since \(e<x^{3\alpha}<D\) and there is no eligible prime divisor of \(n\). Also \(\sum_{q\mid n}u_q=1\) exactly. Thus (53) equals \(1-P_i(1)=0\). On the rough set, repeats anywhere in \(n\) cost \(O(x^{1-\varepsilon}L)\) in \(a+b\) mass, where \(K_{P_i}\) is bounded independently of \(s\) by \(\sum u_q\le1\) and the bound on \(F_T\). The reference mass follows by the rough product count plus finite Buchstab inclusion-exclusion counting no prime of exponent \(\ge\alpha\), exactly as (46) of [CenteredMarkerLongOverlap.md](CenteredMarkerLongOverlap.md), now with \(u=1\) and no initial long prime. At fixed \(s\) the reference for these fixed-rank products is \(\mathfrak S(N)\) times ordinary counts up to additive \(o_s(M)\) by (35). Taking \(s\to\infty\), the ordinary density ratio is \(\rho(1/\alpha)>0\). This establishes item 2 at the same normalization as item 3.

## 2. Edge signature

It suffices to consider squarefree \(n=Pv\) with a fixed label \(P\in[x^{1/2-\Delta},D]\). In this section \(P\) as a label is a prime, and the chosen polynomial is \(P_i\). Let \(u=1-t_P\in[.5+\delta,.5+\Delta]\) and \(J(T)\) denote the alternating subset sum of the eligible primes of \(v\) at exponent limit \(T\). No eligible product containing \(P\) and another eligible prime can lie below \(D\). For a small tuple \(\mathbf q\) let \(e=\operatorname{rad}(\prod q_i)\); then
\[
 F_{D/e}(n)=J(\beta-t_e)-1_{\,t_e\le\beta-t_P},\qquad
 F(n)=J(\beta)-1.
 \tag{55}
\]
The term involving the indicator has total absolute contribution \(O_\alpha(S_0)\), where \(S_0=\sum_{q\mid v,\ t_q\le\beta-t_P} t_q\); indeed every prime in any qualifying tuple must belong to this short range, so its total tuple weight is \(O((S_0)^j)\). One can use \(t_{q_i}\) in place of \(u_{q_i}\) at \(O(1/L)\) cost pointwise.

Declare exceptions as in §2 of the prior edge note: \(v\) contains a prime \(>D\) or its entire eligible radical has exponent \(>\beta\). If \(v\) has no eligible prime and is not exceptional, \(J(\beta-t_e)=1\) for every small tuple, because \(e<x^{3\alpha}<D\); squarefree \(v\) is all smooth. Hence
\[
 K_{P_i}(n)=-P_i(t_v)+O_\alpha(S_0+1/L)
            =-1+O_\alpha(\Delta+S_0+1/L).
\]
If \(v\) has a nontrivial eligible radical \(\le D\), \(J(\beta)=0\). A nonzero \(J(\beta-t_e)\) comes only from an eligible subset \(d\mid v\) that is removed at the shifted cutoff, so \(\beta<t_{de}\le u\). This yields the counterpart of (52): \(|K_{P_i}+1|\) is bounded by \(O_\alpha(S_0+1/L)\), plus an \(O_\alpha(1)\) multiple of
\[
 \sum_{\substack{d\mid v,\ d\ {\rm eligible}\\d\le D}}
 \ \sum_{j=1}^3\
 \sum_{\substack{\mathbf q\ {\rm small\ primes\ dividing}\ v\\
                  \beta<t_{de}\le u,\ e=\operatorname{rad}(\prod q_i)}}
      \prod_{i=1}^j t_{q_i}.
 \tag{56}
\]
On the exceptions just use \(|K_{P_i}+1|\ll_\alpha1\).

## 3. Pointwise mass bound, including repeated tuple marks

As in the prior edge result, for fixed \(P\) set \(X=x/P\) and count rough \(v\in(X/2,X]\). Exceptions, extra labels, \(S_0\), and the bulk term are bounded there by \(O_\alpha(X[(\Delta+\delta)/\varepsilon+1]/L)\), up to negligible fixed-\(s,\Delta\) errors. For (56), group the tuple by its distinct small factors \(e\); the total weight for any \(e\) is at most a fixed constant times \(\prod_{q\mid e}t_q\), including repeats in the original tuple. For each \(d\) and all but the last distinct small factor (their product \(e'\)), the final prime \(q\) is restricted to \(\beta<t_{de'q}\le u\), a strip of width at most \(h=\Delta+\delta\). Its weighted reciprocal sum is \(O(h+1/L)\), by Mertens. The admissible residual rough cofactor count is \(O(X/(de'q\,\varepsilon L)+1)\). The \(+1\), weighted in the last prime, contributes
\[
 \sum_{q\le X/(de')} t_q\ll X/(de' L)
\]
by Chebyshev uniformly in the small admissible exponents; this covers terminal cofactor 1 and scales below \(y\). The remaining small factors have bounded weighted reciprocal sums and the eligible \(d\) have bounded reciprocal sums. Thus (56) satisfies exactly the same per-label estimate, with no additional negative powers of \(\varepsilon\).

Summing \(P\) uses \(\sum 1/P=O(\Delta)+o_{s,\Delta}(1)\). By (35) at fixed \(s\), positive labelled product regions and weights transfer these ordinary upper counts to the reference, and the **actual** reflected-prime upper is at most four times the leading reference bound. The product rank and the number of affine walls are finite at each fixed \(s\); all leading \(O_\alpha\) constants are uniform since they come from the preceding ordinary counts, not from the implied BV remainder. As before separately compare the total labelled rough \(w\) by Type I, then remove the \(x^\alpha\)-rough high labels at cost \(O_\alpha(\Delta M)+o_{s,\Delta}(M)\) using the compact simplex strip, and correct duplicate labels by their positive upper bound. Therefore writing \(K_{P_i}=-1+(K_{P_i}+1)\) on the edge proves (54).

## 4. Other rows and precise limitation

An additional exact signature is available on the whole squarefree \(m=1\) class. All eligible divisor tests then equal 1 (the tuple product is always \(<D\)), and if
\[
 \lambda=\sum_{q\mid n,\ q>D}\frac{\log q}{\log n},
\]
the sum of the small-prime weights is \(1-\lambda\). Thus 
\[
 K_{P_2}=\lambda(2\lambda-1),\qquad
 K_{P_3}=\lambda(2\lambda-1)^2 .
\]
The cubic variant is nonnegative and no larger than 1 on all of \(m=1\); it vanishes quadratically near \(\lambda=1/2\) and exactly at \(\lambda=0\). This pointwise damping is not a signed estimate of the mixed class.

There is still significant positive low overlap. For example, take two eligible exponents near \((.20,.22)\) and small exponents near \((.10,.11,.115,.12,.135)\). The original \(F=0\). In \(K_{P_2}\), all small singles and pairs cross the eligible pair only, so \(K_{P_2}\) is near \(3(.58)-2(.58)^2=1.0672\). With eligible exponents near \((.190,.200,.240)\) and small exponents near \((.112,.123,.135)\), the original \(F=1\), while all eligible pairs are removed and all singles retained in the shifted tests for \(K_{P_2}\), giving \(K_{P_2}\) near \(1+6(.37)-4(.37)^2=2.6724\), for sufficiently small fixed \(\delta\). These are stable chambers at actual even targets as explained in the prior edge note.

The tradeoff also persists on the larger \(M/\varepsilon\) reference scale, not only on fixed-rank boxes of finite \(M\)-scale mass. Take two eligible primes in exponent intervals of half-width \(10^{-5}\) about .24 and .25, and nine distinct small marked primes in disjoint intervals of half-width \(10^{-6}\) about \(.055+(j-5)10^{-5}\) for \(1\le j\le9\). Leave the remaining cofactor \(y\)-rough and otherwise unrestricted, subject to \(n\in I\). Its log exponent lies in \([.014,.016]\) for \(x\) large, so none of its primes can supply another chosen label or a macro prime. Moreover \(F=0\), since the two eligible primes have product exponent near .49 and every eligible subset fits. Any mark tuple of length at most three containing a chosen .055-scale factor pushes the eligible pair over \(D\) while retaining both eligible singletons. No such tuple can push a singleton out since even the largest small exponent is \(<.056\). Therefore the shifted \(F\) in all these tuples is \(-1\). Tuples involving only residual primes contribute total error at most \(\sum_{j=1}^3 |c_j|(.017)^j\), since their whole normalized log mass is \(<.017\). The full small-prime mass \(S\) lies in \([.509,.511]\), apart from discarded repeats. On this entire carrier,
\[
 K_{P_i}(n)\ge P_i(S)-\sum_{j=1}^3|c_j|(.017)^j > .90
\]
for either polynomial, since \(P_2(S)\ge1\) and \(P_3(S)\ge1-(.022)^2\). The inequalities persist at sufficiently large fixed \(s\) with \(\delta<.001\).

For its reference count, fix the eleven labelled primes and sum the rough cofactor in the induced interval \((X/2,X]\), where \(X=x\) divided by the product of these primes. This scale has log exponent bounded below by .014. Its ordinary count is \((1+o_s(1))X\omega(\log X/\log y)/(2\varepsilon L)\), by the uniform Buchstab formula. All chosen prime intervals have fixed positive logarithmic widths, the product decomposition is unique, and \(\omega\to e^{-\gamma}\) uniformly on the residual exponent range as \(s\to\infty\). Then PNT reciprocal summation and comparison (35) give a strictly positive leading constant times \(M/\varepsilon\) for \(b\) on this carrier. Repeats are negligible. Thus deleting the full smooth class does **not by itself** strictly reduce any proved upper for the final signed low budget: another substantial reference carrier now has positive weight where the old marker vanished, and its actual signed discrepancy is not controlled. This fact does not assert the new total upper is worse; a comparison would require additional arithmetic.

The polynomial modification is global, like the linear-log one. Its main correction on a smooth cofactor attached to \(P\) still uses \(d=1\) and small marks with total exponent \(>\beta-t_P\), so inserting the label into their physical moduli would exceed \(D\). It is not a free localized change of the **old** \(F\) residual. Nevertheless, for the **new** markers, item 2 eliminates a full fixed low factorization class exactly, and item 3 converts another part of larger ambient scale to an \(M\)-scale bound. No claim is made that the remaining mixed low residual meets the Goldbach criterion.
