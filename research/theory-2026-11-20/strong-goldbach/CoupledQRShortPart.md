# A genuine coupled \(Q,r\) short-part transfer on the composite-quotient debit

The extra positive chamber in [HigherQuotientReflectedSourceSwitch](HigherQuotientReflectedSourceSwitch.md) has true independent factors \(q=aQ r b_2b_3\). The prior reflected-source switch cannot put \(Q\) and \(r\) into the same modulus at scale \(x^{.67}\). Here both are retained, as true factors of an independently grouped **source** instead. For one reflected prime mark this evaluates the whole short part of the original \(C\) in that actual chamber. An exact high unmarked-divisor sum remains, with a pointwise favorable sign on a high-rough subfamily and the adverse sign on another genuine rank-four cofactor profile. This is not a cap on the whole debit or a Goldbach proof.

## Statement and exact remainder

Use \(N=2x\), \(L=\log x\), \(H=\exp(L^\sigma)\), and the original \(U=\sqrt x/H^4,\ V=H,\ Q_0=\sqrt x/H^2\) and \(C(m)\) of the prior note. Let \(\mathcal B\) consist of the true labelled prime tuples \(s,a,Q,r,b_2,b_3\), with exponents in the following open intervals (respectively):
\[
 (.1384,.1386),\quad(.0684,.0686),\quad(.2974,.2976),\quad
 (.1650,.1651),\quad(.16512,.16524),\quad(.16525,.16545).
\]
Their product is \(n=sq\in(x/2,x]\), \(q=aQ r b_2 b_3\), \((n,N)=1\), and \(m=N-n\). The disjoint intervals make all six labels distinct and unique. They describe an interior subbox of the earlier true positive debit; e.g. the centers \((.1385,.0685,.2975,.16505,.16518,.16527)\) sum to one. In particular the old Selberg square on \(b=r b_2b_3\) is exactly one since all three primes exceed \(R=x^{1/40}\). The original \(W_s(q)\) is unchanged.

Let \(E=(x^{.311},x^{.321})\), and \(D=x^{.219}\). For a marked true \(p\mid m,\ p\in E,\ p^2\nmid m\), put \(u=m/p\) and
\[
\begin{split}
 A(p,u)={}&\sum_{\substack{d\mid u\\D<d\le U}}\mu(d)\log(pu/d)
 -\sum_{\substack{d\ell\mid u\\D<d\le U,\ \ell\le V}}\mu(d)\Lambda(\ell)\\
 &+\sum_{\substack{d\ell\mid u\\d>U,\ \ell>V,\ d\ell\le Q_0}}\mu(d)\Lambda(\ell).
\end{split}                                                               \tag{1}
\]
Uniformly at every sufficiently large actual even \(N\), for every fixed \(A_0>0\),
\[
 \sum_{\mathcal B}W_s(q)\,[-C(m)]\,\omega_E(m)
 =\sum_{\mathcal B}W_s(q)
       \sum_{\substack{p\in E,\ p\mid m,\ p^2\nmid m\\p\ {\rm prime}}} A(p,m/p)
       +O_{A_0}(xL^{-A_0}).                                                \tag{2}
\]
In particular (2) **does not** replace \(\omega_E\) by the exact-one mask from the prior note. Its other mark-intersection moments on this same genuine source would require additional work.

## Proof of the actual signed short-part cancellation

Drop \(p^2\mid m\) for the currently marked \(p\), which costs \(x^{.689+o(1)}+x^{.321+o(1)}\) by the square divisor sum before the harmless divisor/log weights. Then \(p\nmid u\). In the exact short reassembly \(C=\Lambda-T_1+T_2-T_3\) of the previous note, \(\Lambda(m)=0\). The portions not containing \(p\) in their short argument are the \(d,\ell\mid u\) formulas. Thus (1) is exactly the high part of \(T_1-T_2+T_3\) with no \(p\) in the short argument. The other no-\(p\) portions have \(d\le D\), and hence use a second modulus \(k'\le DV=x^{.219+o(1)}\).

If \(p\) enters a short argument, it must enter \(d=pd'\), with \(\mu(pd')=-\mu(d')\): \(\ell=p\) is impossible in \(T_2\) by \(\ell\le V\), and in \(T_3\) by \(d>U,\ d\ell\le Q_0\). For these \(p\)-bit portions the moduli are \(p k'\) with \(k'=d'\) or \(d'\ell\), and \(k'\le Q_0/p < x^{.19}\). The cutoffs are \(d'\le U/p\) or \(U/p<d'\le Q_0/(p\ell)\), as appropriate; in every nonempty last case \(\ell\le Q_0/U=H^2=x^{o(1)}\). The \(T_1\) log on the \(p\)-bit has \(\log(m/(p d'))\) instead of \(\log(m/d')\).

Use the true source
\[
 \alpha(c)=1_{c=b_2b_3\ \text{with the indicated true prime labels}},\qquad
 \beta(t)=1_{t=s a Qr\ \text{with the indicated true prime labels}} .
\]
All labels, including **both** \(Q,r\), are retained in these coefficients, independently of the actual modulus slots
\[
                  q_1=p,\qquad q_2=k'\le x^{.22},\qquad q_3=1 .
\]
The unit slot requires no lower power of \(x\) and is kept in a fixed size-one bin in [Lichtman Proposition 5.2](https://arxiv.org/html/2309.08522#S5). On dyadic product intervals \(|c|\asymp x^\nu,\ \nu\in[.3303,.3308]\), the strict uniform upper exponents of its four rails are
\[
 -.0093,\qquad .8816,\qquad 1.97055,\qquad 1.800275 .
\]
The last uses that \(5-2\theta>0\), so the fourth bound is largest at \(k'\) scale \(x^{.22}\), with \(\theta=7/32\). The actual residue is \(N=2x\), which is admissible. The first factor has \(P^{-}(c)>z_0\).

Here the first factor is genuinely SW with the auxiliary divisor mask of that proposition. For modulus \(q_\ast\le L^B\) and \((a_\ast,q_\ast)=1\), fix the actual prime \(b_2\) in its interval, deleting if it shares a factor with the auxiliary divisor or with \(N\). It is automatically coprime to \(q_\ast\). Apply prime prefix SW to \(b_3\equiv a_\ast\overline{b_2}\pmod{q_\ast}\), in the intersection of its independent interval and the product dyad, dropping its possible prime divisors of the auxiliary divisor and \(N\). Their cardinality is bounded by \(\tau(\mathrm{aux})^{O(1)}+O(L)\). The summed prime-SW errors over \(b_2\) have arbitrary log reserve at scale \(c\), since the relevant prime interval lengths are both polynomially large and \(\sum_{b_2}1/b_2\) is bounded. The total omitted-divisor error is \(O(x^{.166}(\tau(\mathrm{aux})^{O(1)}+L))\). For \(q_\ast>L^B\), \(\alpha\) is 1-bounded and the trivial AP count \(O(X_c/q_\ast+1)\) and its \(1/\phi(q_\ast)\) counterpart suffice by choosing \(B\) large. This argument is uniform in smaller prime prefixes and dyadic endpoints, and gives the required coprime-masked condition. Unit restrictions on \(n\) split on the two source slots. The other coefficient may be arbitrary bounded on its listed factors, and is independent of \(\alpha\).

Keep \(p\) in its genuine modulus slot and freeze only its location on relative \(L^{-F}\)-meshes for the two upper bounds \(U/p,Q_0/p\). The third slot \(1\) is fixed, and the signed \(k'\) coefficient formed by divisor decomposition is independent of \(p\) **on each such box**. The three cutoff-change errors are controlled by the existence of a true divisor \(p d'\) or \(p d'\ell\) of \(m\) in an \(O(L^{-F})\)-relative strip about \(U,Q_0\); the divisor-opening bound there is \(O(x L^{-F}+x/T)\) per strip at \(T=U,Q_0\). Analogous fine rectangles for the cuts of \(n\in(x/2,x]\), and freezing \(s,n\) for \(W_s\) and the separated \(\log m\) factor, cost \(O_{A_0}(xL^{-A_0})\) by the global divisor moments of \(n\) and \(N-n\), with sufficiently large fixed \(F\). The coefficients depending on \(k'\) contain at most logs and divisor powers. Clip the latter at \(L^K\) and rescale, applying the proposition with enough log reserve; for actual APs the exceptional tail forces \(\tau(N-n)>L^{K'}\), and for the principal it is paid by \(\sum_{k'}\tau(k')^c/\phi(k')\ll_c L^{O_c(1)}\). Coupled freeze errors in the principal itself are bounded directly by the harmonic sums over \(k'\) in the corresponding narrow strips at \(U/p,Q_0/p\): Cauchy with the dyadic divisor moments costs \(O(L^{-F/2+C}+x^{-c})\) per such relative strip, uniformly in \(p\). There are log-power many boxes and all moduli have \((pk',N)=1\) on the surviving tuples. This proves signed replacement of the actual progression \(n\equiv N\bmod pk'\) by its reduced principal, for every indicated short sum.

Fix a physical tuple \(n\) for the principal. The prime \(p\in E\) cannot divide any of its true prime factors, \(p\nmid k'\) by sizes, and a divisor \(p\mid N\) was already excluded. The factor \(1/\phi(pk')\) separates as \(1/(p-1)\) times \(1/\phi(k')\), with the *same* remaining coprimality mask \(Nn\) on both short harmonic sums from \(T_1\). By the finite \(\mu/\phi\) moment of [Huang–Li, Lemma 1](https://huixil.wordpress.com/wp-content/uploads/2019/10/on-a-variant-of-the-elliott-halberstam-conjecture-and-the-goldbach-conjecture.pdf) (see also [SwitchedLongFreeReverseColumns](SwitchedLongFreeReverseColumns.md)), either polynomial cutoff \(T=D\) or \(T=U/p\) gives
\[
 \sum_{\substack{d'\le T\\(d',Nn)=1}}\frac{\mu(d')}{\phi(d')}\log(Y/d')
          =\mathfrak S(Nn)+O_{A_0}(L^{-A_0})
\]
for any of the logs \(Y=m,m/p\) here, because the moment without log has arbitrary log reserve and \(\log(Y/T)=O(L)\). The no-\(p\) \(T_1\) short part and the \(p\)-bit \(T_1\) therefore cancel in the principal, with matching factor \((p-1)^{-1}\) and opposite signs.

For each other short term, fix \(\ell=P^j\) and enforce \((\ell,Nn)=1\). Then
\[
  \frac{\phi(d')\phi(\ell)}{\phi(d'\ell)}
       =1-\frac1P1_{P\mid d'}
\]
on all squarefree \(d'\); no assumption that \((d',\ell)=1\) is needed. Both prefixes for the \(P\)-divisible terms remain polynomial (move \(d'=P f\)), since \(P\le H^2\) in the nonempty \(T_3\) range and \(P\le V\) in \(T_2\). The first, log-free coprime \(\mu/\phi\) moment now gives principal zero with arbitrary log reserve, even after the \(\ell\)-harmonic weights. The same applies to a difference of two prefixes for \(T_3\). Thus all evaluated parts of \(T_1-T_2+T_3\) have zero net principal. Their genuine marked sum is \(O_{A_0}(xL^{-A_0})\). This proves (2); actual squareful \(u\) was allowed throughout.

## Exact scope of the remaining sign

On the subgroup with \(u\) squarefree and \(P^-(u)>x^{.220}\), both \(\Lambda(\ell)\)-correction sums in (1) are zero: the second because \(P^-(u)>V\), and the third because \(d>U\) and \(\ell>x^{.220}\) force \(d\ell>Q_0\). As \(x^{.679}<u<1.5 x^{.689}\), only ranks \(1,2,3\) occur. For rank 1, \(u>U\), so \(A(p,u)=0\). For rank 2, each prime factor lies in \((D,U)\) (each is \(<1.5 x^{.469}\)), but their product exceeds \(U\); the sum in (1) is the negative of the two log weights. For rank 3 the three singletons and three pairs lie in \((D,U)\), and the full product does not. The resulting sum is \(-\log u\) exactly. These are actual nonpositive contributions to the remainder, **not** a sign of the original \(-C\) in that subgroup before evaluating the full short sum.

There is a genuine opposite chamber. Let \(p\) have exponent close to \(.316\) and let \(u\) be a product of four distinct primes near \(.171\) apiece. Every singleton is \(<D\), all six pairs are in \((D,U)\), and every triple exceeds \(U\); both \(\Lambda(\ell)\)-corrections are zero again. Thus \(A(p,u)=6\log m-3\log u>0\) exactly. There is only one \(E\)-mark here. The chamber has genuine positive dyadic occupancy at the signed scale when paired with the actual source \(\mathcal B\), by the same two independent prime-product PNT counts (vary the last free prime in each product, then set the actual \(N=n+m\)) used in [HigherQuotientReflectedSourceSwitch](HigherQuotientReflectedSourceSwitch.md); within each side choose distinct nearby exponent subintervals preserving the stated strict inequalities. This is not a fixed-target lower bound on its mass, and it cannot price its cancellation against the favorable remainder. In particular it explains why (2), although retaining the true \(Q,r\) intersection and removing every one of its short principal terms, is not a uniform upper on the artificial composite-\(b\) correction.
