# The adjusted reverse positive part exceeds the budget on near-equal reflected triples

This is a statement about a specified signed ledger, not its signed total. After the global long-free reverse subtraction, even the sum of positive **grouped** physical rows on genuine near-equal reflected triprimes exceeds the desired uniform \(.010M_N\) upper budget for infinitely many even targets. The quotient \(q\) in these rows is an actual product of three primes in the opened ledger, **not** a prime in the original ledger.

Use \(N=2x,\ L=\log x,\ x^{.10}<s<x^{.14}\) with \(s\) prime, \(n=sq\in(x/2,x]\), \(m=N-n\), and \((n,N)=1\). Use the original [three-mark notation](ActualNegativeThreeMarkReserve.md):
\[
 C(m)=\sum_{\substack{d\ell\mid m\\ d>\sqrt x/H^4,\ \ell>H,\
                           d\ell>\sqrt x/H^2}}\mu(d)\Lambda(\ell),\qquad
 H=\exp(L^\sigma),\quad 0<\sigma<1,\qquad
 W_s(q)=(1-t)(1-2t)^2,\quad t=\frac{\log s}{\log(sq)}.
\]
Write \(M_N=\mathfrak S(N)x/(2L)\), where
\(\mathfrak S(N)=2C_2\prod_{p\mid N,p>2}(p-1)/(p-2)\) and
\(C_2=\prod_{p>2}(1-(p-1)^{-2})\). Set \(U_q=x^{.070},V_q=x^{.010},B=x^{.501}\) and use the exact long-free subtractions
\[
 P_B(r)=-\sum_{\substack{t b=r\\b>B}}(\mu*\mu)(t),\qquad
 H_B(k)=\sum_{\substack{t b=k\\b>B}}\{\mu(t)\log b-(\mu*\Lambda)(t)\},\qquad
 D_B(q)=\sum_{\substack{r k h=q\\r>U_q,\ k>V_q}}
             (\mu(r)-P_B(r))(\Lambda(k)-H_B(k)).
\]
Let \(P_{2x}\) be the sum of the positive part, one for each physical \((s,q)\), of
\[
                  \frac{W_s(q)}{\log q}\,C(2x-sq)\,D_B(q).
\tag{1}
\]
Retain in \(P_{2x}\) **only** \(m\) which are products of three distinct genuine primes in \((x^{.25},x^{.45})\). Then
\[
 \boxed{\ \liminf_{X\to\infty}
    \frac{\sum_{X\le x\le2X,\ x\in\mathbb Z}P_{2x}}
         {\sum_{X\le x\le2X,\ x\in\mathbb Z}M_{2x}}
      > .01037.\ }
\tag{2}
\]
If the reflected restriction uses all distinct triprimes with factors \(<x^{.49}\) instead, the same lower bound argument gives \(>.0416\) before deleting any published triprime tube. The narrow version (2) requires no such deletion adjustment and is the relevant comparison. Neither is a mean of \(P_N/M_N\); both are weighted averages with precisely the original normalization.

## 1. Legitimacy of the whole ledger

With no restriction on the arithmetic shape of \(m\), the whole true \(q\)-prime row \(\sum W_s(q)C(N-sq)\) equals the sum of (1) over eligible integer \(q\), up to \(O_A(xL^{-A})\) for every fixed \(A\). First use the unchanged [reverse Vaughan opening](ReverseVaughanDoubleResidual.md), §2, **before** any partition of the double remainder. On each reflected \(d\)-dyad, the reverse short moduli are \(\le x^{.22}\), whereas \(d\ge x^{.5-o(1)}\); this gives fixed slack in the masked Möbius BV at scale \(d\). The term \(rk>x^{.080}\) is automatic from \(r>U_q,k>V_q\). Replacing the true prime indicator on \(q\) by \(\Lambda(q)/\log q\) in this opening costs a power-small error as in that proof.

For the genuine global swap use [SwitchedLongFreeReverseColumns.md](SwitchedLongFreeReverseColumns.md), with one cutoff check for the present \(C\). The switched moduli \((N-m)/b<x^{.499}\) have the original reduced residue \(N\), and the three short reflected terms have divisor argument at most \(\sqrt x/H^2\). Thus their entire summed CRT floor in that proof is at most \(x^{.999+o(1)}\). The principal calculation uses the identical finite coprime Möbius moments at \(U=\sqrt x/H^4=x^{.5-o(1)}\), and ordinary prime BV with divisor-weighted log reserve controls the \(\Lambda(m)\) error up to \(x^{.499}\). The prime-power exclusion, unit masks and interval variations are as in that proof. This argument licenses the subtraction on the **whole** original ledger, not on the selected chamber individually.

For the normalized criterion in [LocalPositiveComplementObstruction.md](LocalPositiveComplementObstruction.md), the original true \(q\)-prime row is \(Z_{2x}-\mathcal M_{2x}+O_A(xL^{-A})\), where \(Z_{2x}=\sum W_s(q)\Lambda(2x-sq)\) on that row, and the literal matched main \(\mathcal M_{2x}\) is
\[
 (J+o(1))M_N,\qquad J=\int_{.10}^{.14}\frac{(1-2\alpha)^2}{\alpha}\,d\alpha
       =\log(7/5)-.160+.0192.
\]
The desired upper on the signed error is \((.010+o(1))M_N\). The change of the signed expression in this section is negligible at that scale; no assertion is made that the reference of a particular positively restricted subsequence is zero.

## 2. Actual pointwise signs, including artificial composite \(k\)

For \(v>1\) define \(S_z(v)=\sum_{t\mid v,\ t\le z}\mu(t)\) and \(L_B(v)=\sum_{t\mid v,\ t<v/B}\mu(t)\). Then
\[
             \sum_{\substack{r\mid v\\ r>U_q}}(\mu(r)-P_B(r))
                       =-S_{U_q}(v)+L_B(v).
\tag{3}
\]
Indeed \(P_B(r)=0\) unless \(r>B>U_q\), and summing all these \(P_B(r)\) over \(r\mid v\) gives
\(-\sum_{b\mid v,\ b>B}(\mu*\mu*\mathbf1)(v/b)
=-\sum_{t\mid v,\ t<v/B}\mu(t)\).
For \(v=1\) the left side is zero; (3) is not used. If \(k\) is squarefree then
\[
 H_B(k)=\log k \sum_{\substack{t\mid k\\t<k/B}}\mu(t)
\]
by \((\mu*\Lambda)(t)=-\mu(t)\log t\) for squarefree \(t\). In particular for distinct primes \(R,T\le B\), \(H_B(R)=0\) and \(H_B(RT)=(\log(RT))1_{RT>B}\). The latter follows from \(RT/B\le\min(R,T)\) and the strict inequality in the divisor sum. The artificial \(k=RT\) terms are essential.

On the prescribed reflected support, every \(m\)-factor is below \(\sqrt x/H^4\) and above \(H\), and every pair product is \(>x^{.55}\) by the central support. Thus \(C(m)=\log m\) exactly: for each of the three pair divisors \(d\), \(\mu(d)=1\) and \(\ell\) is the third prime. The same reasoning works for the broader support in (2) with cap \(x^{.49}\), since its central triprimes have each factor \(>x^{.02}\) and each pair \(>x^{.51}\).

Use two disjoint physical \(q\)-families:

* **One small prime and one marked macroprime:** \(q=a P Q\) with distinct primes, \(x^{.010}<a<x^{.070}\), \(P,Q<B\), and \(aP>B\); regard \(P\) as the marked factor. Central \(n=sq\) implies \(P,Q>x^{.28}\) and \(P Q>B\); indeed \(P/Q\) need not be close, \(P\le B\), and \(Q\gg x^{.86-.07-.501}\); the same lower holds upon interchanging \(P,Q\). The two marks cannot coexist, since \(aP,aQ>B\) would give \(a q>B^2\), but \(a q\le ax/s<x^{.97}\). For \(k=a\), (3) at \(v=P Q\) is \(-1+1=0\). For \(k=P\) or \(Q\), \(S_{U_q}(aQ)\) or \(S_{U_q}(aP)\) is zero, and \(L_B(aR)=1_{aR>B}\). Such a column contributes \(\log k\) times the mark of its complementary pair. For \(k=P Q\) the only nontrivial \(r\) divides \(a<U_q\) and contributes nothing. Each \(k=aR\), \(R=P\) or \(Q\), has coefficient \(-\log(aR)1_{aR>B}\), multiplied by \(-1\) from the remaining genuine macroprime in (3). The divisor \(k=q\) leaves no valid \(r\). Consequently
\[
                   D_B(q)=\log q\,(1_{aP>B}+1_{aQ>B})=\log q.
\tag{4}
\]
* **Three polynomial macroprimes:** \(q=P Q R\) has distinct prime factors each \(<x^{.358}\). Each factor is \(\gg x^{.86-.716}>x^{.14}\), and each pair is \(\gg x^{.86-.358}>B\). For a prime \(k\mid q\), the complementary pair \(v\) in (3) contributes \(-1+1=0\). For a pair \(k\mid q\), the weight \(-H_B(k)=-\log k\) is multiplied by \(-1\) from the remaining prime. Again \(k=q\) gives no valid \(r\). This yields
\[
                                D_B(q)=2\log q.
\tag{5}
\]
In either family \(s\) is the unique prime label in its designated band. In the first, the marked \(P\) and complementary \(Q\) are unique, and the test \(P,Q<B\) does not impose an ordering beyond the mark. In the second, count the three macroprimes unordered.

These adjusted groups survive the specific previously published [triprime Jain tube](PositiveTriprimeReverseJainTube.md) and [whole-triprime columns](PositiveTriprimeWholeReverseColumns.md): those require a smallest reflected exponent below \(.25\) (in the intermediate column near \(.179\), and in the high charts bounded above by \(.25-4\nu/3+w<.25\)). This is disjoint from our narrow support. Also every **positive individual** adjusted summand on (4) or (5) has \(h=1\), hence \(A=s r k=n\): the only proper nonempty complements have one eligible prime \(r\), with coefficient \(-1\), when \(k\) is prime; if \(k\) is a pair only \(h=1\) can contribute. Thus a deletion of raw low \(A\) columns up to \(x^{.90}\), if licensed in the same ledger, cannot remove positive parts of these groups; any nonzero removed terms within them are negative. The reflected factor \(d\ell=m\) also prevents these summands from being in the short reflected product/near-hyperbola pieces. These remarks do not claim every possible subsequent reassembly leaves (4)–(5) unchanged.

## 3. Joint dyadic mass and an exact rational lower

Put \(\alpha=\log_X s\), \(w=1-\alpha\), and \(W(\alpha)=(1-\alpha)(1-2\alpha)^2\). On dyadic central ranges with \(X\le x\le2X\), all actual exponent cutoffs can be implemented using a fixed inner margin in \(\log_X\) variables, and then letting that margin tend to zero after \(X\to\infty\). With \(n/X\) in fixed subintervals of \([1/2,2]\), the normalized measures of eligible \(n\), weighted by \(W_s(q)D_B(q)/\log q\) on (4)–(5), have ordinary Lebesgue densities \(I_1,I_2\) on the scale \(X/\log X\), where
\[
\begin{aligned}
 I_1&=\int_{.10}^{.14}\frac{W(\alpha)}{\alpha}
           \int_{.010}^{.070}\frac{d a'}{a'}
                   \int_{.501-a'}^{.501}
                        \frac{du}{u(1-\alpha-a'-u)}\,d\alpha,\\
 I_2&=\frac{2}{6}\int_{.10}^{.14}\frac{W(\alpha)}{\alpha}
              \int_{\substack{u+v+z=w\\u,v,z<.358}}
                         \frac{du\,dv}{uvz}\,d\alpha .
\end{aligned}
\tag{6}
\]
Here \(a'=\log_X a,\ u=\log_X P\) are exponents in \(I_1\); \(Q\) is automatically below cap and has positive exponent bounded away from zero, as in §2. There is no extra factorial in \(I_1\) because the mark is unique. In \(I_2\), the \(2/6\) is the exact weight in (5) and the \(3!\) for unordered labels. For the reflected product measure on \(m/X\in[1,3]\) with weight \(C(m)=\log m\), normalized by \(X\), the density is
\[
                   I_m=\frac{1}{6}
                   \int_{\substack{u+v+z=1\\.25<u,v,z<.45}}
                      \frac{du\,dv}{uvz}.
\tag{7}
\]

For completeness, the input is the ordinary prime number theorem on fixed relative intervals, and its partial-summation consequence
\(\sum_{X^a<p\le X^b}1/p\to\int_a^b dt/t\) for fixed \(0<a<b\). In each formula fix all but the final genuine prime, and take the PNT on its actual scale \(X/\)(product of the fixed primes). For an interval \(J\) of the normalized product this yields \(|J|X/(\text{fixed product}\cdot e_{\rm last}\log X)\), with \(e_{\rm last}\) its exponent, uniformly through any fixed interior exponent box. The other prime factors give the reciprocal measure just stated. The weight \(\log m\) cancels the single \(\log X\) on the reflected side, while \(W_s(q)=W(\alpha)+O(1/\log X)\) on the initial side. The cutoffs of each formula are affine inequalities in projected exponents, with these exponents uniformly polynomially positive. Their boundary strips can be bounded by omitting the final-prime restriction and applying the same upper PNT on the full fixed product interval and reciprocal-prime measures on the first slots. The strips cost \(O(\epsilon)\) in the normalized total before \(\epsilon\downarrow0\); thus exact limit densities and the inner-margin lower can be used. Repeated factors are power-small, since any repeated base exceeds \(X^{.009}\) and the number of multiples of their squares among integers \(O(X)\) is \(O(X^{.991})\), using the sum of \(1/p^2\). Labels have bounded multiplicity throughout.

All constants can be lowered without quadrature. In \(I_1\), \(u(1-\alpha-a'-u)\le .89^2/4\), and the inner interval of length \(a'\) cancels the factor \(1/a'\); since \(1-\alpha\ge .86\),
\[
                  I_1\ \ge\ \frac{.24\cdot .86}{.89^2}\,J.
\tag{8}
\]
In \(I_2\) the projected simplex has area \((3\cdot .358-w)^2/2\) and \(uvz\le (w/3)^3\) by AM–GM. Therefore
\[
       I_2\ \ge\ \frac92\int_{.10}^{.14}\frac{(1-2\alpha)^2}{\alpha}
                   \frac{(.074+\alpha)^2}{(1-\alpha)^2}\,d\alpha
             \ \ge\ \frac92\left(\frac{.174}{.90}\right)^2\,J.
\tag{9}
\]
In (7), start with the simplex \(u,v,z\ge .25\), and remove three disjoint projected triangles from the constraints \(u,v,z<.45\). Their sides relative to the simplex coordinates are \(.05\), whereas the full projected side is \(.25\). With \(uvz\le1/27\), this gives \(I_m\ge(27/12)(.25^2-3\cdot .05^2)=.12375\). For the optional broader cap \(.49\) without lower constraint the projected area is \(.47^2/2\), yielding \(I_m\ge (27/12)\cdot .47^2=.497025\). The rational lower \(J>2(1/6+(1/6)^3/3)-.160+.0192\) follows from the positive atanh series for \(\log(7/5)\). These bounds give \(I_m(I_1+I_2)>.01037\) on the narrow support, and \(>.0416\) on the broad support. See [exact arithmetic check](check_adjusted_triprime_positive_budget.py).

For the actual additive constraint, fix normalized \(u=n/X,v=m/X,y=(u+v)/2\). A pair in the region \(1\le y\le2,\ y/2<u\le y\) gives \(N=n+m\), and conversely enforces exactly the central supports and dyadic targets. Both products are odd, so \(N\) is automatically even. The area is \(2\int_1^2(y/2)dy=3/2\), with Jacobian \(2\); there is no extra factor \(1/2\) for the even lattice. The boundary has zero area, so inner and outer rectangle meshes multiply the independent product-measure limits. The unit condition \((n,N)=1\) is exactly \((n,m)=1\). All possible common primes are at least \(X^{.009}\); the count of excluded integer pairs \(n,m\ll X\) is bounded by \(\sum_{p\ge X^{.009}}O(X^2/p^2)=O(X^{1.991})\) on these bounded-multiplicity products. Their weights are \(O(\log X)\); hence this changes nothing at scale \(X^2/\log X\). Endpoints of the dyadic interval or central half interval similarly do not affect the area. This proves
\[
             \sum_{X\le x\le2X} P_{2x}
                  \ \ge\ (I_m(I_1+I_2)+o(1))\frac{3X^2}{2\log X}.
\]
Finally the mean of \(\mathfrak S(2x)\) over integers \(x\) is \(2\). Expanding over squarefree odd divisors \(d\mid x\) gives summable coefficients after weighting by \(1/d\), and the Euler product of the mean is \(2C_2\prod_{p>2}(1+1/[p(p-2)])=2\). Partial summation with \(x/(2\log x)\) gives \(\sum_{X\le x\le2X}M_{2x}\sim3X^2/(2\log X)\). This is the denominator in (2).

## 4. Scope of the obstruction and a direct candidate for signed compensation

Taking positive parts **after** grouping by physical \((s,q)\) already pays more than the original uniform \(.010\) budget on these selected cohorts for infinitely many actual \(N\); taking positive parts before grouping can only cost more. Thus any upper envelope that retains the unresolved positive rows in this specified adjusted ledger and replaces its remaining rows by their positive parts cannot fit the original \(.010\) budget after the cited whole operations. It says nothing about an upper budget \(.010+c_*\) obtained by separately crediting a negative reserve of unspecified size. It does not disprove a signed upper, a different ledger, or an upper after explicitly accounting for compensating negative mass. The independent [local complement obstruction](LocalPositiveComplementObstruction.md) concerns the *signed original true \(q\)-prime complement* on shorter windows, and does not quantify this adjusted positive part against \(.010\). Neither proves binary Goldbach.

A genuine opposite sign occurs in the same adjusted weight: if \(q=P Q\) with distinct primes \(U_q<P,Q\le B\), (3) at a single prime gives \(-1\) and the composite \(k=q\) is absent, so \(D_B(q)=-\log q\). For the marked part of (4) this puts an exact candidate comparison on the same \(s,P\) rows: count \(m+sP v=N\) with the actual near-equal reflected triprime \(m\) and \(v\) a true prime (negative), versus \(v=aQ\) with the small-prime mark \(aP>B\) (positive). The coupled physical \(m\) and \(v\) restrictions remain; independent marginal PNT as used for (2) is not such a fixed-target comparison. No bound for that signed comparison, the rest of the complement, or the Goldbach prime-pair term is claimed here.

## Related work

[Arneth's September preprint](https://zenodo.org/records/23016346) gives exact same-target compensation examples and a separate conditional signed-capacity criterion. [Pham's October preprint](https://www.preprints.org/manuscript/202610.3061) likewise leaves a required fixed-target signed correlation open. The November [K-Correction preprint](https://doi.org/10.20944/preprints202611.0975.v1) separates a different prime/semiprime contamination estimate from its algebraic closure. The lower bound here concerns the positive part of the specific reverse coefficients above and uses a dyadic average; it does not supply the missing uniform arithmetic estimate in any of those frameworks.
