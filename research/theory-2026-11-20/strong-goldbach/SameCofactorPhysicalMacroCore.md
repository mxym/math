# Physical macro-core regrouping of the same-cofactor Vaughan term

In [SameCofactorVaughanCenter](SameCofactorVaughanCenter.md) the true prime-versus-balanced-semiprime cell was reduced to one open Vaughan Type II sum. Grouping it by the **actual reflected integer** eliminates the formerly suspect irreducible center with two genuine large primes and a nontrivial small core. We further move the equal Vaughan cutoffs to just below the quarter exponent and bound the entire four-macro and mixed three-macro neck. Pure all-macro semiprimes/triprimes and a long smooth-core signed term survive.

## 1. Literal physical identity, including proper powers

Use the preceding note's \(N=2x\), \(I=(x/2,x]\), \(L=\log x\), \(m=N-su\), \(Z=e^{L^{1/4}}\), \(R_Z(v)=1_{P^-v\ge Z}\), \(M_N=\mathfrak S(N)x/(2L)\), unit mask \((su,N)=1\), and signed \(C_s(u)\). Thus \(s\) is a genuine prime of exponent \(\sigma\in[.10,.14]\); \(C_s(u)\) has true prime or distinct balanced-semiprime quotient, both \(x^{.36}\)-rough, and the source mark is unique. Its prime score is \(1-f\) and its semiprime score \(-1-f\), where \(f(t)=(1-2t)^3\), \(t=\log s/\log(su)\).

For real \(U\ge2\) put
\[
 T(m;U)=\sum_{\substack{d\ell k=m\\d,\ell>U}}\mu(d)\Lambda(\ell),
 \qquad S_U(v)=\sum_{\substack{d|v\\d\le U}}\mu(d).
\]
Factor \(m=Mv\) canonically with \(M=\prod_{p\mid m,\ p>U}p^{v_p(m)}\). Then for every positive integer \(m\),
\[
 T(m;U)=\Lambda(m)1_{m>U}-(\log M)S_U(v)
       -\sum_{\substack{\ell|v\\\ell>U}}\Lambda(\ell)S_U(v/\ell).       \tag{1}
\]
For each long \(\ell\mid m\), complete the \(d\)-sum to \(1_{m=\ell}\) and subtract its short part. If the base of \(\ell\) is \(>U\), all short \(d\) divide \(v\); all the corresponding prime-power logs sum to \(\log M\), with their full multiplicities. Otherwise the base is in \(v\), and the short sum is exactly \(S_U(v/\ell)\). This proves (1), also when \(M=1\) or a pure prime power. For example, \(m=p^j\) with \(p>U\) gives \(\log p-\log m\). The last sum properly retains long powers with a small base.

For squarefree \(m>U\), the last sum is empty. A prime contributes exactly zero; so does a composite with \(M=1\) or \(1<v\le U\). A pure all-macro composite (\(v=1\)) contributes \(-\log m\), and a mixed composite with \(M>1,v>U\) contributes \(-(\log M)S_U(v)\). The zero for \(M>1,1<v\le U\) holds even with repeated prime factors.

At the original equal cutoff \(U=x^{1/5}\), the open term in equation (3) of SameCofactorVaughanCenter groups exactly to \(\sum_{s,u} C_s(u)1_{(su,N)=1}R_Z(m)T(m;U)\), since the combined factor rough masks equal \(R_Z(m)\). In particular if \(m=pqv\), \(p,q\) are distinct true primes \(>x^{.43}\), and \(v>1\), then \(v\le1.5x^{.14}<U\) and the coefficient is zero. The original open shape \(d\) true prime near \(x^{.49}\), \(\ell\) true prime near \(x^{.46}\), and \(k\) near \(x^{.05}\) is part of this exactly vanishing aggregate, not an unresolved contribution by itself. The allocations of the small core to \(d\) must be included with their actual signs. All long \(\Lambda\)-labels in this two-big shape have bases \(>x^{.43}\), so it is disjoint from the two low-\(\ell\) charts in [SameCofactorTypeIIRoughCore](SameCofactorTypeIIRoughCore.md). More general classes in (1) may overlap those charts; we regroup the **whole original** sum here, not the chart-subtracted one.

## 2. Moving equal cutoffs, unchanged literal reference

Let \(\varepsilon=L^{-.49}\), \(\vartheta=1/4-\varepsilon\), and \(U=x^\vartheta\). Uniformly for every fixed \(D>0\), the **same** \(G_N=\sum_{s,u}(a-b)(su)C_s(u)\) now satisfies
\[
 G_N=\sum_{s,u} C_s(u)1_{(su,N)=1}R_Z(m)T(m;U)+O_{D,\delta}(xL^{-D}).   \tag{2}
\]
This is a new decomposition of the same observable, not additional credit on the old decomposition.

Use the exact Vaughan identity with both cutoffs \(U\), as in Section 2 of SameCofactorVaughanCenter. The two short moduli are \(q=d\le U\) and \(q=d\ell\le U^2\); they are \(Z\)-rough. Open the remaining rough condition by squarefree Bonferroni labels \(e\) supported below \(Z\), of depths near \(L^{1/4}\), giving
\[
 qe\le x^{1/2}\exp(-2L^{.51}+O(L^{1/2}))<x^{1/2}L^{-B}
\]
for every fixed \(B\). The decomposition \(qe\) is unique by disjoint prime support. For \(q=d\ell\) the signed modulus coefficient has absolute weighted multiplicity at most \(\sum_{\ell|q}\Lambda(\ell)=\log q\). In the first short term retain \(-\log d\) in its modulus coefficient and \(\log m\) in the source. This latter factor is frozen to \(\log(N-s_0u)\) only when separating the \(s\)-bin, with error \(O(L^{-K})\) on relative bin width \(L^{-K}\).

Apply classical convolution BV at the **full scale \(su\asymp x\)**: [Polymath, Theorem 2.9, journal p.2079](https://msp.org/ant/2014/8-9/ant-v8-n9-p03-p.pdf), from [BFI Theorem 0(b)](https://doi.org/10.1007/BF02399204). It allows maximum reduced residue up to \(x^{1/2}L^{-B(D)}\), on independent dyadic coefficient scales with product comparable to \(x\). The SW slot is the genuine \(s\) in a relative bin, in \([x^{.10},x^{.14}]\). Prime prefix SW remains true with its auxiliary coprime mask: remove at most \(O(L+\omega(d_0))\) primes dividing \(Nd_0\) and use the trivial progression estimate for moduli larger than any required log power, as in SameCofactorTypeIIRoughCore §2. The other slot is the bounded true signed \(u\)-coefficient after extracting \(O(L)\) for logs; neither artificial primes nor SW on the semiprime side are needed. Use the actual reduced residue \(N\) with \((q e,N)=1\) forced by the unit condition, and the coprime model \(1_{(su,qe)=1}/\phi(qe)\).

For separability use dyads and \(s\)-relative bins of width \(L^{-K}\) about comparison points \(s_0\). Freeze the tests \(s_0u\in I,\ P^-u>x^{.5+2\delta}/s_0\) and the smooth log score, never the actual \(s\) in a congruence or unit mask. The physical endpoint strip has \(O(xL^{1-K}+x^{.14})\) pairs by counting \(u\) at fixed \(s\). A changed quotient-factor cutoff requires one factor of the true semiprime in a relative \(O(L^{-K})\) strip near \(x^{.5+2\delta}/s\). Counting this factor as an integer, then its quotient as an integer, gives \(O(xL^{1-K}+x^{.64})\) pairs. The genuine mark is unique on original and frozen supports. Physical opened coefficients at each \(m\) are bounded by \(L\tau(m)^{O(1)}\), including Bonferroni overlap, so Cauchy with fixed divisor moments pays both strips to arbitrary-log accuracy; in the principal the absolute harmonics cost only log powers. There are only a fixed log power of bins, dyads and prefixes. The sieve bracket error uses the unsigned coefficient first, then the same BV and the factorial Euler tail. Hence no extra loss at the moving BV frontier.

The masked rough harmonic evaluation (4)–(5) in SameCofactorVaughanCenter is uniform at the new polynomial \(U\), with \(\log U\asymp L\) and polynomial mask \(Nsu\). Pointwise \(\log(m/d)=\log(U/d)+\log(m/U)\), with the unweighted harmonic killing the latter. When \(\ell=p^j\) and \(p\mid d\) the second principal's overlap correction \(1-1/p\) costs \(O(L^{O(1)}/Z)\) as there. Together these short terms still match the literal \(b(n)\) reference, independent of the new cutoff. Proper powers in replacing the prime log weight by \(\Lambda(m)\) cost \(O(x^{1/2}L^{O(1)})\). This proves (2).

## 3. Removing the complete quarter neck

All nonsquarefree \(m\) may be discarded in (2) at arbitrary-log precision. On \(R_Z\) their population is \(O(x/Z+x^{1/2})\) by opening \(p^2\mid m,\ p\ge Z\), even summing over integer bases. The weight \(L\tau(m)^{O(1)}\) and Cauchy with fixed divisor moments pay the deletion. This estimate is applied only after the literal formula (1).

For squarefree \(m\), \(j=\omega(M)\le4\) eventually. We show that \(j=4\) and \(j=3,v>U\) together contribute \(O_\delta(M_N L^{-.46})\) in absolute value. These are actual fixed-target bounds, not PNT averages of additive correlations.

Fix \(s\), a product \(P\) of three true macro primes with exponents in the neck below, and \(a\le2x^{4\varepsilon}\) with \(R_Z(a)=1\). Write \(m=Pa b\). The \(j=4\) use takes \(a=1\), \(b\) the last true prime; the other use has \(b\) \(Z\)-rough. The row is empty unless \((sPa,N)=1\), \((s,Pa)=1\): if \(s\mid Pa\) then \(s\mid m,n,N\), contrary to the actual units. Choose \(1\le b_0<s\), \(b_0\equiv N\overline{Pa}\pmod s\); the free forms are
\[
 b=b_0+s t,\qquad u=u_0-Pa\,t,\qquad u_0=(N-Pa b_0)/s .
\]
Each is primitive, their determinant is \(N\), and \(t\) lies in an interval of length \(O(x/(sPa))\); \(sPa\le x^{.89+o(1)}\) here. Since \(u\) is \(x^{.36}\)-rough, sieve it to \(x^\eta\) for a fixed sufficiently small \(\eta>0\). Sieve \(b\) to \(Z\) when rough or to \(x^\eta\) when prime (the actual prime is \(>U\)). The upper beta-sieve, e.g. Friedlander–Iwaniec, *Opera de Cribro*, Theorem 6.9, with level \(x^{.01}\) and \(\eta\) sufficiently small in fixed dimension two, gives
\[
 \ll\mathfrak S(N)\frac{x}{sPa L^{5/4}}+x^{.01+o(1)}
 \quad(\text{rough }b),\qquad
 \ll\mathfrak S(N)\frac{x}{sP L^2}+x^{.01+o(1)}
 \quad(\text{prime }b,\ a=1).                                      \tag{3}
\]
Indeed below the smaller cutoff there are two forbidden residues at primes outside \(NsPa\), one at primes of \(N\) when the slopes are units, and one at primes of \(sPa\): one form is then constant nonzero, the other has unit slope. At \(2\) both slopes are odd and \(N\) even, so the single root yields the local singular factor \(2\). The exceptional slope primes are all \(\ge Z\), yielding only a relative factor \(1+O(L/Z)\) in the local product. When only \(u\) is sieved there is one root except at primes dividing its slope. Mertens gives the mixed product \(O(\mathfrak S(N)/(\log Z\log x^\eta))\), and the both-long product \(O(\mathfrak S(N)/(\log x^\eta)^2)\). The dimension condition is uniform by \(\nu(p)\le2,\,\nu(2)=1\); the CRT floor at squarefree \(d\) is at most \(2^{\omega(d)}\), yielding \(x^{.01+o(1)}\) at the indicated sieve level. No prime lower estimate is used.

* **Four macros.** Here \(v\le1.5x^{4\varepsilon}<U\), so only \(v=1\) survives. Each of the four true primes has exponent in \((\vartheta,1-3\vartheta+O(1/L)]\); its reciprocal prime harmonic is \(O(L^{-.49})\) by ordinary PNT with log reserve, also on this shrinking exponent interval. Choose three for \(P\) and apply the prime case of (3) with \(b\) the last. Counting all label orders is harmless. The \(\log m\) weight costs \(O(L)\), the \(s\)-harmonic is \(O(1)\), and the three prime harmonics cost \(O(L^{-1.47})\). There are \(x^{.89+o(1)}\) labels \(s,P\), so the sum of floors is power-small with the log weight. This gives \(O(M_N L^{-1.47})\).
* **Three macros and \(v>U\).** Their exponents lie in the same near-quarter interval, since the other two and \(v\) each exceed \(U\). Complete Möbius and complement the divisor:
\[
 |S_U(v)|\le\sum_{\substack{a|v\\a<v/U}}1,\qquad
                     v/U\le1.5x^{4\varepsilon}.
\]
Open \(a\), then apply the rough case of (3) to \(m=Pa b\). Its rough harmonic satisfies
\[
 \sum_{\substack{a\le W\\R_Z(a)=1}}\frac1a
 \le\prod_{Z\le p\le W}(1-1/p)^{-1}
 \ll\frac{\log W}{\log Z}\ll L^{.26},\qquad W=2x^{4\varepsilon}.
\]
The total is \(O(\mathfrak S(N)x\cdot L\cdot L^{-1.25}\cdot L^{.26}\cdot L^{-1.47})=O(M_N L^{-.46})\). The \(a\)-choices are subpower, so again the aggregate floor \(x^{.90+o(1)}\) times log powers is negligible.

## 4. Actual surviving signs

The uniform fixed-target reduction of the **same** \(G_N\) is now
\[
\begin{split}
G_N={}&-\!\!\sum_{\substack{s,u,\ m\ {\rm squarefree}\\v=1,\ j\in\{2,3\}}}
 C_s(u)1_{(su,N)=1}R_Z(m)\log m\\
&-\!\!\sum_{\substack{s,u,\ m\ {\rm squarefree}\\v>U,\ j\in\{1,2\}}}
 C_s(u)1_{(su,N)=1}R_Z(m)(\log M)S_U(v)
 +O_\delta(M_N L^{-.46}).                                           \tag{4}
\end{split}
\]
In the first line true prime \(u\) is favorable (nonpositive); true balanced-semiprime \(u\) is adverse (nonnegative). An absolute \(O(M_N)\) bound for the line follows from the same two-form upper: fix \(s\) and all but the largest macro prime, whose \(j-1\) product is at most \((1.5x)^{2/3}\), then sieve the true largest prime and actual rough \(u\) as in (3). The one or two fixed macro harmonics cost \(O(1)\), and the floor still has power reserve. This does not reach the strict .00659 whole-low allowance.

In the second line \(S_U(v)=-1\) on two true small primes with product \(>U\), so true prime \(u\) is adverse and true balanced-semiprime \(u\) favorable there. For squarefree three-prime \(v>U\), \(S_U(v)=-2+\#\{p_i p_h\le U:i<h\}\), and both signs occur as algebraic profiles. For higher ranks the full signed \(S_U(v)\) is intact. No sign on this second line, or on its combination with the first, follows from the quarter removal. Neither this cell nor the rest of the whole-low ledger is now bounded at the required threshold.

[check_same_cofactor_physical_macro_core.py](check_same_cofactor_physical_macro_core.py) tests the literal all-powers identity and rational exponent reserves independently.
