# An opposite-sign half switch with negligible actual rank three

Let \(x=N/2\), \(L=\log x\), \(I=(x/2,x]\), \(n=sq\), \(m=N-n\), and \(s\sim S=x^\alpha\) an actual prime, \(.10\le\alpha\le .14\). Retain the literal semiprime weight
\[
 W_s(q)=K_{P_3}(sq)=(1-t)(1-2t)^2,\qquad t=\log s/\log(sq).
\]
All rows below retain \(sq\in I\) and \((sq,N)=1\). For the artificial quotient row take \(\kappa_s=1\), or an independent smooth \(s\)-weight as allowed in [FullScaleConvolutionBV.md](FullScaleConvolutionBV.md). For the actual rank-three result take \(\kappa_s=1\) (fixed bounded weights are harmless).

Fix \(0<\eta<1\), put \(H=\exp(L^\eta)\), and use the true reflected cutoffs
\[
 U=\sqrt x/H^4,\qquad V=H,\qquad Q=\sqrt x/H^2,\qquad B=\sqrt x\,H,\qquad Z=Z(m)=m/B.
\tag{1}
\]
These retain the whole high reflected coefficient
\[
 C(m)=\sum_{\substack{d\ell\mid m\\d>U,\ \ell>V,\ d\ell>Q}}\mu(d)\Lambda(\ell).
\]
The two exact signed long pieces at the new forward threshold are
\[
 P(m)=-\!\!\sum_{\substack{a\mid m\\a<Z}}\!(\mu*\Lambda_{>V})(a),
 \qquad
 J(m)=\!\!\sum_{\substack{a\mid m\\a<Z}}\!
       \big\{\mu_{>U}(a)\log(m/a)-(\mu_{>U}*\Lambda)(a)\big\}.
\tag{2}
\]
In particular the long \(\Lambda\)-piece \(J\) is not automatically empty at the new threshold \(B\). Define the **opposite-sign** alternative \(C^\dagger=C+P-J\).

For the actual quotient, let \(\mathcal T_{\rm p}(F)\) denote the sum of \(\kappa_s W_s(q)F(N-sq)\) over the true primes \(s,q\) above. For the separate reverse-opened quotient, let
\[
 \mathcal T_{\rm v}(F)=
   \sum_{s,q}\kappa_s W_s(q)F(N-sq)\frac{C_q^{\rm hi}(q)}{\log q},
 \qquad
 C_q^{\rm hi}(q)=\sum_{\substack{rk\mid q\\r>x^{.070},\ k>x^{.010},\ rk>x^{.080}}}
                        \mu(r)\Lambda(k).
\tag{3}
\]
Here \(q\) in \(\mathcal T_{\rm v}\) is an integer, not a prime. Let \(\mathcal M\) be the exact matched semiprime reference (3) in [DoubleSwitchedMain.md](DoubleSwitchedMain.md). Then for every fixed \(D>0\),
\[
\begin{array}{ll}
 \mathcal T_{\rm p}(P)=-\mathcal M+O_D(xL^{-D}),&
 \mathcal T_{\rm p}(J)=O_D(xL^{-D}),\\
 \mathcal T_{\rm v}(P)=O_D(xL^{-D}),&
 \mathcal T_{\rm v}(J)=O_D(xL^{-D}).
\end{array}
\tag{4}
\]
In fact the \(J\) estimate in the second line holds with any independent divisor-bounded \(q\)-weight in place of \(C_q^{\rm hi}(q)/\log q\), with the same stated SW hypothesis on the independent short-prime coefficient. No such assertion is made for \(P\).

With exact original \(\kappa_s=1\), summing all dyads in the stated \(s\)-band gives the following genuine true-prime rank result, uniformly in each \(N\):
\[
 \sum_{\substack{s,q\ {\rm prime},\ sq\in I,\ (s q,N)=1\\
                  \Omega(N-sq)=3}}
      |W_s(q) C^\dagger(N-sq)|
       \ll_{\eta} \frac{\mathfrak S(N)x}{L^{2-\eta}}(\log L)^2
       +o\!\left(\frac{\mathfrak S(N)x}{L}\right).
\tag{5}
\]
Here \(\Omega\) counts with multiplicity, including true repeated-prime cases. Thus actual rank three is \(o(M_N)\) for \(M_N=\mathfrak S(N)x/(2L)\) in this alternate coefficient. In the true-prime row the overall sign threshold changes:
\[
                    \mathcal T_{\rm p}(C)
                   =\mathcal T_{\rm p}(C^\dagger)+\mathcal M+O_D(xL^{-D}).
\tag{6}
\]
One cannot credit the \(o(M_N)\) in (5) as a positive budget for the old signed inequality: for a target \(\mathcal T_{\rm p}(C)\le .010 M_N\), the new target is \(\mathcal T_{\rm p}(C^\dagger)\le -\mathcal M+.010 M_N+O_D(xL^{-D})\). In particular the comparable centered artificial row in (4) must not be substituted into (5).

## 1. Exact long identities and the moving cutoff in full-scale BV

Use the formal actual \(P_B,H_B\) HB decompositions of [SwitchedLongFreeReverseColumns.md](SwitchedLongFreeReverseColumns.md) now on \(d,\ell\). The inputs are \(<x\): \(d\le m/V\) and \(\ell\le m/U\), with \(m\le3x/2\). The support proof for the reciprocal HB identity applies because the product of the short cofactors of a marked \(b>B\) is \(\le m/B\ll x^{.5}\). Also \(B^2>m\) so there is never a double marked slot in a single actual tuple. If a long free slot occurs in \(d=t b\), both \(d>U\) and \(d\ell>Q\) are automatic; retain \(\ell>V\) and combine \(-\mu_2(t)\) with the original free \(h\), using \(\mu_2*\mathbf1=\mu\). With \(a=t\ell h\), this is exactly \(P\). If it occurs in \(\ell=t b\), then \(\ell>V,d\ell>Q\) are automatic; retain \(d>U\) and combine the coefficient \(\mu(t)\log b-(\mu*\Lambda)(t)\) with \(h\). This is \(J\) with \(a=d t h\). The strict distinction \(b>B\) produces \(a<Z\) exactly. Independent cutoffs on the original \(d,\ell,h\) would not in general survive these combinations, so the theorem uses the complete reflected high coefficient before other selections.

For both terms the switched progression is the true \(n=sq\equiv N\bmod a\), with \(a\le(3/2)\sqrt x/H\), not a progression at the single quotient scale \(x/S\). This is within the full-scale generalized BV range \(x^{1/2}/L^C\) from [Maynard I, Lemma 8.9](https://ora.ox.ac.uk/objects/uuid%3A39a52f47-3770-4ddd-b7a2-b2a4f7300931/files/srj4305733), for every requested log reserve; all choices in (1) are deliberately subpower. The SW input is the genuine \(q\)-prime in \(\mathcal T_{\rm p}\), and the genuine smooth \(s\)-prime factor in the second row. Use the factor-wise physical unit mask and sharp product control from [FullScaleConvolutionBV.md](FullScaleConvolutionBV.md). If \(a\) is nonunit modulo \(N\), \(a\mid m\) is impossible on the physical \((n,N)=1\) support. No \((a,sq)=1\) condition is needed on the actual progression beyond that: the centered reduced mean independently includes \((a,n)=1\), as the source prescribes. Thus its exact harmonic mask is \(F=Nn\).

For clarity the new cutoff \(a<m/B\) in the \(n\)-interval is not handled by assuming a maximal theorem with a different moving cutoff in each modulus. Mesh the physical \(n\)-interval with lengths \(O(x L^{-F_0})\), and for each retained mesh rectangle with representative \(n_0\) retain \(a<(N-n_0)/B\). This leaves a fixed subset of outer moduli, independent of the product variables in that application of absolute BV. Any erroneous physical term has \(a\mid m\) and \(|m-Ba|\ll xL^{-F_0}\). Then \(a\asymp x/B\), and \(b=m/a\) lies within \(O(BL^{-F_0})\) of \(B\). There are at most \(O(xL^{-F_0}+x/B)\) such physical \(m\) even before weighting. Use global divisor moments and the exact divisor envelope at \(m,n\), as in the ordinary product edge proof. In the centered mean, for any fixed physical \(n\), the possibly erroneous \(a\) have
\[
  \sum_{|Ba-m|\ll xL^{-F_0}}\frac{1+\log a}{\phi(a)}
                 \ll L^C(L^{-F_0}+B/x),
\]
using \(a\asymp x/B\) and \(a/\phi(a)\ll L^C\). This also has arbitrary log reserve after summing over \(n\). The \(J\) log weight splits exactly \(\log(m/a)=\log m-\log a\); the moving part \(\log m\) has smooth physical variation, absorbed in the same mesh. All coefficients at fixed \(a\) are \(O(L)\). This proves that one may use the true central reduced mean below with the moving \(Z\).

## 2. Two distinct harmonic centers

Uniformly for polynomial \(F=Nn\), the finite coprime \(\mu/\phi\) identities (11) of [UnmarkedSemiprimeWholeTypeI.md](UnmarkedSemiprimeWholeTypeI.md) give
\[
 \sum_{\substack{a<Z\\(a,F)=1}}
           \frac{-(\mu*\Lambda_{>V})(a)}{\phi(a)}
                   =-\mathfrak S(F)+O_D(L^{-D}).
\tag{7}
\]
Indeed \(\mu*\Lambda=-\mu\log\), and the short \(\Lambda_{\le V}\) portion is negligible by fixing \(\ell=p^b\), using \(\phi(d)\phi(\ell)/\phi(d\ell)=1-p^{-1}1_{p\mid d}\), then summing the two exact masked harmonic tails at \(Z/\ell\) of polynomial size. Terms coprime to \(F\) are retained throughout.

For \(J\), its first summand in (2) has zero harmonic main because the values of both \(\mu/\phi\) moments at \(Z\) and \(U\) agree to arbitrary log accuracy. For the convolution \(\mu_{>U}*\Lambda\), subtract the \(\mu_{\le U}*\Lambda\) part from \(\mu*\Lambda\). The identity in §3 of [DoubleSwitchedMain.md](DoubleSwitchedMain.md) is still applicable even though \(Z/U\) is now subpower: for \(d\le U\), \(Y=Z/d\gg H^3\), and
\[
 \sum_{\substack{\ell\le Y\\(\ell,F)=1}}\frac{\Lambda(\ell)}{\phi(d\ell)}
  =\frac1{\phi(d)}\left(
       \log Y+C_F-\sum_{p\mid d}\frac{\log p}{(p-1)^2}
                      +O_D(L^{-D})\right).
\tag{8}
\]
The ordinary \(\Lambda(\ell)/\ell\) harmonic PNT has error decaying exponentially in a fixed positive power of \(\log Y\), hence \(O_D(L^{-D})\) for \(Y\gg H^3\). The absolutely convergent \(\Lambda/\phi-\Lambda/\mathrm{id}\) tail and the geometric prime-power tails for \(p\mid Fd\) have errors \(O(L^C/Y^c)\) for a fixed \(c>0\), by \(\log(Fd)=O(L)\); these likewise have arbitrary reserves. The overlap constant in (8) is the displayed exact prime-power sum. Multiplying by \(\mu(d)\) and summing at \(U\), the prime-dependent constant has negligible contribution: for \(p\le\sqrt U\) sum \(\mu(d')/\phi(d')\) with the mask \(Fp\) at \(d=p d'\) and limit \(U/p\); for \(p>\sqrt U\) the absolutely convergent \(p^{-2}\) tail is power-small. The \(\log Y\) term gives \(\mathfrak S(F)\) and the \(C_F\) term has zero main by the finite identities (11). Therefore \(\mu_{>U}*\Lambda\) has zero harmonic main. This proves the \(J\) estimates for both rows directly, and proves that the \(P\) row equals its weighted singular-series sum from (7) with a **minus** sign. Strict endpoints in \(a<Z\) change a bounded-index term of power-small mass in these finite harmonic evaluations.

## 3. Why the \(P\) center is different in the two rows

On the actual prime-quotient row, \(q\asymp x/S\) is prime with \(q\nmid Ns\) (unit domain, and \(q\ne s\) by size). Therefore the exact extra Euler factor \((q-1)/(q-2)\) in \(\mathfrak S(Ns q)\) may be replaced by 1 with power-small error. Ordinary PNT in \(q\) with the true \(W_s(q)\) gives \(-\mathcal M\) in (4).

On the artificial row we instead prove the required singular-weighted cancellation, not an assertion about actual prime \(q\). For fixed \(s\) let \(X=x/S\). On \((q,N)=1\) the exact series is
\[
 \frac{\mathfrak S(Ns q)}{\mathfrak S(Ns)}
    =\sum_{\substack{g\mid q\\(g,Ns)=1}}\xi(g),\qquad
 \xi(g)=\prod_{p\mid g}\frac{1}{p-2}\ \text{for squarefree \(g\) with \(2\nmid g\)},
\]
and 0 on other \(g>1\). Since \(\xi(g)\ll\tau(g)^C/g\), for \(G=L^J\) the tail \(g>G\) in the \(q\asymp X\) sum, before \(\mathfrak S(Ns)\), is
\[
 \ll \sum_{G<g\ll X}\xi(g)\tau(g)\frac{X}{g}\,L
                 \ll X L G^{-1/2}.
\tag{9}
\]
Here \(|C_q^{\rm hi}(q)|/\log q\le\tau(q)\): each von Mangoldt label can have multiple eligible \(r\)'s. For \(g\mid q\), \(\tau(q)\le\tau(g)\tau(q/g)\), and the sum over \(q/g\ll X/g\) of its divisor weight is \(O((X/g)L)\), even near the upper endpoint. The final tail uses \(\sum_g\tau(g)^{C+1}/g^{3/2}<\infty\). Thus \(J\) large depending on the reserve suffices, including after multiplying by the singular factor and summing \(s\).

For \(g\le G\) it suffices to test \(C_q^{\rm hi}(q)\) on an arbitrary interval in \(q\asymp X\), with \(g\mid q,(q,N)=1\). The true \(W_s(q)/\log q\) is handled by partial summation. Reassemble the exact \(C_q^{\rm hi}\) as \(\Lambda(q)\) minus its short \(\mu_{\le U_q}*\log\), plus its short \(\mu_{\le U_q}*\Lambda_{\le V_q}*\mathbf1\), minus its short \((r>U_q,k>V_q,rk\le E)\) product. Here \(U_q=x^{.070},V_q=x^{.010},E=x^{.080}\). A short divisor \(e\) requires \((e,N)=1\); for \(g\mid q,e\mid q\), the unit-on-\(N\) CRT gives density \(\phi(N)/(N\operatorname{lcm}(e,g))\) and floor \(O(\tau(N))\). The entire floor cost \(O(E x^{o(1)})\) is much smaller than \(X L^{-D}\), even after the fixed log sums. For the first short piece its exact harmonic factor before \(1/g\) is
\[
 \sum_{\substack{d\le U_q\\(d,N)=1}}
       \frac{\mu(d)(d,g)}{d}\log(q/d).
\]
Expand \((d,g)=\sum_{f\mid(d,g)}\phi(f)\), and write \(d=f w\). Squarefreeness enforces \(\mu(d)=\mu(f)\mu(w)1_{(w,f)=1}\). For each \(f\mid g\), the uniform ordinary coprime Mertens moments (8) of [SwitchedLongFreeReverseColumns.md](SwitchedLongFreeReverseColumns.md) at the polynomial endpoint \(U_q/f\) give
\[
       \frac{\mu(f)\phi(f)}{f}\frac{Nf}{\phi(Nf)}
                   +O_D(L^{-D})
            =\mu(f)\frac N{\phi(N)}+O_D(L^{-D})
\]
with arbitrary reserve; \((N,f)=1\). Thus the true continuum mean for this first short piece is \(1_{g=1}\), including the density \(\phi(N)/(Ng)\), not a nonzero mean on every multiple progression.

In the other two short pieces fix the actual von Mangoldt argument \(k\), and use, since \(g\) is squarefree,
\[
                       (rk,g)=(k,g)(r,g/(k,g)).
\]
Expand the second gcd as before into \(f\mid g/(g,k)\) and sum pure harmonic \(\mu(w)/w\) with the exact \((w,Nf)=1\) mask. The full short \(r\le U_q\) endpoint or both nonempty endpoints of the high \(r>U_q\) short-product interval are polynomial after division by \(f\le L^J\). These means are log-small. The possible factor \((k,g)\), cutoff \(g\) and their divisor multiplicity have only fixed log costs. Finally \(\Lambda(q)\) contributes the ordinary interval length if \(g=1\), after PNT and omitting \(O(L^2)\) prime powers of prime factors of \(N\). When \(g>1\), an ordinary prime multiple of \(g\) would be \(q=g\), outside the range \(q\asymp X\gg G\); proper prime-power multiples have base \(p\mid g\), at most \(O(L^2)\) such \(q\) and \(O(L^3)\) total log weight. This matches the first short center exactly and leaves only \(O_D(X L^{-D})\) after summing \(g\). With (9) this proves the artificial-row \(P\) estimate in (4), retaining the original \(1/\log q\). For (6) there is no use of that second row.

## 4. Exact rank formula including all cutoff errors

The following literal identity holds for every \(m\) on the central band. Define
\[
\begin{split}
 E_H(m)&=\sum_{\substack{d\ell\mid m\\d>U,\ d\ell<Z}}\mu(d)\Lambda(\ell),\\
 E_C(m)&=\sum_{\substack{d\ell\mid m\\d>U\\\ell\le V\ {\rm or}\ d\ell\le Q}}
                            \mu(d)\Lambda(\ell),\\
 E_P(m)&=\sum_{\substack{a\mid m\\a<Z}}(\mu*\Lambda_{\le V})(a).
\end{split}
\]
Then
\[
 C^\dagger(m)=
    \sum_{\substack{d\mid m\\d\ge Z}}\mu(d)\log(m/d)
   +\sum_{\substack{a\mid m\\a< Z}}\mu(a)\log a
   +E_H(m)-E_C(m)+E_P(m).
\tag{10}
\]
The logical union in \(E_C\) counts the two cutoff failures once. To prove (10), first introduce the full divisor identity \(\sum_{\ell\mid m/d}\Lambda(\ell)=\log(m/d)\) in \(C\) and subtract its exact omitted union. In \(P\), use \(-\mu*\Lambda=\mu\log\). In \(-J\), remove exactly the \(\mu(d)\log(m/d)\) with \(U<d<Z\), valid since \(Z>U\), and add the \(E_H\) remainder. This derivation handles all integer endpoints and prime powers literally.

If \(m\) is squarefree of odd rank, complement pairing in (10) gives the main part
\[
                         -\!\sum_{\substack{a\mid m\\Z\le a\le B}}\mu(a)\log a.
\tag{11}
\]
The interval is genuinely the **closed** \([m/B,B]\), invariant under \(a\mapsto m/a\); each pair has opposite \(\mu\) and \(|\log a-\log(m/a)|\le\log(B/Z)\ll\log H\). Each error term in (10) is supported on small \(\Lambda\)-arguments: in \(E_H\), \(\ell<Z/U\ll H^3\); in \(E_C\), \(\ell\le V\) or \(\ell\le Q/U=H^2\); in \(E_P\), \(\ell\le V\). Thus the actual odd-squarefree coefficient has absolute bound \(O(\tau(m)^2\log H)\).

For rank three \(m=p_1p_2p_3\) with distinct primes, the pointwise formula may also be given as
\[
 C^\dagger(m)=
 \sum_{i:\,Z\le p_i\le B}(2\log p_i-\log m)
  -\sum_{\substack{i\ne j\\p_i>U,\ p_i p_j<Z}}\log p_j
  -E_C(m)+E_P(m).
\tag{12}
\]
The first sum arises from each singleton and its paired complementary product; this includes any possibility of more than one prime in the neck. In \(E_H\) the divisor \(d\) can only be the single \(p_i\): selecting a two-prime \(d\) and its only remaining \(\ell\) gives product \(m>Z\). The negative sign in the second sum is therefore exact. The remaining two signed cutoff corrections are the exact piecewise terms just defined, not approximated. More explicitly, \(E_C\) sums \(-\log p_j\) for \(d=p_i>U\) whenever \(p_j\le V\) or \(p_i p_j\le Q\), and \(+\log p_j\) for the two-prime complementary \(d>U\) if \(p_j\le V\). In \(E_P\), each small \(p_j\le V\) contributes \(+\log p_j\) at \(a=p_j<Z\) and \(-\log p_j\) at each \(a=p_j p_i<Z\). Thus all shapes with both the neck and the tiny-prime cut corrections absent have **nonpositive** coefficient, with exact zero if the second sum is absent too. General positivity (if present) is bounded by \(O(\log H)\); the estimate includes all actual moving threshold comparisons. For rank three the divisor bound is absolute.

If \(m=p^2r\) with \(p\ne r\), either its repeated \(p>H^4\), a sparse case below, or \(p\le H^4\). In the latter case \(r>B\), \(p^2<Z\), and the only nonzero Möbius divisors are \(1,p,r,pr\). The first two sums in (10) total exactly \(-2\log p\). In \(E_H\) there is no term: \(d>U\) forces \(r\mid d\) among those divisors. In \(E_C\) and \(E_P\) the only possible small \(\Lambda\)-arguments are \(p,p^2\), costing \(O(\log p)\) in total (including if \(p\) or \(p^2\) falls on a cutoff). Thus \(|C^\dagger|\ll\log p\) absolutely, not merely \(O(\log H)\), on this case. The \(p^3\) shape is part of the repeated-prime \(p>H^4\) case for large \(x\). The number of physical \(m\le 3x/2\) divisible by any \(p^2\) with \(p>H^4\) is \(O(x/H^4)\), by the simple \(\sum_{k>H^4}1/k^2\) bound. Global physical divisor moments show that the weight of all these actual terms is \(O_D(xL^{-D})\), even after all allowed \(s,q\).

## 5. Rank-three normalization in the real prime row

For distinct prime factors of \(m\), fix its two least primes \(p,t\) and the true prime \(s\); let \(\ell\) be the largest factor, required prime. Set \(u_0=p t\). On physical unit support \((u_0,N)=1\), \((s,N)=1\), and \((s,u_0)=1\), since \(s\mid u_0\) would give \(s\mid m,n\) and hence \(s\mid N\). Thus \(\ell\equiv N\overline{u_0}\bmod s\) and after writing \(\ell=\ell_0+s v\), \(q=(N-u_0\ell_0)/s-u_0 v\) is a second affine form. The free \(v\) interval has available length \(Y\asymp x/(s u_0)\ge x^{.19+o(1)}\), because the product of the two least factors is at most \(m^{2/3}\). Extra largest-factor inequalities only shorten this interval. Both sought primes are above \(Y^{1/100}\). At a prime not dividing \(N s u_0\) these two forms have different roots, and at primes dividing \(N s u_0\) only one root: when a coefficient is nonunit its constant is a unit, whereas at a unit coefficient prime dividing \(N\) the roots coincide. At \(2\) this is one root by even \(N\) and the unit mask. The uniform version of the classical Selberg bound needed here follows directly from [Tao's sieve notes, Theorem 30](https://terrytao.wordpress.com/2015/01/21/254a-notes-4-some-sieve-theory/comment-page-1/). To make uniformity in \(N\) explicit, put \(R=Y^{1/100}\), let \(h(p)=\omega(p)/(p-\omega(p))\) with the exact root count \(\omega(p)\), and extend \(h\) to squarefree integers multiplicatively, zero on other integers. Take the fixed comparison \(h_*(2)=1,\ h_*(p)=2/(p-2)\) for odd \(p\). At each odd exceptional prime choose \(k(p)=h_*(p)-h(p)\ge0\), and \(k(p)=0\) elsewhere, again extended multiplicatively on squarefree integers. Then \(h_*\le h*k\) pointwise, with equality on squarefree numbers, and
\[
 \sum_{d\le R}h_*(d)\le \left(\sum_{d\le R}h(d)\right)
    \prod_{\substack{p\mid N s u_0\\p>2}}
    (1+h_*(p)-h(p))\ll \mathfrak S(Ns u_0)\sum_{d\le R}h(d).
\]
For the inequality use
\(1+h_*(p)-h(p)=((p-1)/(p-2))(1+1/(p-1)^2)\).
The fixed comparison sum is \(\gg\log^2R\) by the fixed dimension-two divisor Euler product, as in the proof of Tao's Theorem 32 with fixed exceptional set \(\{2\}\). The remainder in Theorem 30 is \(O(R^2(\log R)^C)\), since each reduced squarefree modulus has at most \(2^{\omega(d)}\) remainder classes. This proves the uniform count
\[
       \ll \mathfrak S(N s u_0)\frac{x}{s u_0 L^2}
       \ll \mathfrak S(N)\frac{x}{s p t L^2}.
\tag{13}
\]
The second comparison uses at most three new distinct prime factors \(s,p,t\), each with local multiplier \((p-1)/(p-2)\le2\). There is no independence assumption on the two affine primes. In the \(p^2r\) nonsparse case use \(u_0=p^2\) and the same two forms; \(Y=x/(s p^2)\) is even longer. Nonunit coincidences similarly leave no term.

The complete \(s\)-band has \(\sum_s1/s\ll1\). Summing (13) against the true exact bounded \(W_s(q)\) and (12) gives
\[
 \ll \frac{\mathfrak S(N)x \log H}{L^2}
                  \left(\sum_{p\le 2x}\frac1p\right)^2
 \ll \mathfrak S(N)x L^{\eta-2}(\log L)^2 .
\]
In the \(p^2r\) small-repeated-prime case, the \(\log p\) weight and \(1/p^2\) reduce the sum to the convergent \(\sum_p\log p/p^2\), costing \(O(\mathfrak S(N)x/L^2)\). Include the already negligible repeated-large-prime cases to prove (5). Since \(\eta<1\), this is \(o(M_N)\) uniformly in the true-prime weighted row. No such estimate against the artificial \(q\)-weight is claimed, and nothing here establishes a suitable one-sided bound for the other ranks in (6).

The subpower cutoff change is compatible with the earlier original expansions: \(UV\le Q<\sqrt x/L^D\) for any fixed desired \(D\), so the true-prime short terms use full-scale convolution BV. The \(d>U\) scale is polynomial and accommodates the same fixed reverse short-\(e\) Möbius BV as before. This note introduces no claim of an unconditional solution to binary Goldbach.

[Arneth's October 2026 cubic minorant](https://zenodo.org/records/23477014) has different coefficients, including a negative squarefree triple profile; [Chan's November 2026 preprint](https://aixiv.science/pdf/aixiv.261111.000001v1.0.pdf) uses parity-sensitive cancellations for another sieve coefficient. The point here is the exact opposite signs of the two long switches in the actual Vaughan row, plus the separate genuine-prime and artificial-quotient centers. No broad graded sign claim or priority for using parity is intended.
