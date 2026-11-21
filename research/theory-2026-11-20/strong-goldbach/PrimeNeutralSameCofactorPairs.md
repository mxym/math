# Two genuine composite half-score signs at fixed target on the same true prime cofactor

This strengthens the aggregate [genuine short-prime half balance](GenuineShortPrimeHalfBalance.md) to an absolute bin-by-bin comparison for the **actual** four-prime source. The new score is prime-neutral, so neither sign witness below can be a prime. It deletes a particular balanced triprime term when inserted as a centered correction in the original signed row, but creates a certified positive debit on a different actual family. It does not bound that whole row or prove Goldbach.

## 1. Fixed-target same-cofactor statement

Keep \(N=2x\), \(L=\log x\), \(m=N-n\), and the literal true \(\mathcal Q_1\) source
\[
 n=s aP Q\in(x/2,x],\quad (n,N)=1,\quad
 x^{.10}<s<x^{.14},\quad x^{.010}<a<x^{.070},\quad
 P,Q<x^{.501}<aP .
\]
All four labels are primes; \(a,P,Q\) are distinct and \(P>x^{.431}>Q\), since \(Q<x^{.399}\) on the physical support. Thus the long cofactor \(A=sPQ\) determines all three of its labelled primes independently of varying \(a\). Use the same positive weight \(W_s(aPQ)\) (bounded above and below by absolute positive constants on all these rows), and write \(A_1(N)=\sum_{\mathcal Q_1}W_s(aPQ)\sim I_1x/(2L)\), \(M_N=\mathfrak S(N)x/(2L)\).

Fix \(B_0\ge1\) and an allowed lost fraction \(0<\eta<1\). There exists a sufficiently small fixed \(\kappa>0\) such that the following holds at every sufficiently large even \(N\). On each dyad \(a\sim Y\) partition its short axis into intervals of length at most \(Y/L^{B_0}\), using \(O(L^{B_0})\) bins. For all but an \(\eta\) fraction of the source **weight** over the actual physical tuples, each source tuple has at least
\[
                     c_\kappa Y/L^{B_0+4}
\]
actual positive and at least that many distinct actual negative alternatives in its own bin, all keeping the **same** \((s,P,Q)\). Each alternative is another true prime \(a'\) still satisfying \(\mathcal Q_1\). Both signs refer to the *same* exact score of the true reflected number \(m'=N-s a'P Q\). All these \(m'\) are squarefree, \(x^\kappa\)-rough **composites**. In particular this does not depend on any lower bound for reflected prime \(m'\) on a fixed long cofactor. If desired, a prescribed lost fraction of the unweighted source count also follows by decreasing \(\eta\), using the stated two-sided bound on \(W_s\).

Here is the prime-neutral score. With \(z=x^\kappa\), \(J=\lceil 1/\kappa\rceil\), set
\[
 \begin{gathered}
 u=1-2t,\quad f(t)=c_*u-\sum_{j=1}^J c_j u^{2j+1},\qquad
 c_1=(1-\kappa)/2,\quad
 c_j=\frac{\kappa}{2j(J-1)}\ (j\ge2),\quad c_*=1+\sum_j c_j,\\
 \mathcal J_f(m)=\sum_{d\mid m,\ d<\sqrt m}\mu(d)
                  [f(\log d/\log m)-1].
 \end{gathered}
 \tag{1}
\]
This slightly different choice of coefficients from the prior note allots only \(\kappa\) of the derivative-normalization mass to its higher powers. In fact \(\sum 2j c_j=1\), so \(f(0)=1\), \(f'(0)=0\), \(f(1/2)=0\), and \(f\) is odd about its midpoint. For a prime \(m\), its only short divisor is 1 and the score is identically zero. On the half interval \(0\le f\le1\), and
\[
                     3t\le -f'(t)\ll t+\kappa .
 \tag{2}
\]
The lower bound uses \(c_1\ge1/4\) in \(-f'=2\sum_j(2j+1)c_j(1-u^{2j})\). For the upper use \(1-u^2=4t(1-t)\) and \(\sum_{j\ge2}(2j+1)c_j\le2\kappa\). On \([0,1/2)\), for each \(2\le r\le2J\), \((-1)^r f^{(r)}(t)<0\). This follows termwise after the linear term disappears: at least one displayed higher odd power has degree \(\ge r\) and is strictly positive after differentiation in \(u>0\).

## 2. Actual weighted L1 bounds and conversion to cofactor coverage

For a cell \(i=(A,I)\) within an \(a\)-dyad, put
\[
 U_i=\sum_{a\in I,\,\mathcal Q_1}W_s(aP Q),\qquad
 Z_i=\sum_{a\in I,\,\mathcal Q_1,\,m\ z\text{-rough sf}}
        W_s(aP Q)\log m\,\mathcal J_f(m).
\]
Write \(\rho\) for Dickman's function, \(V_N(z)=\prod_{p\le z,p\nmid N}(1-1/(p-1))\), and \(S=.004/\kappa\). There is a positive model multiplier
\[
 b_N=L V_N(z)\left[-\int_0^{1/2}\rho(t/\kappa)f'(t)\,dt
                             -\rho(1/(2\kappa))\right]
           \asymp \kappa\mathfrak S(N)
 \tag{3}
\]
such that
\[
 \sum_i|Z_i-b_N U_i|\ll L V_N(z) A_1(N)
       \left(\kappa^{-1} S^{-S/2}+o_{\kappa,B_0}(1)\right).
 \tag{4}
\]
Here \(b_N\asymp\kappa\mathfrak S(N)\) holds for all sufficiently small fixed \(\kappa\) and all large \(x\), with the constants absolute. Indeed the bracket has lower bound \(\tfrac32\kappa^2-\rho(1/(2\kappa))\) by (2) and the fact \(\rho=1\) on \([0,1]\); it is \(O(\kappa^2)\) using (2), \(\int_0^\infty(1+t)\rho(t)\,dt<\infty\), and rapid decay of \(\rho\). Also \(L V_N(z)\sim e^{-\gamma}\mathfrak S(N)/\kappa\), uniformly in target.

To prove (4), take any weights \(|\alpha_i|\le1\) on the whole cells. On each short-prime bin they act only on the long coefficient, so the [Fouvry Corollary 1](https://www.numdam.org/article/ASENS_1987_4_20_4_617_0.pdf) proof in §2 of the prior note applies **with the same errors uniformly in \(\alpha_i\)**: the source still has its independent SW prime \(a\), all cutoff and moving half edges are treated by the same fine rectangles and physical divisor strips, and all composite sieve moduli are at most \(x^{.504+o(1)}\). The bin endpoints are kept as independent prime intervals and cost only a fixed log-power multiplicity. Split signs of \(\alpha_i\mu(d)(f(t_d)-1)\) when applying upper and lower sifting weights; the sieve error is then bounded by the absolute harmonic measure \(O(1/\kappa)\), since the coefficient has bounded sup norm and variation on the half interval. The short harmonic measure converges to \(d\rho(t/\kappa)\), including the atom at 0. The endpoint test is now \(f(1/2)-1=-1\), which gives the explicit endpoint \(-\rho(1/(2\kappa))\) in (3). Endpoint shifts of each frozen half divisor have mass \(o_\kappa(1)\) in that harmonic measure, since the limiting cumulative function is continuous at \(1/(2\kappa)>0\); actual changes in the progression sum are paid by the original physical strips even though the test does not vanish there. Finally take \(\alpha_i=\operatorname{sgn}(Z_i-b_N U_i)\) to prove (4), not a bound for each individual modulus.

For negative alternatives count genuine marked tuples at the same physical source with
\[
 x^{.5+.1\kappa}<p<x^{.5+.2\kappa},\qquad
 x^{1.1\kappa}<e<x^{1.2\kappa},\qquad p,e\text{ prime},\quad pe\mid m,
 \quad m\ z\text{-rough and squarefree}.
 \tag{5}
\]
Denote the weighted count, including the marks, by \(T_i\) on cell \(i\). The same argument with arbitrary cell selectors, now with no signed \(d\)-summation, gives
\[
 \sum_i|T_i-v_N U_i|\ll v_N A_1(N)[S^{-S/2}+o_{\kappa,B_0}(1)],\qquad
 v_N=V_N(z)\Big(\sum_{p\text{ in }(5)}\frac1{p-1}\Big)
                    \Big(\sum_{e\text{ in }(5)}\frac1{e-1}\Big)
          \asymp \frac{\mathfrak S(N)}L .
 \tag{6}
\]
All moduli \(pew\le x^{.504+1.4\kappa}\) fit the fixed Fouvry margins for sufficiently small \(\kappa\), with \(w\) split off uniquely by smoothness and \(p,e\) by their disjoint bands. The endpoint/label masks are the same exact ones as in the prior note. Excluding markers dividing the actual \(nN\) removes only \(o_\kappa(1)\) of each harmonic sum by their polynomial lengths and the bounded possible number of such polynomial prime divisors. Lower and upper fundamental-lemma estimates apply separately to signs of cell selectors; relative error is \(O(S^{-S/2})\) rather than the larger harmonic \(d\)-loss in (4). The harmonic sizes in (6) are respectively \(\asymp\kappa\) and \(\asymp1\) by the prime number theorem. Squareful rough outputs in either calculation cost \(O(x^{1-\kappa+o(1)})\) before log weights, harmless even with tuple multiplicity and all bin choices.

Every actual output on (5) has \(p>\sqrt m\) for large \(x\), and \(pe<x\) (as \(\kappa\) is sufficiently small), so \(u_0=m/p\) has at least two prime factors. The short divisor list of \(m\) is exactly the complete divisor list of \(u_0\). Its constant Möbius sum is zero, and its signed \(f\)-sum is the full mixed finite difference of order \(r=\Omega(u_0)\ge2\) sampled inside \([0,\log u_0/\log m]\subset[0,.5-.09\kappa]\) for large \(x\). By the derivative sign after (2) it is uniformly \(\le-c(\kappa)<0\): all the log factor lengths exceed \(.95\kappa\), and \(r\) ranges through a finite range \(2\le r\le (1+o(1))/\kappa<2J\). This evaluates the sign on every actual allowed rank, without a primality or parity assumption on the cofactor.

Choose \(\kappa\) small enough for the right side of (4) to be less than \((\eta/8)b_N A_1(N)\) and that of (6) less than \((\eta/8)v_N A_1(N)\) for large \(x\). This is possible because the required relative error in (4) is \(O(\kappa^{-3}S^{-S/2})+o_\kappa(1)\). Cells failing \(Z_i\ge b_N U_i/2\) or \(T_i\ge v_N U_i/2\) then carry combined source weight at most \((\eta/2) A_1(N)\), by summing their respective pointwise deficit lower bounds. Also discard cells with \(U_i\le Y/L^{B_0+3}\) on each \(a\)-dyad. There are \(O((x/Y)L^{B_0})\) cells on that dyad, before genuine primality restrictions, so all such discarded cells across the \(O(L)\) dyads carry only \(O(x/L^2)=o(A_1(N))\) weight.

For each remaining cell, the positive part of its true half-score sum is at least \(b_N U_i/2\), and the contribution of one \(a'\) is at most \(O_\kappa(L)\) since \(m'\) is rough squarefree of bounded rank and \(0<W_s\le1\). Thus there are \(\gg_\kappa U_i/L\) positively scored distinct \(a'\). The actual marked negative tuples have weighted count at least \(v_N U_i/2\); each possible \(a'\) carries at most \(O_\kappa(1)\) marks, giving the same count lower for negatively scored distinct \(a'\). The two sign sets are disjoint and cannot include primes on the reflected side by (1). Uniformity in \(N\) uses \(\mathfrak S(N)\ge2C_2>0\). This proves the cofactor claim at its actual source-weight normalization.

## 3. What this score removes, and the exact debit it creates

On every genuine reflected squarefree triprime with all three factor exponents \(t_i<1/2\), the only short divisors are the unit and the three primes. The choice (1) has \(f(t)\le F_3(t)=1-6t^2+4t^3\) on \([0,1/2]\): write it as the convex combination with weights \(2j c_j\) of \(u+u(1-u^{2j})/(2j)\), and use \((1-u^{2j})/j\le1-u^2\). Consequently
\[
 \mathcal J_f(m)=3-\sum_{i=1}^3 f(t_i)
          \ge 3-\sum_{i=1}^3 F_3(t_i)
          =2-12t_1t_2t_3\ge14/9 .
 \tag{7}
\]
The support used in the original positive budget, all reflected factors in \((x^{.25},x^{.45})\), is a strict instance. There \(C(m)=\log m\) exactly for large \(x\), and every such factor is above \(z\). Subtracting \((9/14)\log m\,\mathcal J_f(m)\) on the rough squarefree rows eliminates this entire particular positive group. This can be a **centered** comparison at fixed target by adding back \((9/14)b_N A_1(N)\) using (4); the model magnitude is \(O(\kappa I_1 M_N)\) and the remaining analytic error is \(O(\kappa^{-2} S^{-S/2}M_N)+o_\kappa(M_N)\), both made small by taking a sufficiently small fixed \(\kappa\). Pointwise the score does not change any actual reflected prime atom. This is not a global improvement of the original budget.

Indeed the negative cohort (5) illustrates a real new debit on the same signed comparison. On it \(u_0=m/p<x^{.5-.09\kappa}\), all its prime factors exceed the reflected \(V=\exp(L^\sigma)\), and \(u_0\) is composite and squarefree. Thus every divisor \(d>U=\sqrt x/\exp(4L^\sigma)\) in the original \(C\) must contain \(p\); conversely any \(d=p c\) satisfies both large cutoffs. Expanding the exact \(C\) on this support gives
\[
 C(m)=-\sum_{\ell\mid u_0}\Lambda(\ell)
                   \sum_{c\mid u_0/\ell}\mu(c)
      =-\Lambda(u_0)=0 .
]
After the proposed subtraction the same rows now have **positive** grouped weight at least \((9/14)c(\kappa)W_s(q)\log m\). By (6) their actual occupancy has weighted lower of order \(\mathfrak S(N)x/L^2\) on the whole \(\mathcal Q_1\) source (with bounded mark multiplicity), so this debit is a strictly positive multiple of \(M_N\) at *each* sufficiently large prescribed target. No equality or favorable bound for its global balance with the eliminated balanced cohort is shown. In particular one cannot report a .010 signed upper, a lower for the original prime atom, an estimate on \(\mathcal Q_2\), or binary Goldbach from this prime-neutral cofactor comparison.

A simple pointwise explanation for the tradeoff: for any prime-neutral continuous half kernel \(k\) with \(k(0)=k'(0)=0\), keeping its score nonnegative on all two-factor cores \(ab\) of giant triprimes would require \(k(t_a+t_b)\ge k(t_a)+k(t_b)\) for every \(t_a+t_b<1/2\). That would give \(k(t)\ge j k(t/j)\to0\), so the balanced triprime score \(-\sum k(t_i)\) could never be positive. This is only a pointwise size-kernel rigidity observation, not a lower bound for the unpriced signed complement.
