# An unbalanced Type II region of the reflected Möbius term

This note removes a genuine but unbalanced part of the Type II remainder in [the reflected Möbius decomposition](DirectGoldbachReflectedMobiusTypeI.md). It does not estimate the remaining Type II terms or prove strong Goldbach.

Put \(X=N\), with \(N\) even. Use the fixed smooth interior test \(W(1-de/X)\) of that decomposition, with \(e>d\), \((d,N)=(d,e)=1\), and any existing upper cutoff on \(d\). For Vaughan cutoffs \(U,V_0\), write
\[
 \beta(b)=\sum_{\ell\mid b,\ \ell> V_0}\Lambda(\ell).
\]
The Type II weight on \(de+ab=N,\ a>U,\ b>V_0\) is
\[
 \mu^2(d)\mu(e)\mu(a)\beta(b)W(1-de/X)\log(e/d).
\]

**Proposition.** Under Dirichlet GRH, the part with \(d\le D,\ U<a\le A\) is
\[
 O_{\epsilon,W}\bigl(X^{1/2+\epsilon}D^{1/2} A(1+V_0)\bigr).
\]
Here the cutoffs are at least 1 and on the natural scales of the displayed sum. In particular, for \(U,V_0\le X^{1/8}\), the box \(D=X^{1/8},\ A=X^{1/4}\) costs \(O_{\epsilon,W}(X^{15/16+\epsilon})\); it still has \(a>U\). For \(d\) up to \(\sqrt X\), one obtains a power saving whenever \(A(1+V_0)\le X^{1/4-\delta}\), with \(\delta>0\) fixed.

**Proof.** Use the exact identity \(\beta(b)=\log b-\sum_{\ell\mid b,\ \ell\le V_0}\Lambda(\ell)\), retaining \(b>V_0\) in both sums. Fix \(d,a\), and in the second sum fix \(\ell\); take \(\ell=1\) in the log term. Then \(b=(N-de)/a\), and integrality and \(\ell\mid b\) are the single congruence \(de\equiv N\pmod{a\ell}\). If \((d,a\ell)>1\) there are no solutions since \((d,N)=1\). Otherwise the congruence is one progression \(e\equiv r\pmod{a\ell}\). The nonunit case is allowed: put \(g=(r,a\ell)\) and \(e=gt\); \(g\) must be squarefree, and the remaining progression in \(t\) is reduced modulo \(a\ell/g\). The Möbius weight becomes \(\mu(g)\mu(t)\) with the added condition \((t,g)=1\). The conditions \((t,gd)=1\) can be included by inducing the characters to a common multiple bounded by a fixed power of \(X\). The uniform Möbius prefix estimate proved in the linked Type I note and character orthogonality give \(O_\epsilon((X/d)^{1/2}X^\epsilon)\) on this progression. The support and \(e>d,\ b>V_0\) impose interval restrictions; the weights \(W(1-de/X)\log(e/d)\), and in the log term also \(\log((N-de)/a)\), have sup norm and total variation at most polylogarithmic in \(X\). Partial summation therefore gives the same bound after adjusting \(\epsilon\). Sum over \(a,\ell,d\), using \(\sum_{\ell\le V_0}\Lambda(\ell)\ll V_0\) and \(\sum_{d\le D}d^{-1/2}\ll\sqrt D\).

There is also a separate unconditional deletion: \((de,ab)\ge X^\delta\) costs \(O_{\epsilon,W}(X^{1-\delta+\epsilon})\) in absolute value. Indeed \(g=(de,ab)\) divides \(N\), and for fixed such \(g\) there are at most \(X/g\) positions \(de\); at each position the two factorization counts and all weights cost \(X^{o(1)}\). Sum over \(g\mid N\). This includes the regions where any cross gcd between one of \(d,e\) and one of \(a,b\) is at least \(X^\delta\). It is a counting deletion, not cancellation. In particular, these bounds do not pay the balanced region with all four variables of order \(\sqrt X\) and small cross gcds.
