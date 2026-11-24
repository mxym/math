# Actual translated-marker transfer for the averaged G23 dispersion

Written research addendum, 2026-11-24. Independent of the proof of the [unmarked mean square](G23AverageWeightedDispersion.md). This extends only the mixed G23 statistic and its weighted dispersion, not other signed high terms.

Use that note's definitions \(P,L_P,y,z,J,A_P(k),\mathcal Q_P\). Write \(L=L_P\) below. Take a fixed \(M\) translated offsets \(j=2,\ldots,M+1\), the existing packets on exponents .105–.195 with grid step \(h=\log4/\log L\), fixed-width packet separation and fixed multiplicity \(K\), and the actual first-cover partition \(C=C_{>1}\) by the [existing translated-tag construction](SmallRadicalShortPrimeMixedParity.md). Thus for each physical \(n\), \(C(P,n)\) is either 0 or 1, because the true chosen pair \((j,H)\) has exactly the number of true tag factors counted by its denominator. This holds also when the shifted cofactor has a squared tag prime: this use is of the actual partition, not its squarefree reindexing. Write
\[
 A_{P,C}(k)=\sum_p W(p,k)c_p\,C(P,kp)R_y(P-kp)\lambda(P-kp),\qquad
 \mathcal Q_{P,C}=\sum_k kR_z(k)|A_{P,C}(k)|^2.
\]

## 1. True integer uncovered bound for every even \(P\)

For every fixed \(M,K\) and all sufficiently large even \(P\), without any assumption on its radical,
\[
 \mathcal E_P:=\sum_{n\in PJ}R_z(n)R_y(P-n)(1-C(P,n))
 \ll P\kappa_z V_y(P)L^{-M/200}+O_A(PL^{-A})
 \tag{1}
\]
for arbitrary fixed \(A>0\). Here \(\kappa_z=\prod_{\ell\le z}(1-1/\ell)\asymp L^{-.24}\) and \(V_y(P)=\prod_{\ell\le y,\ell\nmid P}(1-1/(\ell-1))\gg L^{-\delta}\) for even \(P\), by Mertens and the convergent product \(\prod_{\ell>2}(1-1/(\ell-1)^2)\). The factor at 2 never vanishes for even \(P\).

The greedy packing step used in the earlier cover argument says that each uncovered offset has every occupied grid point in the union of at most \(K-1\) anchored intervals of length \(1/(20K)\). Thus some choice of boxes forces at least \(.04/h-O(K)\) packets empty at each offset. For each fixed box choice let \(t_i\le M\) be the number of offsets requiring packet \(i\) to be empty. Each such choice specifies true avoided congruences \(n\not\equiv jP\pmod q\) for all packet primes \(q\) in packet \(i\) and their corresponding \(j\)'s. For packet primes \(q\) not dividing \(P\), \(q>M+1\) and these \(t_i\) residues are distinct and nonzero, so, conditional on \(n\not\equiv 0\pmod q\) which is already forced by \(R_z(n)\), the **exact** additional survival factor is \(1-t_i/(q-1)\). A packet prime \(q\mid P\) would give only the extra residue \(0\) for all offsets; this residue is already avoided by the true \(z\)-rough source. Thus dropping its extra packet conditions is equality on the source's existing support, not an assertion that such primes can create covered rows. Indeed if \(q\mid P\) and \(R_z(n)=1\), it divides none of the \(jP-n\). The lost reciprocal packet mass is at most
\[
 \sum_{\substack{q\ {\rm packet\ prime}\\q\mid P}}\frac1{q-1}
 \ll L e^{-cL^{.105}} .
\]
Originally each packet has reciprocal prime mass at least \(1/4\); the lower bound after omission is \(1/4-o(1)\) uniformly in the packet. The other rough local factors combine exactly into \(\kappa_z V_y(P)\): at \(\ell\le y\) the two residues \(0,P\) are distinct precisely when \(\ell\nmid P\), and at \(y<\ell\le z\) only \(0\) is forbidden apart from the packet refinements. This includes \(\ell\mid P\) at all sizes; primes \(>z\) impose no condition here.

Consequently the full CRT survival product for a fixed box choice is at most
\(\kappa_z V_y(P)\exp(-(1/4-o(1))\sum_i t_i)\).
There are \(O_{M,K}((\log L)^{M(K-1)})\) box choices, and \(\sum_i t_i\ge M(.04/h-O(K))\). Since \(.04/(4\log4)>1/200\), summing model masses with the strictly positive exponent margin gives \(O(\kappa_z V_y(P)L^{-M/200})\).

For the passage to true integer counts, use Bonferroni through \(\lfloor L^{.1}\rfloor\) bad prime events and one more. If \(\nu(\ell)\) is the exact number of forbidden residues at \(\ell\), then \(\nu(\ell)\le M+2\) and \(\sum_{\ell\le z}\nu(\ell)/\ell=O_M(\log L)\). The omitted model shell is factorially smaller than every \(L^{-A}\). At a retained squarefree modulus \(d\), the actual number of CRT classes is exactly \(\prod_{\ell\mid d}\nu(\ell)\le(M+2)^{\omega(d)}\), and
\(d\le \exp(O(L^{.34}))=P^{o(1)}\).
Their aggregate floor over the number of moduli, polynomial-in-\(\log L\) choices, and residue counts is \(P^{o(1)}\); the actual interval is \(PJ\) in each class. This proves (1) for every even \(P\). It does not prove a new marked Type I/II estimate at general radical.

## 2. Weighted square and conversion of exponents

Since \(C\) is an indicator, \(|1-C|^2=1-C\) exactly. With each \(k\) fixed, all at most \(O_J(P/k)\) available true slopes lie in \([aP/k,bP/k]\); Cauchy and \(|Wc_p|\le1\) give
\[
 \begin{aligned}
 \sum_k kR_z(k)|A_{P,C}(k)-A_P(k)|^2
 &\ll_J P\sum_{k,p:\,kp\in PJ}R_z(k)R_y(P-kp)(1-C(P,kp))\\
 &\ll_{\sigma,J} P\mathcal E_P
 \ll P^2\kappa_z V_y(P)L^{-M/200}+O_A(P^2L^{-A}).
 \end{aligned}
 \tag{2}
\]
The middle sum is still restricted to the true slope range \(P^\sigma<p\le D_P\); \(p>z\) implies \(R_z(k)=R_z(kp)\). Each \(n< P\) has at most \(1/\sigma\) distinct prime divisors exceeding \(P^\sigma\), so this regrouping incurs only a constant loss.

The original sufficient one-sided dispersion budget is \(P^2V_y(P)^2/(\kappa_z L^5)\). Dividing the explicit main bound in (2) by that budget gives \(O(L^{5-.48+\delta-M/200})\). Thus **fixed \(M\ge1000\)** pays the squared marking difference to \(o\) of that budget uniformly in every even \(P\); choose \(A\) large for the last term. By \(\mathcal Q_{P,C}\le2\mathcal Q_P+2\sum_k kR_z(k)|A_{P,C}-A_P|^2\), the unmarked theorem with a sufficiently strong log power pays the actual marked square to that budget outside \(O_F(X/(\log X)^F)\) even targets, for every fixed \(F\). If one instead wants any specified log exponent in the averaged marked square, take fixed \(M>200(A+1)\) for desired exponent \(A\) and then apply the same estimate (not uniform in \(M\)). The true marked shared-gcd and diagonal increments are bounded by the unmarked absolute increments, since the row weights only decreased.

For the scalar mixed statistic alone, the direct unsigned transfer already gives
\(|\mathcal M_C-\mathcal M|\ll_\sigma L\mathcal E_P\),
so \(M\ge400\) suffices for \(o(PV_y(P)/L)\): the ratio is \(O(\kappa_z L^{2-M/200})=o(1)\). That scalar bound is not a substitute for the marked weighted square unless the stronger threshold calculation above is made. No conclusion for a given fixed \(P\) or the thin small-radical family follows.