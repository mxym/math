# A completed dual reciprocal estimate and a genuine Vaughan III slice

Use the notation \(x=N/2\), \(I=(x/2,x]\), \(s\sim S=x^\alpha\) with \(s\) prime, \(.10\le\alpha\le.14\), and the original second prime \(q\) with \(sq\in I\) from [UnmarkedSemiprimeWholeTypeI.md](UnmarkedSemiprimeWholeTypeI.md). The latter gives the two exact reflected Vaughan Type I terms through exponent \(1/2-\alpha/4-\Delta\). The dual estimate here reaches
\[
                 b_*=(4-5\alpha)/7-\Delta,\qquad 0<\Delta<.01.
\tag{1}
\]
It also evaluates a strict, nonempty **part of the true remaining Vaughan III term**, comprising the products \(d\ell\le x^{b_*}\) with \(d>U\), \(\ell>V\). No estimate for the complete Vaughan III term is asserted. All statements fix the actual even \(N\), with no exceptional set of targets.

More explicitly, take \(U\ge x^{.40}\) and \(1\le V\le x^{.03}\) with \(UV\le x^{b_*}\) for the full Type I formulas (2) of the prior note, now valid with \(b_*\) replacing its cap. On the same actual weighted semiprime cell, one also has for every fixed \(B>0\)
\[
\sum_{\substack{s,q\ {\rm prime}\\s\sim S,\ sq\in I}}\kappa_s W_s(q)
       \sum_{\substack{d\ell h=N-sq\\ d>U,\ \ell>V,\ d\ell\le x^{b_*}}}
                        \mu(d)\Lambda(\ell)
                   \ll_{\Delta,B} x(\log x)^{-B}.
\tag{2}
\]
The test \(W_s\) includes the same sharp central region and the exact \(K_{P_3}(sq)\) of the preceding note. One may further require any fixed additional intervals in \(d,\ell\), retaining the proof below. The divisor cutoff ranges are literal, not smooth restrictions. Across the full label band \(b_*\ge33/70-\Delta\) and the value at \(\alpha=.10\) is \(1/2-\Delta\).

For a strict log-width example of (2) **beyond the preceding cap**, let \(b_{\rm old}=1/2-\alpha/4\), \(\Delta=.002,\ U=x^{b_{\rm old}-.006}\), \(V=x^{.004}\). The choices are within the preceding Type I theorem as well. Take the actual two factors of Vaughan III in the box
\[
 \log_x d\in[b_{\rm old}-.004,b_{\rm old}-.003],\qquad
 \log_x\ell\in[.005,.006].
\]
Here \(d>U,\ell>V\) and \(\log_x(d\ell)\in[b_{\rm old}+.001,b_{\rm old}+.003]\), above the preceding cutoff by a fixed amount, while \((4-5\alpha)/7-b_{\rm old}=(2-13\alpha)/28\ge .00642857\ldots\). Thus (2) includes a uniform positive-width box of the actual residual, not just the difference of two evaluations of the original \(\mu*\log\) term.

## 1. Coprime mean for the true slice

Let \(a=d\ell\) and set
\[
 c_3(a)=1_{a\le x^{b_*}}\sum_{\substack{\ell\mid a\\\ell>V,\ a/\ell>U}}
                           \Lambda(\ell)\mu(a/\ell).
\tag{3}
\]
Optional interval restrictions in \(d=a/\ell,\ell\) are included in this sum. Its free factor \(h\) has weight 1 and \(|c_3(a)|\le\log a\). This is the actual coefficient in (2), not a postulated parity sign. Since \(b_*<1/2\), only \(\ell\le x^{b_*}/U\le x^{.10}\) enter. For the Type I calculations use the other two coefficients of (5) in the preceding note, with their original support and free weights.

For ordinary BV, use the same joining exponent \(b_0=1/2-.51\alpha\) and cut \(a\le x^{b_0}\). For each actual \(s\), the principal coefficient sum now has the form
\[
 \sum_{\ell\le x^{b_*}/U,\ (\ell,E)=1}\Lambda(\ell)
 \sum_{\substack{d>U,\ d\le \min(x^{b_*}/\ell,x^{b_0}/\ell)\\(d,E)=1}}
                          \frac{\mu(d)}{\phi(d\ell)},\quad E=Ns,
\]
with the lower cut on \(\ell\) and any other intervals understood. If the inner interval is nonempty, it is a difference of prefixes with both endpoints at least \(U\ge x^{.40}\). For \(\ell=p^k\), split the exact factor \(\phi(d)\phi(\ell)/\phi(d\ell)=1-p^{-1}1_{p\mid d}\), and use the arbitrary-log coprime \(\mu/\phi\) prefix estimates in (11) of the preceding note with \(E\) and \(Ep\). The harmonic weight \(\sum_{\ell\le x^{.10}}\Lambda(\ell)/\phi(\ell)\) costs only log powers. The actual BV error below the join is handled by \(|c_3(a)|\ll L\), even with endpoint cuts.

For the true Poisson zero above the join, use the same exact substitution \(a=g n,\ t=(g,\ell),\ n=(\ell/t)v,\ g_0=g/t\). Then \(a/\ell=g_0v\). The conditions in (3), including \(g_0v>U\), are one interval in \(v\), after fixing \(\ell\); the unit mask is fixed or zero for that \(\ell\). Use \(\mu(g_0v)=\mu(g_0)\mu(v)1_{(g_0,v)=1}\), including the zero case for nonsquarefree \(g_0\). The scale \(D t/(g\ell)\) of \(v\) is at least \(x^{.328+o(1)}\) by \(D\ge x^{b_0}/2\), \(g\le L^K\), \(\ell\le x^{.10}\). Thus uniform coprime Mertens and partial summation with the genuine smooth zero-frequency test give arbitrary log saving. The harmonic loss from fixing \(\ell\) is \(O(gL)\), and all prefactors match the earlier proof. In the two Type I cases, exactly the earlier zero and BV principal computations apply unchanged.

## 2. Direct dual estimate for *all* nonzero reciprocal frequencies

For each original divisor dyad \(D<a\le2D\), use the same \(D\) in the primed copy after Cauchy over the original quotient \(q\) (only then enlarged to integers). Write \(H=x/D,\ Z=D/g\). All physical determinant, smoothing, unit support and absolute tail estimates of the preceding note remain valid: the proofs used only \(|c_j(a)|\ll L\), \(D\gg x^{b_0}\), \(D<x^{1/2}\) here, and the actual prime label band. In particular in the nonzero analysis \(g,s_0\le L^K,\ f\le e^{L^{3/4}}\), \(f\mid N,\ r_1\asymp Z\), and the reduced Fourier phase is
\[
  e_Q((N/f)t_{B,\nu}\bar n),\qquad
  t_{B,\nu}=\frac{\nu(B-A)}{g s_0 B},\quad
  Q=A r_1/s_0,\quad Q_2=Q/A=r_1/s_0 ,
\tag{4}
\]
where \(A,B\) are distinct true primes from the same dyad. Here \(gs_0\mid B-A\), \(A\nmid gs_0\), \(B\) and \(N/f\) are units modulo \(Q\), and each admissible rational is interpreted modulo \(Q\). Other mask conditions remain on their original slots. The Poisson prefactor is \(H/(f s_0 Q)\). Take
\[
          T=x^{\alpha+2b_*-1+\Delta}
            =x^{(1-3\alpha)/7-\Delta}.
\]
The true frequency scale is at most \(x^{\alpha+2b_*-1+o(1)}\), so the discarded \(|\nu|>T\) have any desired power saving. The retained signed frequencies satisfy \(2T<A\) for large \(x\), since \(b_*+\Delta\le1/2\).

Fix \(A,g,f,s_0,r_1\). As before, fixed-cutoff Mellin inversion in the normalized \(n/Z\) alone separates \(\widehat W_{\rm ph}\) from the sharp \(n\) coefficient. For each separated integral entry, the inner sum to bound, before the prefactor, is of the form
\[
 \sum_{\substack{n\asymp Z\\(n,Q)=1}} c_n
       \sum_{\substack{B\sim S,\ B\ {\rm prime}\\0<|\nu|\le T}}
              w_{B,\nu}e_Q((N/f)t_{B,\nu}\bar n).
\]
The \(n\)-range can be kept a fixed integer interval containing its sharp support; all possibly extra \(n\) unit tests (including \((n,q_0)=1\) if \(q_0\) had a prime removed by \(s_0\)) are absorbed into \(c_n\). The weights \(w_{B,\nu}\) may contain all restrictions depending on the actual \(B,\nu\) and outer data; they are uniformly log-bounded with integrable Mellin decay. Cauchy in \(n\) costs \(\|c_n\|_2\ll\sqrt Z L^C\). Inside its squared norm \(n\) is now **unweighted** other than the interval and \((n,Q)=1\).

For a pair \((B,\nu),(B',\nu')\), choose the integer
\[
  \Delta_0=
   \frac{\nu(B-A)B'-\nu'(B'-A)B}{g s_0}.
\tag{5}
\]
The numerator is integral on the actual allowed pairs; \(t_{B,\nu}-t_{B',\nu'}=\Delta_0/(BB')\); hence the gcd of the phase coefficient with \(Q\) is precisely \((\Delta_0,Q)\). Reduced denominators and \(0<|\nu|\le T<A,B\) show \(\Delta_0=0\) only on the exact diagonal \((B,\nu)=(B',\nu')\). Also \(|\Delta_0|\ll S^2T\le x^{.42+o(1)}<Q_2\) by \(Q_2\ge x^{.4286+o(1)}\). If \(\nu\ne\nu'\), then \(A\nmid\Delta_0\), because
\(\Delta_0\equiv BB'(\nu-\nu')/(g s_0)\pmod A\) and \(0<|\nu-\nu'|<A\). If \(\nu=\nu', B\ne B'\), allow a factor \(A\) in the gcd by \((\Delta_0,Q)\le A(\Delta_0,Q_2)\). These conclusions include \(A\mid Q_2\); no coprime decomposition of \(Q\) is imposed.

Complete the unweighted \(n\)-interval by additive Fourier series mod \(Q\) (\(Z\ll Q/A\cdot s_0<Q\)), whose normalized interval-transform \(\ell^1\)-norm is \(O(\log Q)\). The usual complete [Weil–Estermann Kloosterman bound for composite moduli](https://doi.org/10.1112/S0025579300002187) for Fourier mode \(k\) is \(\ll\tau(Q)\{Q(k,\Delta_0,Q)\}^{1/2}\), since both \(N/f\) and \(BB'\) are units. Thus its bound for the incomplete interval is \(Q^{1/2}(\Delta_0,Q)^{1/2}x^{o(1)}\), for every nonzero pair (5) with no squarefree assumption on \(Q\).

**Average the gcd before taking the outer square root.** Fix \(A,g,f,s_0\) and the ordered pair in (5), so \(\Delta_0\) is independent of \(r_1=s_0Q_2\). The number of potential \(Q_2\) is \(\asymp Z/s_0\), and even enlarging to *all* integers in its dyad,
\[
  \sum_{Q_2\asymp Z/s_0} (\Delta_0,Q_2)^{1/2}
   \ll (Z/s_0)\sum_{v\mid\Delta_0}v^{-1/2}
   \ll (Z/s_0)x^{o(1)}.
\]
Use \((\Delta_0,Q_2)^{1/2}\le\sum_{v\mid\Delta_0,\,v\mid Q_2}\sqrt v\), then \(O((Z/s_0)/v)\) multiples of \(v\) (all such \(v<Q_2\) up to fixed dyadic constants). The other restrictions merely remove pairs, and the original weights depending on \(r_1\) are bounded in this positive estimate. Jensen/Cauchy over the \(r_1\)-sum is now legitimate after this averaging. This is distinct from assuming individual Kloosterman energy cancellation.

For each \(A,g,f,s_0\), the average squared norm inside Cauchy in \(n\) is consequently at most
\[
 x^{o(1)}\bigl(ST Z+S^2 T^2\sqrt Q+S^2 T\sqrt{A Q}\bigr),
 \qquad Q\asymp S Z/s_0 .
\tag{6}
\]
The first term is the literal diagonal. For distinct frequencies there are \(O(S^2T^2)\) pairs and no extra \(A\)-loss; equal frequencies, distinct labels contribute \(O(S^2T)\) pairs. Multiply by \(\sqrt Z L^C\) and compare with the target \(SZ\); the three respective normalized ratios are
\[
 \sqrt{T/S},\qquad
 T Q^{1/4}Z^{-1/2},\qquad
 \sqrt T(AQ)^{1/4}Z^{-1/2}.
\]
In exponents up to \(o(1)\), these are at most
\[
           -\Delta/2,\qquad -3\Delta/4,\qquad
                                     (13\alpha-2)/28-\Delta/4 .
\]
For the latter two, the ratio is largest when \(D=x^{b_*+o(1)}\) **if** one uses the sharper \(D\)-dependent frequency cap \(T_D\ll f q_0/H\cdot x^{\Delta-o(1)}\le x^{\alpha+2\log_x D-1+\Delta+o(1)}\), with \(T_D\ge1\); the near-zero-scale case is addressed below. Both exponents increase with \(\log_x D\). The third is at most \(-.0064-\Delta/4\). At \(T_D=1\) the three exponents are immediately negative using \(Z\ge x^{.4286+o(1)}\) and \(\alpha\le .14\) (for the last ratio use \(AQ\ll S^2 Z\)). More precisely one can and does choose \(T_D=\max(1,\lceil x^{\alpha+2\log_x D-1+\Delta}\rceil)\). It beats the true scale by a power whenever nonzero terms beyond this cutoff are discarded. The upper \(T\) above may be doubled without affecting \(2T<A\). This dyad-specific cutoff is important in (6): inserting the common largest \(T\) on all smaller \(D\)'s would not give the same exponent arithmetic.

Finally sum the true prefactor \(H/(fs_0Q)\) over \(r_1=s_0Q_2\) and over \(A\sim S\) using the harmonic factor \(1/A\). Jensen from (6) bounds the resulting contribution by \(O(xS x^{-c_\Delta}/(f s_0 g))\), since \(HZ=x/g\). The remaining \(f,s_0,g\) sums have harmonic costs and all box/smoothing/Mellin costs are fixed log powers. This proves (2) and the claimed improved Type I evaluation.

## 3. A one-sided exact support cut beyond (2)

Write \(m=N-sq\) and assume the actual test \(\kappa_s W_s(q)\ge0\), as for \(K_{P_3}\). The part of the remaining Vaughan III term from integers \(m\) with a prime factor \(P>m/U\) can be discarded in an **upper** estimate. Indeed \(U\le x^{b_*}<\sqrt m\), so \(P>\sqrt m\) is unique, \(m=P t\), \(t<U\), and \(P>x^{b_*}\). Every \(d>U\) dividing \(m\) contains \(P\); write \(d=P a\). Then \(\mu(d)=-\mu(a)\) even when \(t\) has squares, and \(\ell\) is a divisor of \(t/a\). The high-product cutoff \(d\ell>x^{b_*}\) is automatic. Therefore the per-\(m\) coefficient in the unestimated piece is exactly
\[
  -\!\sum_{a\ell h=t,\,\ell>V}\!\mu(a)\Lambda(\ell)
                     =-\Lambda_{>V}(t)\le0.
\tag{7}
\]
This is an exact largest-prime switching identity on the actual support; it requires no upper/lower estimate for these negative summands. It only narrows an upper-bound problem to \(P^+(m)\le m/U\). It does not show a sign or cancellation there, in particular in the balanced region \(d>U,\ d\ell>x^{b_*},\ P^+(m)\le m/U\), where the positive composite ranks remain. The result is on the actual semiprime cell but does not yet provide its required signed upper bound or close Goldbach.
