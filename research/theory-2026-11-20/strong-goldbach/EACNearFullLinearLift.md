# A near-full divisor detects affine congruences in an actual prime-factor component

Fix an even integer \(N>4\). Write \(x\to y\) when the unit prime \(y\) divides \(N-x\), for unit primes \(2<x,y<N\). No Goldbach conjecture or prime-distribution estimate is assumed.

**Pointwise lifting theorem.** Let \(x_1,\ldots,x_k\) be distinct such vertices.
Suppose each vertex has a predecessor among them with composite complement (in particular this is true of any all-composite terminal). For coefficients \(a_0,\ldots,a_k\in\mathbb Z\) and \(D\mid N\) put
\[
  Z=a_0+\sum_{i=1}^k a_i x_i,\quad H=\max(2,\sum_{i=0}^k|a_i|),\quad U=HN/D.
\]
Then
\[
                      U^{\,2^k}<N-1,\quad D\mid Z
                      \quad\Longrightarrow\quad N\mid Z.             \tag{1}
\]
In particular, if \(N\nmid Z\),
\[
             \gcd(N,Z)\le HN/(N-1)^{\,1/2^k}.
\]
For bounded \(k\), \(D=N^{1-o(1)},\,H=N^{o(1)}\) suffice along any unbounded sequence. Neither the exponent matrix nor the arities nor their rational nullity is fixed. If additionally \(|Z|<N\), the congruence upgrades to an exact zero. Distinct labels of an all-composite terminal (each \(\le N/3\)) therefore cannot coincide up to sign modulo such a \(D\), nor can a label be \(\pm1\bmod D\).

The same conclusion (1) holds for a finite forest of actual paths with designated roots \(x\le N/U^{2^k}\), where each nonroot has a chosen earlier predecessor. No compositeness condition is required in this forest version. In particular for distinct endpoints \(y,z\) of witnessed prime-factor paths from small roots, if \(D\mid y+z\), the path union meets this size bound with \(H=2\), and (1)'s numerical gate holds, then \(y+z=N\). Distinct roots or overlapping paths can be handled by first-visit predecessors on their finite union. This is a sufficient fixed-center criterion, **not** a proof that a suitable antipodal pair is reached.

**Proof.** Each vertex has deficit \(\delta_i=\log(N/x_i)>0\). Sort in nondecreasing order and form a prefix \(I\) greedily: start \(S=0\); include the next vertex whenever \(\delta_i\le S+\log U\), updating \(S\gets S+\delta_i\). Once one vertex fails, stop. After \(r\) inclusions,
\[
            S=\sum_{i\in I}\delta_i\le (2^r-1)\log U.
\]
Thus \(e^S U\le U^{2^k}<N-1\). In the forest case no root can belong to this prefix: its deficit is at least \(2^k\log U\), exceeding every inclusion threshold \(2^{r-1}\log U,\ r\le k\).

For each included \(i\), choose one predecessor \(h(i)\) under the applicable hypothesis, and write \(N-x_{h(i)}=b_i x_i\). These positive cofactors are units modulo \(N\) and \(b_i<N/x_i=e^{\delta_i}\). In the composite case \(b_i>1\). The selected edges between included vertices give no directed cycle: multiplying around one after reduction modulo \(N\) would give \(\prod_{\rm cycle} b_i\equiv(-1)^{|\rm cycle|}\bmod N\), but \(1<\prod_{\rm cycle}b_i\le e^S<N-1\). In the forest case the same absence is already part of the selected order, even if a cofactor is 1. Tracing selected predecessors back thus exits \(I\), at some anchor \(z_i=x_j\notin I\); for indices not in \(I\) take \(z_i=x_i\). In particular \(I\) cannot be all vertices. Every anchor has deficit strictly greater than \(S+\log U\).

Let \(Q=\prod_{i\in I}b_i\le e^S\), a unit modulo \(N\). Along any selected path, its product \(Q_i\) of cofactors divides \(Q\), since the path never revisits a vertex. Write \(n_i\) for its length (zero for an outside vertex). Then \(Q_i x_i\equiv(-1)^{n_i} z_i\bmod N\). Therefore \(QZ\) is congruent modulo the *full* \(N\) to the integer
\[
                 Z'=Q a_0+\sum_i(-1)^{n_i} a_i (Q/Q_i) z_i.
\]
All anchors are \(<N/(e^S U)\), and the same strict bound holds for the constant 1 since \(e^SU<N-1\). Hence \(|Z'|<H e^S N/(e^S U)=D\) (the zero coefficient vector is immediate). But \(D\mid Z'\) if \(D\mid Z\), so \(Z'=0\), then \(N\mid QZ\), then \(N\mid Z\). Taking \(D=\gcd(N,Z)\) proves the gcd bound. In the path application \(0<y+z<2N\), leaving precisely \(y+z=N\). No lifting modulo a nondivisor of \(N\) is used.

**Application to changing nullity-one matrices on a fixed primary fraction.** Fix \(k\ge2,\ \ell\in\{2,3\},\ \epsilon>0\). At all sufficiently large \(N\) with \(P=\ell^a\mid N,\ P\ge N^{1-2^{-k}+\epsilon}\), every actual all-composite \(k\)-vertex terminal of rational corank one for \(B=I-A\), with least prime \(p\) and maximum row arity \(t\), satisfies
\[
              t(\log p)^{k-1}(1+\log\log p)^{2k-1}\gg_{k,\epsilon}\log N.       \tag{2}
\]
For \(t\le(\log N)^{1/(k-1)-\epsilon'}\), any fixed \(\epsilon'>0\), one also has \(\log p\gg_{k,\epsilon,\epsilon'}\log N/(1+t)^{k-1}\). The complementary cofactor \(N/P\) can now grow as a fixed power. The proof refers to the explicit Smith and two-log estimates of [the primary scale theorem](EACPrimaryNullityScale.md); here is why every change in their uses is valid.

Set \(L=\log N,\ H_0=(1+t)^{k-1}=O_k(L^{k-1})\); let \(d\) denote the last nonzero Smith invariant, and \(v,c\) primitive integral kernel and left-kernel vectors of \(B\). The signed cyclic parametrization gives \(x_i\equiv\sigma_i u^{v_i}\bmod D\) with \(D=P/\ell^{v_\ell(d)}\ge P/H_0\). In particular \(D\mid N\). For large \(N\) this meets (1)'s gate with affine height 2. Thus all \(v_i\) are nonzero and pairwise distinct, independently of \(p\); a collision or a zero would give a forbidden congruence for a signed pair or a signed singleton. The least prime tends to infinity on any such sequence, since otherwise the [bounded-orbit fixed-seed independence theorem](PrimeOrbitMovingSeed.md) would give corank at least two (here \(P\ge N^{3/4+\epsilon}\)). 

For \(q\) the second least prime and \(T=L/\log q\), put \(J=C_k(1+T)^{k-1}\) as in the primary scale proof. The projected-minor inequalities still apply: only the \(p\)-column can cost \(1+t\), the remaining independent columns cost \(\ll_k 1+T\). In particular \(d,|v_p|,\max|c_i|\le J\). For the two-log estimate use the integral row-lattice relation \(2d(v_q e_p-v_p e_q)\); the coefficient of \(\log q\) costs \(O_k((1+T)^{2k-2})\), the one of \(\log p\) costs \(O_k((1+t)(1+T)^{2k-3})\), so the normalized coefficient parameter is \(O_k((1+T)^{2k-2})\) by \(t/\log q\le T/\log p\). Bugeaud–Laurent's two-log theorem at \(\ell\) therefore gives \(T\ll_{k,\epsilon}(\log p)(1+\log(1+T))^2\), since \(\log P\gg L\). If \(p\le J\) along an infinite subsequence, it follows \(T\ll_{k,\epsilon}(1+\log(1+T))^3\), whence \(T,p\) bounded, impossible. Thus \(p>J\) eventually. This is enough: exponents were already separated by (1), and the extreme coefficient of the sparse resultant is a single nonzero integer of absolute value \(\le J<p\). Its nonzero value at \(p\) is divisible by \(D\); \(\log D\gg L\). The explicit bound from the linked argument now gives
\[
 L\ll_{k,\epsilon}(1+T)^{k-1}(1+\log(1+T))+
                    (1+t)(1+T)^{k-2}\log p .
\]
Inverting the two-log bound and substituting proves (2). In the additional small-arity range, \(p\le H_0\) would give \(\log p=O_k(\log L)\) and force \(t\ge L^{1-o(1)}\) by (2), impossible. With \(p>H_0\) and all exponents distinct, the unprojected resultant bound is \(\log D\le H_0\log(kH_0)+2H_0\log p\). Here the first term is \(o(L)\), giving the second assertion. These estimates do not exclude all growing signatures or certify a Goldbach representation.
