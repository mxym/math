# Complementary short labels in the genuine double Vaughan remainder

This is an alternative exact partition of the original (unmarked) giant remainder, not a deletion to be added to an overlapping accounting with fully opened long log labels.

Retain the prescribed individual even \(N\), fixed \(J_0\Subset(0,1)\), \(J\subset J_0\), \(L=\log N\), \(\ell=\log L\), \(S=\exp(\ell^4)\), \(B=N/S\), \(z=\exp(\ell^2)\), and now \(V=\exp(\ell^3)\), and literal real interval \(I\subset[\sqrt N S^2,B]\) of [the double rough reversal](../reverse_giant_typeI/DoubleRough.md). Put \(y=N-x\), \(T_y=y/B\), \(Q_y(m)=\sum_{d\mid m,\ d<T_y}\mu(d)\), and \(\lambda_{>W}(n)=\sum_{j\mid n,\ j>W}\Lambda(j)\). Every \(x\) is in \(NJ\). The quantity under study is the genuine prime--prime marked remainder
\[
 C_I=\sum_{\substack{x\in NJ\\x\ {\rm prime}}}(\log x)
            \sum_{\substack{y=rm,\ r\in I\\ r\ {\rm prime}}}(\log r)Q_y(m).
\]
Use the double reversal with cutoff \(D=V\) on the \(x\)-side as well. Then, at arbitrary fixed log precision,
\[
 C_I=\sum_{\substack{x=ab,\ y=mcv,\ x+y=N,\ cv\in I\\
                (abmcv,N)=1,\ P^-(abcv)>z,\ a>V,\ c>V}}
        \mu(a)\mu(c)\lambda_{>V}(b)\lambda_{>V}(v)Q_y(m)
            +O_A(NL^{-A}).                                           \tag{1}
\]
For either \(b\) or \(v\), the condition \(\lambda_{>V}\ne0\) is represented by the actual weights, not used as a separate cut in an opened term.

**Proved scope.** The entire **raw** part of (1) on
\[
                     a(mc)\le N/V^3                      \tag{2}
\]
is \(O_A(NL^{-A})\). No restriction on the factor rank or polynomial size of \(m\) is imposed. Independently, on raw dyads \(a\asymp N^u,\ mc\asymp N^v\), put \(g=u+v,\ h=\max(u,v)\). The whole raw dyad is \(O_A(NL^{-A})\) when there is fixed positive slack in both of the relevant inequalities
\[
\begin{array}{ll}
   .7g+.25h-.85<0,\quad .875g+.125h-1<0, &g\ge1,\\
   .5-.65g+.25h<0,\quad .5-.625g+.125h<0, &g\le1. 
\end{array}                                                         \tag{3}
\]
In particular \(a,mc\in[N^{.49},N^{.51}]\) is covered, including genuinely supercritical products; so is a small fixed neighborhood of \((u,v)=(.475,.54)\). The symbol \(mc\) denotes the literal product of the unrestricted giant quotient \(m\) and the Möbius slot \(c\). These are raw cohorts, independent of how large the log-divisor labels are in another opening. For example raw \(u=.30,v=.50\) may include actual expanded \(af\asymp N^{.60},\ mch\asymp N^{.70}\) in the earlier *long-label* bookkeeping. This example only illustrates scope; it is not an occupancy assertion.

## 1. The smaller cutoff and the four exact terms

First verify the uniform rough harmonic at the new, smaller \(V\). For \(H\le N^{O(1)}\), the Dirichlet series for \(\mu(n)1_{P^-(n)>z,(n,H)=1}\) is \(\zeta(s)^{-1}\) times \(\prod_{q\le z\ {\rm or}\ q\mid H}(1-q^{-s})^{-1}\). At \(\sigma=1-\log\ell/(2\ell^2)\) the absolute coefficient sum of that second factor is \(\exp(O(\sqrt\ell\log\ell))\), since \(q^{1-\sigma}\le\sqrt\ell\) for \(q\le z\), and the \(O(L)\) possible \(q\mid H\) above \(z\) are negligible. Split the convolution at \(\sqrt X\): classical Mertens bounds the smaller part, and Rankin at this \(\sigma\) bounds the other. For \(X\ge V/2\) the relative prefix error is at most
\[
  \exp(O(\sqrt\ell\log\ell))
   \bigl(e^{-c\sqrt{\log X}}+X^{-(1-\sigma)/2}\bigr),
\]
which is integrable against \(dX/X\) with an arbitrary fixed log saving from \(V/2\) onward. Hence signed \(\mu(a)/a\) harmonics on real intervals with \(a>V\) remain arbitrary-log small with every permitted unit mask. The Bonferroni products of DoubleRough, even including the first omitted degree, have cardinality and size \(\exp(O_A(\ell^3/\log(2\ell)))=V^{o(1)}\). Their factorial reciprocal estimates are unchanged.

The rough reversal of the actual \(r\)-prime in ReverseTypeI §3 works at this \(V\): its largest short progression modulus is \(\sqrt N S^{-2}V^2 V^{o(1)}=\sqrt N S^{-2+o(1)}\), and the required \(Q_y(m)\) harmonic (with cutoff \(T_y\asymp S\)) is unchanged. In §2 of DoubleRough, the \(x\)-side rough Vaughan step holds with \(D=V\) instead of \(N^{1/200}\). The small \(\Lambda_{\le D}\) term is absent in central \(NJ\), and the two Type I moduli \(a\) are now \(\le V^2\le N^{.01}\), with the same \(O(L)\) coefficients. In the first case \(k>N^{.1}\) the product ceiling persists, and use the just-proved rough harmonic in \(c>V\); in the second the genuine masked Möbius B--V length \(N^{.1-o(1)}\) is unaltered; in the third the genuine prime mark \(h\ge N^{.29}\), its prime B--V, and the (now shorter) \(c\)-harmonic again give the claimed error. The original \(x\)-prime powers cost \(N^{1/2+o(1)}\); on the giant side the sum of reciprocal proper powers above \(\sqrt N S^2\) is \(N^{-1/4+o(1)}\), with the same physical divisor envelopes, so both errors are power-small. This proves (1); it does not assert that double Type II at the two choices of cutoff agrees on any sector.

Use the exact identity
\[
      \lambda_{>V}(n)=\log n-\sum_{\substack{j\mid n\\j\le V}}\Lambda(j).
                                                                    \tag{4}
\]
For the first factor choose either free coordinate \(b\) with weight \(\log b\) or \(b=f G_0\) with a real short label \(f\le V\) and coefficient \(-\Lambda(f)\). For the second choose either free coordinate \(v\) with weight \(\log v\) or \(v=t K_0\) with a real short label \(t\le V\) and coefficient \(-\Lambda(t)\). In a log term set the corresponding label to \(1\). Thus there are four terms; when present the literal factors \(f,t\) automatically are genuine prime powers where their coefficients are nonzero. A short label must be \(z\)-rough and a target unit; this simply makes the rest of the original rough and unit constraints exact on the new free integers. We do not approximate prime-power weights, discard their powers, or impose long-prime conditions from the other opening.

If \(f=1\) represents the log choice, its real weight is \(\log(x/a)=L+\log(x/N)-\log a\); the other log choice \(t=1\) has weight \(\log((N-x)/(mc))=L+\log(1-x/N)-\log(mc)\). All their variations are controlled by centrality and these actual identities. The two short-label harmonic sums satisfy \(\sum_{f\le V}\Lambda(f)/f\ll\log V\) (and likewise for \(t\)); when counting tuples without reciprocal weights, bound them by \(V^2 L^2\) for the two labels together, inclusive of the \(1\) choices. No coprimality between \(a\) and \(f\), or \(c\) and \(t\), is imposed.

We may first freeze the moving \(T_y\) and the \(m\) cuts determined by \(y/m\in I\) on the actual \(y\)-mesh of [the reciprocal-seam proof](../reverse_giant_typeI/GiantReciprocalSeam.md). For width \(NL^{-F}\), the displaced \(d<T_y\) rows have actual \(d\mid y,\ d\ll S,\ |y-Bd|\ll NL^{-F}\), and the displaced \(I\)-side rows have \(m\mid y,\ m\le\sqrt N,\ |y-E m|\ll NL^{-F}\) at an endpoint \(E\) of \(I\). The union is \(O(NL^{1-F}+S+\sqrt N)\) integers, counted once globally by actual multiples. The frozen \(m\)-interval still has \(m\le\sqrt N\) because \(E\ge\sqrt N S^2\). Every expansion here is bounded on the physical \(x,y\) by \(L^C\tau(x)^C\tau(y)^C\) with an absolute exponent. Cauchy and divisor moments pay these boundary errors. Smooth each cell on a thinner band as in the same proof; this is uniform even for smaller \(J,I\). Thus we may use \(\Psi(x/N)\), \(Q_T(m)\) with \(T\asymp S\), and an independent interval for \(m\) on each cell. There are only fixed log powers of cells, absorbed by increasing precision.

## 2. Literal CRT on the raw product region

Open the \(z\)-roughness of both free integers using the actual labels \(e_1,e_2\) of DoubleRough, squarefree, on primes \(\le z\) outside \(N\), with the two successive Bonferroni truncations. The new outer products are
\[
              A=a f e_1,\qquad C=m c t e_2,
\]
and the remaining free coordinates satisfy \(A G+C K=N\) exactly. Retain \((A C,N)=1\); any actual unit row also has \((A,C)=1\). Conversely in each compatible tuple \(x\) occupies one progression mod \(AC\), with the actual condition \((x,N)=1\) on that progression. The central support makes both free coordinates positive.

For the roughness errors one may first count actual omitted labels \(e\mid x\) or \(e\mid y\) globally (\(\ll N\sum 1/e\) incidences) and use the divisor envelope. Bounds of the form \(N L^{-A}\) survive because the high-degree factorial reciprocal tails beat any prescribed log power. For the unit mask on the integer CRT keep small target primes via the same Bonferroni bounds and apply the union bound at the \(O(L)\) target primes larger than \(z\); this is exactly the computation in DoubleRough §2, Case 1. At fixed compatible tuple the main density is \(\varphi(N)/(N A C)\), with errors \(O_A((N/(AC))L^{-A}+V^{o(1)})\) before log weights. Ordinary real partial summation keeps this statement for \(\Psi\) and either of the log choices.

On (2), writing \(W=N/V^3\), the number of raw \((a,m,c)\) is bounded by \(W L^{O(1)}\) (sum the three-divisor function). With the two short \(f,t\) labels and both small presieve counts and floor allowances, the total floor bill is
\[
                     W V^2 V^{o(1)}L^{O(1)}
                         \le N V^{-1+o(1)}.
\]
This counts all multiplicities of the actual raw variables and both short weights. The reciprocal part of the errors is harmless by ordinary divisor harmonic bounds, including \(\sum |Q_T(m)|/m\ll L^2\), the two short log-label harmonic sums, and the small-label Euler harmonics.

For the principal term, fix \(x,m,c,f,t,e_1,e_2\). The remaining actual \(a\)-sum is the rough \(\mu(a)/a\) harmonic for \(a>V\), with \((a,NC)=1\) and interval endpoints from (2). All other checks are independent of \(a\). The possible \(\log(x/a)\) is monotone in \(a\) with supremum and variation \(O(L)\). In particular there is no prime assumption on \(a,m,c\), nor independent-factor approximation to the true \(Q_T(m)\). The uniform masked rough harmonic from §1 applies at all prefixes on this interval; with the weight it follows by partial summation. Sum the remaining *reciprocal* masses, not the cardinalities of the presieve labels. This proves (2) at arbitrary log precision.

## 3. The same short-label expansion in the reciprocal region

Keep the raw dyads in \(a,mc\) independently, leaving out the product cut for this calculation. For fixed \(f,t,e_1,e_2\) the proof of the genuine reciprocal seam applies to \(A=a f e_1\), \(C=mc t e_2\). Both added scales are \(N^{o(1)}\). The \(x\)-weights from (4) separate into finitely many smooth functions of \(x/N\) and outer factors \(\log a,\log(mc)\) of size \(O(L)\). No derivative in a label is needed. The genuine coefficient on \(a\) relabelled at \(A\) is single-valued for fixed \(f,e_1\), bounded by \(L^{O(1)}\) including the log factors. The coefficient at \(C\), on fixing \(t,e_2\), aggregates only the actual factorizations \(mc=C/(t e_2)\) with \(Q_T(m)\); it is \(L^{O(1)}\tau_3(C)\). Thus on dyads \(A\asymp M_1\), \(C\asymp M_2\) the two \(\ell^2\) norms cost \(M_1^{1/2}L^{O(1)}\), \(M_2^{1/2}L^{O(1)}\), even with all the prescribed masks. All short-label coefficients are bounded by \(L^{O(1)}\) and their absolute number is \(N^{o(1)}\).

Remove the exact \((x,N)=1\) by \(u_0\mid (G,N)\), which forces \(u_0\mid K\), truncating \(u_0\le\exp(L^{3/4})\) by the actual weighted tail in the reciprocal seam. This is valid for both new log-weight choices, since their suprema on the physical lattice are \(O(L)\). After substituting \(G=u_0G'\), the progression for \(G'\) has modulus \(C\) and residue \((N/u_0)\bar A\). Poisson supplies
\[
 \frac{N}{u_0 AC}\,
 \widehat{\Psi}\left(\frac{\nu N}{u_0 AC}\right)
 \exp\left(\frac{2\pi i\nu(N/u_0)\bar A}{C}\right).                 \tag{5}
\]
Each separated smooth weight replaces \(\Psi\) in this same formula. At \(\nu=0\) sum the signed rough harmonic in \(a\) as in §2; the other coefficients and the \(u_0\) variables are summed by reciprocal weights, which are only log powers. Unit duplication, including \(f,t\) overlap within each outer product, is treated exactly by the actual product and Möbius unit condition, not by an lcm in (5).

For the nonzero \(\nu\), rapid Fourier decay truncates \(|\nu|\le N^\rho(1+M_1M_2/N)\) with arbitrarily small fixed \(\rho>0\) and negligible power error, because \(u_0=N^{o(1)}\). In a signed frequency dyad \(|\nu|\asymp T_1\), separate the smooth function of \(|\nu|/(A C)\) by compact Mellin inversion with log-power norm, as in the reciprocal seam. Apply [Bettin--Chandee, Theorem 1](https://arxiv.org/pdf/1502.00769) with phase multiplier \(N/u_0\), supports on these two dyads and the frequency dyad, and the true condition \((A,C)=1\). Put \(g=\log_N(M_1M_2)\), \(h=\log_N\max(M_1,M_2)\); these differ from the raw dyadic exponents by \(o(1)\). With \(b=\max(0,g-1)\) the frequency exponent, the norm times front factor contributes \((b-g)/2\), the phase factor contributes \(\max(0,1-g)/2\), and the two terms of their bound contribute \(.35(b+g)+.25h\) and \(.375(b+g)+.125(b+h)\). Combining these gives exactly (3), apart from errors \(O(\rho)+o(1)\) and the arbitrarily small exponent in Bettin--Chandee. The assumed strict slack preserves a power saving through summation of all nonzero terms, including the absolute \(V^2\) short-label count. This proves (3).

One may combine (2) and (3) at exactly the same raw cutoffs, subtracting the literal intersection of a chosen raw dyad and (2). In the intersection proof the two independent dyadic conditions add literal intervals to the CRT principal and reduce its floor count. At most \(L^C\) log-scale boxes for fixed \(C\) can be summed with higher prescribed precision, provided the chosen reciprocal boxes retain fixed slack in (3); disjoint dyads avoid overlap with one another. A comparison with a previous deletion based on \((af)(mch)\) with \(f,t>V\) has no such permissive disjointness: that is a different exact opening. No sign for the rest of (1) is claimed. On the remaining raw rows one has \(a(mc)>N/V^3\), which forces \(bv\ll NV^3\) by the exact identity \(a(mc)bv=x(N-x)\); this assertion alone does not make either free coordinate small.
