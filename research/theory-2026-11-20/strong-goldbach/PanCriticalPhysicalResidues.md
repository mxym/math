# Physical residue profiles at Pan's fixed critical split

Keep the notation and central interval of [the critical physical roughness proof](PanCriticalPhysicalRoughness.md). Here the period \(m\) is any positive integer, not necessarily squarefree. Let \(a\bmod m\) be a residue, \(J_m(a)=1_{(a(P-a),m)=1}\), \(h_m=\sum_{a\bmod m}J_m(a)\), and \(G_m(a)\) the actual central two-log prime-pair sum for \(n\equiv a\bmod m\). The Chinese remainder theorem gives
\[
 h_m=\phi(m)\prod_{\ell\mid m,\ell\nmid P}(1-1/(\ell-1)),\qquad
 S(Pm)/\phi(m)=S(P)/h_m.
\]
Thus \(h_m>0\). For an arithmetic summand \(F(n)\) let \(F_m(a)=\sum_{n\in I,n\equiv a\,(m)} F(n)\). Write \(\mathcal M_m(a)=X S(P) J_m(a)/h_m\).

**Theorem.** At every sufficiently large even \(P\), with the same fixed \(Q=\sqrt P/(\log P)^{20}\),
\[
\begin{split}
 \sum_{m\le L^4}\sum_{a\,(m)}
  |(\Lambda(n) B^*(r))_m(a)-\mathcal M_m(a)|&\ll P L^{-1+o(1)},\tag{1}\\
 \sum_{m\le L^{1/10}}\sum_{a\,(m)}
  |(A(n)A^*(r))_m(a)-G_m(a)+\mathcal M_m(a)|&\ll P L^{-1/3}.\tag{2}
\end{split}
\]
Formula (1) also holds with \(BB^*\) on the left. It describes the sign-reversed true prime–composite raw row up to negligible prime powers, because \(B^*(r)=0\) on a large prime and it is the long coefficient on a composite having at least two distinct prime factors for \((r,P)=1\). In (2) the **actual asymmetry is kept**. Any choice of bounded test depending on both \(m\) and the whole residue \(a\) is allowed by this total-variation estimate. This is a signed assertion per residue class aggregated in absolute value, not a bound after taking absolute values at each physical integer. It is independent of, and does not assert, a lower bound on \(G_m(a)\).

## Prime–short and short–short

Pass first to true prime \(p=n\), \(p\nmid P\), in (1), with a \(P^{1/2+o(1)}\) error per modulus even summed over residues. If \((a,m)>1\), there are no such central primes. Otherwise write \(d=j f\) for the squarefree short divisor of \(P-p\), with \(j\mid\operatorname{rad}m\) and \((f,Pm)=1\). Exactly \(j\mid P-a\) is needed for the \(j\) part; such primes in \(j\) automatically do not divide \(P\). The prime satisfies \(p\equiv a\pmod m,\ p\equiv P\pmod f\), one reduced class mod \(mf\). In the BV main, \(1/\phi(mf)=1/(\phi(m)\phi(f))\). At upper endpoint \(Q/j\) the signed \(\mu(f)\log(j f)/\phi(f)\) mean is \(-S(Pm)+O_H(L^{-H})\), uniformly since \(j\le L^4\), as in §1 of the roughness proof. The outside \(\sum_{j\mid(\operatorname{rad}m,P-a)}\mu(j)\) is just the other unit indicator. The actual prime discrepancy per modulus, with all residues summed in absolute value, is at most
\[
 O\big(L\,m\tau(m) E(P,mQ)\big),
\]
where \(E\) is Vaughan's explicit estimate (3) in the linked proof. For each \(j\) the modulus \(mf\) determines \(f\); the factor \(m\) already pays the separate residue maxima. Its second term costs \(P L^{-13}\sum_{m\le L^4}m^2\tau(m)\le P L^{-1+o(1)}\). The first permits arbitrary log savings. This proves (1). By reflection the true-prime endpoint in the other orientation has the identical profile.

For \(B(n)B^*(r)\) fix a right short divisor \(d\) coprime to \(P\), requiring \(n\equiv P\pmod d\). This is compatible with \(a\bmod m\) iff \((m,d)\mid P-a\), giving a single residue \(c\bmod u\), \(u=[m,d]\). The progression sum of \(B(n)\) is
\[
 1_{(c,u)=1}\frac{X}{\phi(u)}
    +O(Q L)+O_H(X\tau(m)L^{-H}/u).
\]
Indeed write the left short divisor as \(s h\), \(s\mid(\operatorname{rad}u,c)\), \((h,u)=1\). The integer count is \(X/(uh)+O(1)\). Since \(c\equiv P\pmod d\) and \((d,P)=1\), all primes of \(s\) belong to \(m\) and \(s\le m\). Apply the uniform \(1/h\)-Euler estimate of the roughness proof up to \(Q/s\), then sum \(\mu(s)\), which kills all nonunits. The floor errors over the short left divisors cost \(O(QL)\), not that bound times an uncontrolled \(\tau(u)\). The resulting main for each \(d\) is precisely the BV model in the preceding prime paragraph (write \(d=j f\)); all the short–short errors per \((m,a)\) are \(O(Q^2L^2)+O_H(P\tau(m)L^{2-H})\), since \(u\ge d\). Hence the same aggregate (1) holds for \(BB^*\).

## Asymmetric local condition

For \(B(n)\Lambda(r_c)\), drop \(r=g p^i\), \(i\ge2\) or \(g>P^{.05}\), exactly as in the roughness proof, with power-saving total absolute error per modulus. For \(r=g p\), \(p\nmid P\), the squarefree divisor of \(n\) splits uniquely as \(d=e j f\), with \(e\mid\operatorname{rad}P,\ j\mid\operatorname{rad}m,\ (j,P)=1\), \((f,Pm)=1\). Then \(e\mid g, j\mid a\). Writing \(g=e t\), the conditions on \((t,p)\) are
\[
 t\mid P^\infty,\quad et\le P^{.05},\quad etp\in I,\quad
 tp\equiv P/e\pmod f,\qquad etp\equiv P-a\pmod m.
\]
We claim the prime/progression model at fixed \(g,e,j,f,a,m\), after summing as below, contributes
\[
  \frac{X}{g\,\phi(f)}\,w_a(g;m),\qquad w_a(g;m)
  =\frac{\#\{b\bmod m:(b,m)=1,\ gb\equiv P-a\pmod m\}}{\phi(m)}.
\]
In particular this local mass depends on \(g\), not on how it was split as \(e t\).

Here are the changes to the explicit conductor proof in §2 of the roughness note. On \(t\le L^{13}\) use (3) at scale \(P/(et)\) with modulus \(mf\le mQ/(ej)\). For fixed \(t\) there are at most \(m\) compatible reduced classes, and \(mf\) determines \(f\). Compared to the bound with level \(Q/e\) and no residue constraint, lose at most \(m^2\) in the square-root term for these two changes. The summed baseline small-\(t\) cost before the extra factors is \(O(PL^{-13+13/2})\). Add a further \(m\tau(m)\) for the named residues and \(j\)'s, and sum over \(m\le L^{1/10}\); the resulting cost is negligible. The first BV term allows arbitrary log powers.

On \(t>L^{13}\), split the bounded sparse coefficient into its at most \(m\) subsets \(t\equiv b\pmod m\). For each \(b,e,a\) restrict the long prime weight by \(eb p\equiv P-a\pmod m\). This is a fixed union of reduced classes in \(p\), without increasing its squared norm \(O(UL)\) in (4). The modulus \(f\) stays coprime to \(Pm\). Its large primitive conductors are bounded exactly by (4), now with level at most \(Q/e\), sparse indicator including the actual target support, and at most the additional factor \(m\) for the \(t\)-subsets. For small nonprincipal primitive conductor \(1<k\le L^{12}\), one has \((k,m)=1\). The Dirichlet character sums to zero over the reduced residues mod \(k\) in *each* fixed prime class mod \(m\); Siegel–Walfisz in modulus \(km\) thus bounds the exact central prime intervals at each \(t\) with arbitrary log saving. For the principal character Siegel–Walfisz modulo \(m\) gives the displayed \(w_a(g;m)\). The long prime always exceeds \(f\), while \(t\mid P^\infty\) is coprime to \(f\); coinduced characters therefore cause no exclusions. Multiplicity and (4) already cost \(O(P L^{-1+o(1)})\) before the new small \(m\)-powers, by \(T\gg L^{13}\). Multiplying by \(\sum_{m\le L^{1/10}}m^2\tau(m)\le L^{3/10+o(1)}\), including all \(a,j,b\), keeps this \(O(P L^{-1/3})\).

Finally, the signed \(f\)-mean is \(-S(Pm)+O_H(L^{-H})\) at \(Q/(ej)>P^{.44}\); the constant \(\log(ej)\) has zero main. Sum the factors \(\mu(e)\) at fixed \(g\): all \(g>1\) vanish as in the roughness proof. At \(g=1\), \(w_a(1;m)=1_{(P-a,m)=1}/\phi(m)\), and \(\sum_{j\mid(\operatorname{rad}m,a),(j,P)=1}\mu(j)\) removes exactly the remaining nonunit \(a\)'s (those primes of \(m\) which divide \(P\) were already excluded by the first indicator). This proves the required full \(\mathcal M_m(a)\) profile of \(B(n)\Lambda(r_c)\). Expanding \(A A^*\), and using the true-pair identity with prime-power error as in (1) of the roughness proof, now gives (2).

This is a local signed comparison at the original fixed cutoff, not an assertion of Goldbach in each admissible class: the unestimated true \(G_m(a)\) still occurs literally. The dependence of the quantitative BV error on the fixed log power in the cutoff is essential; no arbitrary polylog conductor exponent or arbitrary saving in (1)–(2) is asserted.

[Pham's 30 October v1](https://www.preprints.org/manuscript/202610.3061) treats a common exceptional set for actual primes in compatible classes and other reflected comparisons. The present class profile is instead a pointwise total-variation estimate for Pan's raw signed residual *minus its true pair count*, without estimating that count even in one admissible class. See the related references in the [physical roughness note](PanCriticalPhysicalRoughness.md).
