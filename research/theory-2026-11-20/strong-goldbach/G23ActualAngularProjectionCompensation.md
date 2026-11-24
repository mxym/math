# Genuine prime/composite compensation in the angular-bin projection

Written research note, 2026-11-24. All slopes, reflected primes and composite Liouville weights are actual as in the [true prime-reflection layer](G23TruePrimeReflectionLayer.md) and the [rough weighted dispersion](SmallRadicalWeightedCoprimeDispersion.md). This handles a nontrivial weighted Hilbert projection at the true prime-layer scale, not the full dispersion statistic.

Let \(P=2^j\), \(L=\log P\), \(J=[a,b]\Subset(0,1)\), \(p\) prime in \((P^\sigma,D]\), \(D=P^{1/2}e^{-L^{3/5}}\), and \(W(p,k)=1_{pk\in PJ}\log(pk)/L\). Define \(B_C(k)=\sum_p W(p,k)C(P,pk)1_{P-pk\ {\rm prime}}\); \(H_C(k)\) replaces the last indicator by \(R_y(P-pk)1_{P-pk\ {\rm composite}}\lambda(P-pk)\). Write \(A_C=H_C-B_C\), which is exactly the genuine rough Liouville vector, since \(\lambda=-1\) on primes and the reflected arguments are comparable to \(P\). Let \(\langle f,g\rangle=\sum_k kR_z(k)f(k)g(k)\). Here \(C=1\) or the actual translated first-cover mark with fixed \(M\ge400\). Fix \([u,v]\Subset(1/2,1-\sigma)\). Partition this interval in \(t=\log k/L\) into equal bins of width \(h\asymp L^{-2}\), with the total number of bins chosen as \(\lceil(v-u)L^2\rceil\). Let \(\Pi\) denote orthogonal projection onto the span of \(e_i(k)=1_{\{\log k/L\in I_i\}}/k\) for these disjoint angular bins. The underlying real \(k\) width is a constant times \(P^{t_i}/L\), not a fixed fraction of \(P^{t_i}\).

**Claim.** Put \(\kappa_z=\prod_{\ell\le z}(1-1/\ell)\), \(V_z(P)=\prod_{\ell\le z,\ \ell\nmid P}(1-1/(\ell-1))\), and \(S_2=2\prod_{\ell>2}(1-1/(\ell-1)^2)\). Then
\[
\|\Pi B_C\|^2\sim
(b-a)^2 S_2^2\left(\int_u^v\frac{dt}{(1-t)^2}\right)
\frac{P^2\kappa_z}{L^3},
\qquad
\|\Pi(H_C-B_C)\|^2=o(P^2\kappa_z/L^3).
\]
In particular \(\langle\Pi B_C,\Pi H_C\rangle=(1+o(1))\|\Pi B_C\|^2\); the genuine signed composites match the actual reflected-prime vector in these coarse directions, whose energy is a positive fraction, bounded away from zero for fixed parameters, of the known \(\|B_C\|^2\asymp P^2\kappa_z/L^3\). The fraction is not asserted to tend to one. The residual is the orthogonal complement of these particular step-bin directions, not an assertion about Fourier frequencies.

**1. Fixed-target unmarked Type I in a moving physical bin.** For any real interval \(\mathcal K\) inside the full allowed \(k\)-range and any fixed \(E>0\),
\[
 \left|\sum_{k\in\mathcal K} R_z(k)A_1(k)\right|\ll_E P L^{-E},
\]
uniformly in the two physical endpoints. For fixed \(p\), intersect \(\mathcal K\) with \([aP/p,bP/p]\) before reflecting to \(m=P-pk\); this is an actual \(p\)-dependent interval for \(m\), not a separately frozen \(k\)-endpoint approximation. Open the two literal rough indicators with upper Bonferroni polynomials through \(O_E(\log L)\) factors and one more layer for the error, as in the [near-root Type I note](SmallRadicalShiftedHighChambers.md). On the true support one may first impose \((k,P)=1\) (equivalently \((m,P)=1\) since \(p\nmid P\)), then expand only primes not dividing \(P\). The retained tests are \(d\mid k\), \(e\mid m\) with \(\log d,\log e=O_E(L^{.24}\log L)\). In every nonempty tuple \((pd,e)=1\), since otherwise a common prime divides \(P\), contrary to the unit support or the true prime range \(p>z\). The lattice for \(m'=m/e\) is therefore \(m'\equiv P e^{-1}\bmod pd\), together with its exact target unit condition; CRT with \({\rm rad}(P)=2\) introduces only reduced classes. Its true endpoints are comparable to \(P/e\), and the modulus \(\le D d\cdot 2\) is below the full square-root BV level there, since the extra logs are \(o(L^{3/5})\). The sign is \(\lambda(e)\lambda(m')\). Use the arbitrary-log full-level uncentered Liouville BV justified in the [near-root Type I note](SmallRadicalShiftedHighChambers.md) by [Granville–Shao, Theorems 1.1(b), 2.1](https://arxiv.org/html/1706.05710v1), with its exact reduced-class and prime-restriction hypotheses. In particular maximal endpoints at this scale follow from the fixed-endpoint result on a mesh of spacing \(X/L^C\) for \(X=P/e\), extending to arbitrary endpoints by the trivial \(O(X/(qL^C)+1)\) progression bound for \(|\lambda|\le1\); both \(C\) and the saving requested at the sampled endpoints may be taken arbitrarily large. The weight \(\log(P-em')/L\) on the restricted \(m'\) interval has uniformly bounded variation. For each \(e\), moduli \(pd\) are distinct (the only prime \(>z\) is \(p\)); sum the resulting errors over \(e\) using \(\sum 1/e\ll L^{O(1)}\).

For completeness, count the discarded Bonferroni shell in absolute value: upper polynomials dominate both true indicators and their product differs from the indicators' product by at most one shell times the other upper polynomial plus the other shell. Each CRT tuple costs \(O(P/(pde)+1)\) in a nonempty unit class. The factorial reciprocal shell can be made \(O_E(L^{-E})\), using \(\sum_{\ell\le z}\ell^{-1}=O(\log L)\) and choosing the depth's fixed constant large; \(\sum_p1/p=O_\sigma(1)\), all remaining divisor harmonic sums are at most log powers, and there are only \(P^{1/2+o(1)}\) tuples for the floor terms. This proves the unmarked bound uniformly in \(\mathcal K\).

**2. True prime density in the same bins.** On the true prime support \(m=P-pk\asymp_J P\), the k-exclusions at primes dividing \(P\) hold automatically. For \(d\) a retained squarefree product of the other primes \(\le z\), test \(m\equiv P\bmod pd\), a reduced class on the literal reflected interval \(P-p(\mathcal K\cap[aP/p,bP/p])\). The local prime model is \(1/\varphi(pd)\). By prime BV with maximal endpoints at the true endpoint comparable to \(P\), the aggregate error is \(O_E(P L^{-E})\); \(pd\le D e^{o(L^{3/5})}\) and p,d are determined uniquely by pd. Partial summation imposes the weight and unweights the reflected prime. Bonferroni shell bounds follow either from the same BV for one extra layer or by trivial floors as in the preceding paragraph. The model gives, uniformly,
\[
 \sum_{k\in\mathcal K}R_z(k)B_1(k)
 =
 V_z(P)\sum_p \frac{p}{p-1}
   \int_{\mathcal K\cap[aP/p,bP/p]}
     \frac{\log(pk)/L}{\log(P-pk)}\,dk
   + O_E(PL^{-E}).
\]
Indeed changing variables from m to k supplies Jacobian \(p\); the factor from the rough k sieve over d is exactly \(V_z(P)\).

For k in the prescribed interior angular range, \(p\in[aP/k,bP/k]\) lies entirely within the genuine original prime range for sufficiently large P, since \(u>1/2\) and \(v<1-\sigma\) by fixed margins. After interchanging sum and integral, true PNT uniformly in these p endpoints (or ordinary maximal PNT with partial summation) gives prime count
\[
 (1+o(1))\frac{(b-a)P}{kL(1-t)} ,\qquad t=\log k/L,
\]
since the endpoints are fixed multiples of \(P/k\), grow polynomially, and \(\log p=L(1-t)+O_J(1)\). On the same support \(p/(p-1)=1+o(1)\), \(\log(pk)/L=1+O_J(1/L)\), and \(\log(P-pk)=L+O_J(1)\), all uniformly. Hence for the bin \(I_i\)
\[
 \langle B_1,e_i\rangle
 = (1+o(1))\frac{(b-a)PV_z(P)}{L}\int_{I_i}(1-t)^{-1}\,dt
\]
uniformly, including for width \(h\asymp L^{-2}\); the arbitrary-log BV error is smaller than the smallest bin main term. The analogous integer Bonferroni sieve for \(R_z(k)\) gives \(\|e_i\|^2=\sum_{k:\log k/L\in I_i}R_z(k)/k=(1+o(1))\kappa_z Lh\) uniformly. Its retained integer lattice floors times \(1/k\) are \(P^{o(1)}/P^u\) per bin, and an arbitrarily small harmonic shell is available; the real integral is \(Lh\). Mertens gives \(V_z/\kappa_z\to S_2\).

Now sum \(\langle B_1,e_i\rangle^2/\|e_i\|^2\) over the orthogonal directions; the Riemann sums converge to the displayed integral. Sum the squares of the arbitrary-log Type I error over the \(O(L^2)\) bins divided by \(\|e_i\|^2\asymp\kappa_z/L\); this proves \(\|\Pi A_1\|^2=o(P^2\kappa_z/L^3)\). The same reasoning allows any fixed log-polynomial angular mesh for the unmarked vector.

**3. Exact marker transfer in the projected norm.** The actual \(M\)-translated first-cover rough [marked rough co-sieve](G23ActualMarkedAverageDispersion.md) bounds the count of missed \(n\in PJ\) with both literal rough filters by \(O(P\kappa_z V_y(P)L^{-M/200})+O_E(PL^{-E})\). On a true slope row \(n=pk\), \(p>z\), so \(R_z(k)=R_z(n)\); the literal marks are the same; each n has at most \(1/\sigma\) true slope divisors p. Thus for both \(F=B\) and \(F=A\) the sum over bins of \(|\langle F_C-F_1,e_i\rangle|\) is bounded by the same expression times \(O_\sigma(1)\). For B the true prime reflected support already has the rough y condition. Divide the square of this total by \(\min_i\|e_i\|^2\asymp\kappa_z/L\). Relative to \(P^2\kappa_z/L^3\), the bound is \(O(V_y(P)^2L^{4-M/100})+o(1)=o(1)\) for \(M\ge400\), since \(V_y(P)\asymp L^{-\delta}\). This proves both marked statements by the triangle inequality. There is no reliance on assumed independence between the mark and a prime. Larger fixed M similarly allows finer log meshes.

**Limits.** This is an actual guaranteed order-of-magnitude contribution in the exact weighted k space, and not just an equality between scalar totals: zeroing arbitrary orthogonal oscillations would be an additional theorem. In the full mixed inner product the complementary term \(\langle(1-\Pi)B_C,(1-\Pi)H_C\rangle\) is still not controlled. It includes edge k angles outside the chosen interior and oscillatory or drifting structure within finer intervals, rather than a class that can be dismissed by referring to high Fourier frequencies. No G23 bound at its full pointwise target scale, P3, or Goldbach conclusion follows.


## Exact moving angle range and deletion of physical boundary pieces

In fact one may take the exact moving interior
\[
 {\cal K}_*=[bP/D,\;aP/P^\sigma],\qquad
 (u_P,v_P)=\left(\frac{\log(bP/D)}L,\frac{\log(aP/P^\sigma)}L\right).
\]
Every k in this interval has the entire prime window \([aP/k,bP/k]\) within \([P^\sigma,D]\), up to endpoint conventions. The proof above is uniform in these moving endpoints: all relevant p are still polynomial, \(1-t\) is bounded away from 0, and \(v_P-u_P\) tends to \(1/2-\sigma>0\). Choose the number of equal angular mesh cells \(\lceil (v_P-u_P)L^2\rceil\) as before. The resulting deterministic norm coefficient is the full
\[
 (b-a)^2 S_2^2\int_{1/2}^{1-\sigma}(1-t)^{-2}\,dt
  = (b-a)^2 S_2^2(1/\sigma-2).
\]
The only omitted real k support consists of \([aP/D,bP/D]\) and \([aP/P^\sigma,bP/P^\sigma]\) with fixed multiplicative widths. In the lower edge the first legal slope p lies between \((a/b)D\) and D; in the upper edge it lies between \(P^\sigma\) and \((b/a)P^\sigma\). Hence each edge uses only \(O_J(1)\) first-prime dyadic boxes. The genuine prime-pair [bound for the real prime layer](G23TruePrimeReflectionLayer.md) gives absolute prime square edge cost \(O(P^2\kappa_z/L^4)+P^{2-\sigma+o(1)}\) (including the global diagonal bound). The proof of the genuine mixed near-diagonal deletion in the [companion actual mixed chambers note](G23ActualMixedFactorChambers.md) gives, without imposing its close-gap restriction, \(O(P^2\kappa_z V_y(P)/L^3)+P^{1.54+o(1)}\) **per** slope box: use its fixed-pair one-prime/rough count and the unrestricted genuine prime pair singular average \(O(U^2/L^2)\). Since \(V_y(P)\to0\) for powers of 2, the absolute mixed contribution of the two edges is \(o(P^2\kappa_z/L^3)\), also with the actual marks. This uses no bound for the full composite square on the edges.

Writing \(B_{\rm int},A_{\rm int}\) for restrictions to the exact interior and \(B_\perp=(1-\Pi)B_{\rm int}\), \(A_\perp=(1-\Pi)A_{\rm int}\), the rigorous consequence is
\[
 \langle B_C,H_C\rangle-\|B_C\|^2
   =\langle B_\perp,A_\perp\rangle+o(P^2\kappa_z/L^3).
\]
Thus physical edges and all angular block indicators have genuinely been removed from the missing weighted matching calculation. The remaining real vectors have zero block projection and are supported on the true interior; they can drift or oscillate **within** the mesh (physical relative scale about \(1/L\) at the fixed M), and this does not identify them with global high Fourier frequencies or prove their mixed inner product negligible.


## The actual source sign lies outside the controlled projection

For the genuine G23 source vector \(g(k)=\lambda(k)/k\), restricted to the same interior, one has for every fixed \(E\),
\[
 \|\Pi g\|^2\ll_E L^{-E},\qquad
 \|g\|^2=\sum_{k\in{\cal K}_*}R_z(k)/k\sim
 \kappa_z L(1/2-\sigma).
\]
Indeed uniformly for a polynomial endpoint \(X\asymp P^t\) in the relevant range, the exact complete-multiplicativity formula gives
\(\sum_{k\le X}\lambda(k)R_z(k)=\sum_{d\mid\prod_{\ell\le z}\ell}\sum_{m\le X/d}\lambda(m)\).
For \(d\le\sqrt X\) use arbitrary-log cancellation of uncentered Liouville prefixes (the zero-frequency case of Davenport, with square convolution from Möbius), and \(\sum d^{-1}\ll\log z\). For \(d>\sqrt X\), the factor \(d^{1/\log z}\) gives reciprocal Rankin tail \(\ll e^{-(\log X)/(2\log z)}(\log z)^{O(1)}\), because every \(\ell^{1/\log z}\le e\). This proves \(O_A(XL^{-A})\) uniformly for all such endpoints. Partial summation over each true physical bin gives \(\langle g,e_i\rangle=\sum_{k\in{\cal K}_i}\lambda(k)R_z(k)/k=O_A(L^{-A})\). Dividing squares by \(\|e_i\|^2\asymp\kappa_z/L\) and summing \(O(L^2)\) bins gives the first claim; the second is the integer rough harmonic density. Thus the controlled angular step directions cannot by themselves settle the original \(-L\langle g,A_C\rangle\): the source weights already have negligible projection onto the directions on which the genuine prime/composite matching has been proved.

For the distinct prime/composite **matching** question, an explicit sufficient (unproved) concentration rate is \(\|B_\perp\|^2=o(P^2\kappa_z/(V_y(P)^2L^5))\). Indeed the true unsigned rough-vector [unsigned rough-vector energy](SmallRadicalWeightedCoprimeDispersion.md) bounds \(\|A_\perp\|^2\ll P^2\kappa_z V_y(P)^2/L\); Cauchy then makes the residual mixed pairing \(o(P^2\kappa_z/L^3)\). The sufficient rate is a relative \(o(L^{-2+2\delta})\) of the true prime energy on powers of 2, so an unquantified asymptotic for that energy would not by itself pay the measured matching error. This would still not establish the original full G23 squared norm.
