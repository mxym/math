# Coupled smooth cutoffs give two disjoint actual negative sectors

Use the genuine target and normalization of [DoubleSmoothBoundedRankResidual.md](DoubleSmoothBoundedRankResidual.md): \(N=2x\), \(L=\log x\), \(n=sq\in(x/2,x]\), \(m=N-n\), \((n,N)=1\), and \(x^{.10}<s<x^{.14}\) a true prime. Write \(M_N=\mathfrak S(N)x/(2L)\) and \(W_s(q)=K_{P_3}(sq)\). The original genuine prime-quotient statistic is \(\mathcal T_{\rm p}(C)\). All the opened sums below have integer \(q\), with the same exact physical domain.

There is an equivalent joint coefficient \(K(m,q)\), a sum of three products of smooth coefficients, for which **both** of the following disjoint sectors have uniformly negative actual contribution:
\[
\begin{array}{ll}
 P^-(m)>x^{.20},\quad P^-(q)>x^{.070}
     &\displaystyle \sum W_s(q)K(m,q)\le -.16 M_N,\\[2pt]
 P^-(m)>x^{.20},\quad q=p t w,\quad P^-(w)>x^{.070},\\
 \qquad .015<\log_x p<.035,\quad .056<\log_x t<.067,
      \quad p,t\ \textrm{true primes}
     &\displaystyle \sum W_s(q)K(m,q)\le -.10 M_N .
\end{array}
\tag{1}
\]
The constants hold for an appropriate fixed smooth neck width and all sufficiently large even \(N\), independently of \(N\). These are entire reflected macro-rough sectors for each stated quotient condition, not a selection of only favorable physical ranks. Neither (1) nor their sum supplies an upper bound for the rest of the row.

## 1. Exact cutoff exchange without a sectorwise prime-row transfer

Take \(\delta\in(0,.01)\), to be fixed small. Let \(b(t)\) for \(t\ge0\) be a smooth function valued in \([0,1]\), equal to 1 for \(t\le 1/2-2\delta\), and zero for \(t\ge 1/2-\delta\). Set
\[
   g_0(t)=-b(t),\qquad g_1(t)=(2t-1)b(t).
\]
Both define legitimate forward weights in the theorem of [DoubleSmoothBoundedRankResidual.md](DoubleSmoothBoundedRankResidual.md): take \(f_{m,1}=b\) and \(f_{m,0}=g_0/(2t-1)\) below \(1/2-\delta\), extended by zero past the cutoff. Both equal 1 at 0; the latter is smooth and need not be constant near zero. For that issue, the proof of the whole replacement only requires the averaging support bounded away from 0. Arrange \(g_0(t)=2t-1\) on \([0,\zeta]\) using a smooth blend to \(g_0=-1\) by \(2\zeta\), with fixed \(0<2\zeta<.20\); this gives \(f_{m,0}=1\) near 0 without changing any composite with \(P^-(m)>x^{.20}\), since all its nonunit divisors have \(\log d/\log m>.20-o(1)\). In the rest of the note \(g_0\) denotes this modified smooth function. The resulting signed averaging densities \(-f'_{m,i}\) both have integral 1 and fixed compact support inside \((0,1/2)\). All proofs of the whole replacement go through for signed densities: the uniform absolute errors are multiplied by their finite total variation. The functions' smoothness and normalizations are unchanged. Let \(Z_i(m)\) be the literal composite coefficient (1) of that note for \(g_i\), zero on prime powers.

For the reverse coordinate fix \(Y=x^{.070}\). Take \(f_1\) in [SmoothReverseCoreShield.md](SmoothReverseCoreShield.md) equal to 1 on \([0,.97]\) and zero above \(.99\) in \(\log d/\log Y\) coordinates. Take \(f_2=f_1-\frac12\theta_1-\frac12\theta_2\), where \(\theta_1,\theta_2\) are fixed disjoint smooth cutoffs supported within \((0,.97)\) and equal to 1 respectively on \([.015/.070,.035/.070]\), \([.056/.070,.067/.070]\). Again \(-f_2'\) is a signed compactly supported smooth density of integral 1, bounded away from the reverse cutoff zero and one. Denote the effective coefficients by \(B_1,B_2\). The uniform proof of their whole replacement and the proof of (2) in the double-smooth note use only finite variation in these signed averages. Thus each of the four actual whole rows \(\sum W_s Z_i B_j\) equals \(\mathcal T_{\rm p}(C)+o(M_N)\). Define
\[
 K(m,q)=Z_0(m)B_1(q)+(Z_1(m)-Z_0(m))(B_1(q)-B_2(q))
        =Z_1(m)B_1(q)-Z_1(m)B_2(q)+Z_0(m)B_2(q).
\tag{2}
\]
It follows **globally** that \(\mathcal T_{\rm p}(C)=\sum W_s(q)K(m,q)+o(M_N)\). No identity transferring a restricted sector from an opened row to a true-prime \(q\)-row is used.

When \(q\) has no core up to \(Y\), both \(B_i=\Lambda(q)/\log q-1\) exactly. Thus \(K=Z_0 B_1\) there. In the second sector of (1), the exact small core is \(z=pt\), with \(z>Y\) since \(.015+.056>.070\), and both single primes below \(Y\). For \(i=1,2\) the formula of the reverse shield gives \(R_i(z)=-1+f_i(\log p/\log Y)+f_i(\log t/\log Y)\), since the product argument is past the support. Therefore \(R_1=1,R_2=0\), and here \(K=Z_1\log w/\log q\). The exact small-core exceptions involving powers of base \(\le Y\) cannot occur in this marked family; for the no-core family the no-core formula covers all powers. There is no such simplified formula for arbitrary other cores.

## 2. No-core sector uses actual triprime compensation

Prime powers of \(q\) beyond primes and all non-squarefree macro-rough \(m\) have negligible total weight, by the divisor envelopes and the same power-small physical count as in the double-smooth note. On the no-core branch the effective multiplier \(B_1\) is 0 on actual prime \(q\) and \(-1\) on non-prime-power composites. Keep this exact subtraction rather than viewing the quadrant as prime-quotient.

For squarefree composite \(m\) of **even** rank, if no divisor has
\[
          1/2-2\delta \le \log d/\log m \le 1/2+2\delta,
\tag{3}
\]
then \(Z_0(m)=0\) on the macro-rough domain. Indeed each complementary pair \(d,m/d\) has equal \(\mu\); the lower divisor is in the region where \(g_0=-1\), including \(d=1\) with \(g_0(0)=-1\). The upper divisor is in the region where \(g_0=0\). Thus \(Z_0/\log m=-\frac12\sum_{d\mid m}\mu(d)=0\). The same cancellation holds whenever the low member is below \(1/2-2\delta\), irrespective of any tiny-modification band outside the current macro support. There are only ranks 2 and 4 among the even composites here. At the exact physical threshold \(x^{.20}\) rank five is not empty automatically: it lies in \(u_i=.20+O(1/L)\) for all five indices, because \(m\le3x/2\). For each fixed \(\varepsilon>0\) bound it by the fixed \(\varepsilon\)-neighborhood of that single simplex point, apply (5) and the same linear upper sieve with bounded pointwise rank-five coefficients, then let \(\varepsilon\downarrow0\). Its total contribution is \(o(M_N)\) in both sectors of (1); this uses the full five-prime product BV with polynomial groups. Ranks above five are empty eventually.

For rank 3 put the ordered log proportions \(u_1\le u_2\le u_3\) on the simplex \(u_1+u_2+u_3=1\), so \(u_i\ge .20-o(1)\). The two least are \(\le .40+o(1)\), hence in the constant region; all two-factor divisors except the possible pair of those least two are above the cutoff. The exact coefficient is
\[
            Z_0(m)/\log m=1-g_0(u_3)+g_0(1-u_3)\ge0
\tag{4}
\]
because \(-1\le g_0\le0\) on this macro range. If \(u_3\le .48\) then (4) equals 2, since \(\delta<.01\). This provides an actual net sign on every rank-three physical point of this sector.

Here and in §3 the uniform positive arithmetic counts use the following elementary application of **full-scale prime-product BV plus dimension-one sieve**. For a fixed compact exponent region in the simplex of the \(k\ge2\) distinct macro prime factors of \(m\), its density relative to \(x/(2L)\) on the actual central \((x,3x/2)\) interval is
\[
              D_k=\int_{\mathrm{sorted\ region}}
                    \frac{du_1\cdots du_{k-1}}{u_1\cdots u_k}.
\tag{5}
\]
The PNT gives (5) as in [TwoMarkNegativeCompensation.md](TwoMarkNegativeCompensation.md), with the factor-unit mask \((m,Ns)=1\) costing \(o(1)\) in this density, uniformly: primes \(\ge x^{.20-o(1)}\) dividing \(Ns\) have total reciprocal weight \(x^{-.20+o(1)}\). For constant smooth or linear exponent constraints, approximate by finite rectangular cells with positive lower/upper approximations. Each cell is governed by [Maynard I, Lemma 8.9](https://ora.ox.ac.uk/objects/uuid%3A39a52f47-3770-4ddd-b7a2-b2a4f7300931/files/srj4305733), at the full \(m\) scale with two grouped lengths polynomially long and one genuine SW prime group. Product interval \(m\in(x,3x/2)\) is handled by the standard sharp product mesh as in [FullScaleConvolutionBV.md](FullScaleConvolutionBV.md). For the cut (3), singleton or partial-sum walls are affine on the compact simplex; thickening by mesh size \(o(\delta)\) with \(\delta\) fixed shows total reference density \(O(\delta)\) (all \(1/u_i\) bounded here). One may first fix a sufficiently fine mesh in terms of \(\delta\) and then take \(x\to\infty\). In rank 4 the only walls are in fact two-factor walls; rank 2 uses singleton walls. This proof does not require joint distribution of m's factors *and* the integer quotient's factors.

For the no-core family the sieve variable is \(q=(N-m)/s\), and \(q\equiv0\bmod e\) gives the true progression \(m\equiv N\bmod se\). Up to \(D=x^{.280}\) or \(x^{.355}\), respectively, all moduli are below \(x^{.50}\) with fixed slack. The local factors and BV summation are those in [NoCoreAdverseSign.md](NoCoreAdverseSign.md): here all retained m factors are \(>x^{.20}\), so one may sieve to \(y'=x^{.1775}\) for the upper bound on true-prime \(q\), safely below every m factor and below actual prime \(q\). At a sieve prime equal to the outer prime \(s\), the true local factor is \(1-1/s\) rather than \(1-1/(s-1)\); equivalently omit it in the upper sieve, with multiplicative cost \(1+O(1/s)\). This does not affect the stated uniform limit. With \(D=x^{.280}\) at \(Y=x^{.070}\), the normalized lower rough coefficient is \(\log 3/.140-o(1)\); with \(D=x^{.355}\) at \(y'=x^{.1775}\), the normalized upper prime coefficient is \(2/.355+o(1)\). They have the same singular normalization \(\mathfrak S(Ns)/(s-1)\) on \(x/(2L^2)\). The difference is \(>2.20\) eventually. For the upper bound on arbitrary no-core quotient at the negligible neck one may just use the linear upper sieve at \(D=x^{.210}\), normalized \(O(1)\). Divisor multiplicities across \(s,e\), the bounded physical \(W_s(q)\), and the uniform unit mask are as in the cited notes. Thus the entire even-rank neck contribution in the no-core sector has absolute bound \(O(\delta M_N)+o(M_N)\), with an implied constant independent of how the smooth function transitions (use \(|Z_0|\le2^4\log m\)).

For the balanced rank-three subregion \(u_i\ge .20,u_i\le .48\), the sorted area is
\[
          ((1-.60)^2-3(.52-.40)^2)/12 .
\]
Indeed the removed corners are disjoint on this simplex and the symmetry factor is 6. Since \(u_1u_2u_3\le 1/27\), its density (5) is \(\ge.2628\). If desired shrink both endpoints strictly by fixed arbitrarily small amounts and retain a density \(>.260\). This makes all physical \(x^.20\) boundaries strict. On the finite subregion the exact \(W_s(q)\) differs by \(O(L^{-1})\) from \((1-\log_x s)(1-2\log_x s)^2>.44\), and the prime harmonic \(s\)-band tends to \(\log(7/5)>.336\); removing \(s\mid N\) changes it by \(o(1)\). The semiprime neck and rank-four errors can be made arbitrarily small by choosing \(\delta\) small independent of \(x\). The strictly favored term therefore has magnitude at least
\[
            2\cdot .260\cdot 2.20\cdot .44\cdot .336\ M_N+o(M_N)
                           > .169 M_N+o(M_N).
\]
All other rank-three terms are nonpositive. This proves the first bound in (1) on choosing \(\delta\) with small enough fixed reserve.

## 3. The marked sector automatically takes the other parity kernel

For squarefree composite \(m\), the \(Z_1\) coefficient differs from
\[
       F(m)=\sum_{d\mid m}\mu(d)\min(\log d,\log(m/d))
]
by \(O(\delta\,\tau(m)\log m)\). This follows by replacing \(b\) by \(1_{t<1/2}\): the multiplier \((2t-1)b(t)\) changes by \(\le4\delta\), and the resulting divisor sum is \(F(m)\), since \(\sum_{d\mid m}\mu(d)\log(m/d)=0\). In particular rank three has absolute contribution \(O(\delta\log m)\), using the exact complement cancellation of \(F\) on odd ranks. On a true squarefree semiprime with smaller prime log proportion \(u\) the literal formula is
\[
             Z_1(m)/\log m=-1+(1-2u)b(u)\le-2u ,
\]
and the normalized negative weighted semiprime density from \(u\in[.20,1/2]\) is
\(\int_{.20}^{1/2}2/(1-u)\,du=2\log(8/5)>.94\).
On rank four use \(|F(m)|\le 2^{3}\min_i\log p_i\le2\log m\) by pairing divisors differing by the least prime; the Lipschitz constant of the piecewise-linear minimum is 1. The positive weighted density is no larger than
\[
          2\frac{(1-.80)^3}{4!3! (.20)^3(.40)}
                          =\frac5{144}<.035 ,
]
because the product of the four proportions is minimized at simplex vertices. The \(O(\delta)\) smoothing error has the same fixed proper prime-product upper sieve and is uniform.

In the marked family use the true \(w=(N-m)/(spt)\) sifted to \(Y\), at level \(D=x^{.210}\). The actual \(s p t e\) moduli are \(\le x^{.14+.102+.210}=x^{.452}\), with the exact local law of [WholePositiveSmallCore.md](WholePositiveSmallCore.md): for primes dividing \(pt\) the local density is \(1/p'\), for primes dividing \(N\) zero, and otherwise \(1/(p'-1)\). In particular the common singular factor after the sieve and base reduced main is \(\mathfrak S(Nspt)/((s-1)pt)\), not \(1/\phi(pt)\) in isolation. All m factors are above the sieve range. The lower/upper dimension-one coefficients are \(2\log2/.210-o(1)\) and \(2/.210+o(1)\). The Marked factors are unique since their bands are disjoint, both are \(\le Y\), and the remainder has no prime \(\le Y\). Also \(\log w/\log q\ge.87\), since \(\log_x(pt)\le.102\) and \(\log_x q\ge.86-o(1)\). Use this lower factor in the negative rank-two estimate and 1 for the positive estimate. With \(\delta\) sufficiently small, the net negative per common label is thus \(>4.9\), using
\[
         (.87\cdot .94\cdot 2\log2-.035\cdot 2)/.210>5.03.
\]
Strict exponent or order boundaries can be frozen first with small slack, as in §2. The harmonic over true disjoint markers equals
\[
          \log(35/15)\log(67/56)+o(1)>.15+o(1).
\]
For these elementary numerical inequalities one can use the positive series \(\log r=2\sum_{k\ge0}((r-1)/(r+1))^{2k+1}/(2k+1)\), with lower truncation (and the geometric upper tail when required). Excluding primes dividing \(N\) has \(o(1)\) harmonic cost. The actual \(W_s\) and harmonic sum have the same \(.44\) and \(.336\) lower margins as above, and \(\mathfrak S(Nspt)\ge\mathfrak S(N)\). Hence the actual marked sector is \(\le-.10 M_N\), because \(4.9\cdot .15\cdot .44\cdot .336>.108\). This has no overlap with the no-core sector.

The new sign on no-core arises by replacing the adverse even-rank kernel by the odd-rank kernel and using actual triprime counts, while the coupled correction independently keeps the favorable marked-sector sign. The two bounds are for (2), not additions to older bounds from an inequivalent restricted row. Outside these sectors (including other cores and smaller reflected prime factors), the actual signed kernels may change in either direction. No unconditional bound on their aggregate relative to the available \(.010M_N\) threshold, and no binary Goldbach proof, follows.

## Comparison with 2026 work

[Arneth's September signed-coefficient and conditional-compensation note](https://zenodo.org/records/23016346) includes balanced-factor identities and discusses the difficulty of prime-filtered compensation. [Pham's October v1](https://www.preprints.org/manuscript/202610.3061) gives different reflected rough and signed boundary comparisons. The result here is the two freely chosen exact whole-row cutoff pairs and unconditional signs on the two stated opened sectors, not a result on their joint complement or a priority claim about general parity compensation.
