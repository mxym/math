# One fixed short detector has an actual finite rough signed window

Use the same original physical row \(N=2x,\ n=sq\in(x/2,x],\ m=N-n,\ (n,N)=1\) and the two actual \(\mathcal Q_i\) families of [AdjustedTriprimePositiveBudget.md](AdjustedTriprimePositiveBudget.md). Write \(w(s,q)=W_s(q)D_B(q)/\log q\), exactly bounded and positive on each family, \(L=\log x\), \(M_N=\mathfrak S(N)x/(2L)\). Choose a single fixed \(K\in C_c^\infty(\mathbb R)\) with
\[
       K(t)=1-t\quad(0\le t\le c_K),\qquad
       K(t)=0\quad(t\ge .49)
\]
for some \(c_K>0\). No sign restriction on the rest of \(K\) is needed. Define
\[
              E_K(m)=\Lambda(m)-\log m
                         \sum_{d\mid m}\mu(d)K(\log d/\log m).
\tag{1}
\]
This is exactly zero at genuine prime \(m\). On each actual whole \(\mathcal Q_i\) profile, \(\sum w(s,q) E_K(m)\) equals the original \(\sum w(s,q) C(m)\) up to \(O_A(xL^{-A})\) for every fixed \(A\).

There is a fixed \(b>1\) for which the following holds for every fixed \(R\ge2\) and \(0<\kappa<.02\):
\[
 \boxed{\quad
 \limsup_{x\to\infty,\ x\in\mathbb Z}
   \frac{1}{M_{2x}}\sum_{\substack{\mathcal Q_i\text{ physical rows}\\
             \Omega(m)>R\ \text{or}\ P^-(m)\le x^\kappa\
                          \text{or}\ m\text{ nonsquarefree}}}
                     w(s,q)|E_K(m)|
        \ll_K b^{-R}+\kappa,\qquad i=1,2 .
       \quad}
\tag{2}
\]
Here \(\Omega\) counts factors with multiplicity. For \(\omega\), the distinct-prime count, one may use any fixed \(b>1\) in the rank tail, with constants accordingly depending on \(b\). Thus **one fixed detector** can be reduced to finitely many actual squarefree polynomially rough ranks at arbitrarily small total absolute cost. The remaining ranks must be compared with their **signs**. One may not make the detector depend on the terminal rank by invoking the bounded-rank sign absorption and still use (2) at the old error: its constants depend on \(K\). The genuine [redistribution barrier](AdjustedPolynomialRedistributionBarrier.md) gives a quantitative reason why that substitution would not settle the signed problem.

## 1. The actual matched normalization

As in §1 of [AdjustedFirstTaperAllRank.md](AdjustedFirstTaperAllRank.md), the whole \(C-C'_U\) is log-small on each actual \(\mathcal Q_i\), where \(C'_U=\sum_{d\mid m,d>U}\mu(d)\log(m/d)\) and \(U=\sqrt x/H^4\). Use \(C'_U=\Lambda-\sum_{d\mid m,d\le U}\mu(d)\log(m/d)\). The support of \(K\) in (1) implies \(d\le m^{.49}<U\) for sufficiently large \(x\). Hence the difference only involves true moduli \(d\le U\), with coefficient \(\log m[(1-t)-K(t)]\), \(t=\log d/\log m\), zero whenever \(t\le c_K\).

Apply the same full-scale generalized BV to the actual independent prime \(s\) (SW) and \(1\)-bounded genuine \(q\)-mask, as in [AdjustedLowRankAbsorption.md](AdjustedLowRankAbsorption.md). The weight is smooth in the variable \(m=N-sq\) at fixed \(d\), and the sharp central product is handled by the same log-fine relative meshes; no oscillatory SW input is needed. For the exact principal at the fixed true \(n=sq\), the finite coprime \(\mu/\varphi\) constant moment has mask \(Nn\). Since the difference weight starts only at the polynomial endpoint \(m^{c_K}\), bounded variation in \(d\) and arbitrary log reserves in the finite coprime moment make the principal negligible as well. This gives the asserted whole normalization. At true prime \(m\) the only term in (1) is \(d=1\), exactly matching \(\Lambda(m)/\log m=1\).

## 2. The actual exponential-rank tilted envelope

As in §2 of the first-taper note, fix \(s\) and all but the final true prime of \(q\), grouping their product as \(B_0\), and let \(v\) be the final prime. We have primitive affine forms \(v,N-B_0v\), \((B_0,N)=1\), length \(Y\asymp x/B_0\ge x^{.144}\), and determinants/coefficients of polynomial height. The harmonic sum over all fixed genuine labels satisfies \(\sum1/B_0\ll1\). Use the same corrected [Henriot upper theorem and Corollary 2](https://arxiv.org/pdf/1102.1643), with [erratum](https://doi.org/10.1017/S0305004114000280). Put
\[
       F_\theta(m)=\prod_{p\mid m}|1-e(\theta\log p/L)|,\qquad
       {\cal E}_x(\theta)=
           \exp\left(\sum_{p\le2x}\frac{|1-e(\theta\log p/L)|}{p}\right).
\]
For the \(m\)-factor in the two-form bound take \(b^{\Omega(m)} F_\theta(m)\). This is multiplicative; at a prime power \(p^\nu\) its value is \(b^\nu |1-e(\theta\log p/L)|\). For a fixed small admissible growth exponent \(\varepsilon_{\rm H}\), take \(1<b\le 2^{\varepsilon_{\rm H}/2}\), so \(b^{\Omega(n)}\le n^{\varepsilon_{\rm H}/2}\), and \(2^{\omega(n)}\ll_{\varepsilon_{\rm H}} n^{\varepsilon_{\rm H}/2}\). Consequently the submultiplicative class condition (2.10) of Henriot holds with uniform fixed constants, for every \(\theta\) and all prime powers, by multiplicativity on coprime products. In the first form \(v\), use its roughness at \(x^{.001}\) as in the first-taper proof. At primes of \(N\) impose the true unit masks in both weights, so their exceptional multiplier has only the zero valuation. At primes of \(B_0\), the \(m\)-form is a nonzero constant, so the new power tilt does not enter that exceptional factor. The only nonzero valuations there are in the unchanged \(v\)-weight. This verifies the exceptional product with the leading coefficient, as required by the erratum, not just the discriminant.

The ordinary local \(m\)-prime value is now \(b|1-e(\theta\log p/L)|\), so the same positive Euler product and unmarking as in the first-taper note give
\[
    \sum_{\mathcal Q_i} b^{\Omega(m)}F_\theta(m)
        \ \ll_b\ \frac{\mathfrak S(N)x}{L^2}\,{\cal E}_x(\theta)^b .
\tag{3}
\]
If using \(b^{\omega(m)}\), its prime-power value is \(b|1-e(\theta\log p/L)|\) independent of \(\nu\); any fixed \(b\) then meets the growth conditions with suitable fixed constants. At fixed \(\theta\), \({\cal E}_x(\theta)\to\exp(\int_0^1|1-e(\theta t)|dt/t)\ll (1+|\theta|)^{4/\pi}\), and globally \({\cal E}_x(\theta)\ll(1+|\theta|)^2\) by the same harmonic-prime estimates as before.

The Fourier transform in (1) is literally scaled by \(\lambda=\log m/L\in[1,2]\); take \(\sup_{1\le\lambda\le2}\lambda|\widehat K(\lambda\theta)|\), rapidly decaying for each fixed \(K\). The divisor Möbius Fourier sum is exactly bounded by its integral against \(F_\theta(m)\), also for repeated prime factors. In the set \(\Omega(m)>R\) put the Markov factor \(b^{-R}\) in (3), use Tonelli and the uniform polynomial Euler bound, and multiply by the outer \(\log m\asymp L\). This gives \(O_K(b^{-R}M_N)\) for the rank tail of the divisor term. The \(\Lambda(m)\)-weight on proper prime powers is \(x^{1/2+o(1)}\) in the whole profile, and actual prime \(m\) is absent from this tail.

## 3. Physical small-factor extraction and all repeated powers

Suppose \(p\le x^\kappa\) divides \(m\) on an actual row, \(0<\kappa<.02\). Necessarily \(p\nmid NB_0\): \(p\mid N\) is excluded by the unit support; if \(p\mid B_0\), then \(p\mid m=N-B_0v\) would imply \(p\mid N\). At fixed \(p,B_0\) write \(v=v_0+pu\), with \(0\le v_0<p\) the true reduced residue \(N\overline{B_0}\bmod p\). Then the actual affine pair in \(u\) is
\[
           v_0+p u,\qquad (N-B_0v_0)/p-B_0u,
\]
the second form exactly \(m/p\). Both are primitive, their determinant has absolute value \(N\), and \(u\) ranges at a polynomial scale comparable to \(Y/p\ge x^{.124}\). At \(p\), the first form is a nonzero constant and the second has one ordinary root. All other leading coefficient exceptions are already among the fixed \(B_0\)-primes, and primes of \(N\) meet the same unit masks. This is a legal instance of the same corrected two-form bound with fixed height margin, not just an arithmetic progression estimate on a putative final prime.

Extract the factor \(a_p(\theta)=|1-e(\theta\log p/L)|\); put the prime-power value of the remaining multiplicative Fourier weight on \(m/p\) equal to \(1\) at \(p\). This handles \(p^2\mid m\) exactly, rather than counting it twice. The local change costs at most an absolute factor in the Euler and leading-coefficient envelopes. The resulting bound, summed over the fixed outer labels, is
\[
 \sum_{\mathcal Q_i,\ p\mid m} F_\theta(m)
       \ \ll\ \frac{\mathfrak S(N)x}{p L^2}\,
                    a_p(\theta){\cal E}_x(\theta).
\]
Using \(a_p(\theta)\le 2\pi|\theta|\log p/L\) and \(\sum_{p\le x^\kappa}\log p/p\ll\kappa L\) at fixed \(\kappa\), sum the prime labels for a union bound. The additional \(|\theta|\) is absorbed by the rapidly decreasing fixed Fourier transform, uniformly for the possible log dilation \(\lambda\). Thus the full divisor weight of these small-prime rows is \(O_K(\kappa M_N)\), with a constant independent of small fixed \(\kappa\). Again proper prime powers cost negligibly, and true prime \(m\) contributes nothing.

Finally repeated prime bases \(p>x^\kappa\) satisfy \(\#\{m\le1.5x:p^2\mid m\text{ for some such }p\}\ll x^{1-\kappa}\) by a sum of \(x/p^2\). On these rows use \(|E_K(m)|\ll_K L(1+\tau(m))\), the bounded number of eligible \(s\) at any physical \(m\), and the ordinary \(\tau^2\) moment with Cauchy. The absolute cost is \(x^{1-\kappa/2}L^{O(1)}=o(M_N)\) at fixed \(\kappa\). Together all three estimates prove (2).

After choosing \(K,\kappa,R\) in that order, the remainder of the genuine profile has only distinct reflected primes above \(x^\kappa\) and ranks at most \(R\). It is still a fixed-target **signed** sum over the exact equation \(m+s q=N\), not a claim that independent product counts are sufficient to compare those ranks. No full \(.010M_N\) inequality or Goldbach conclusion follows from this truncation.

## Comparison

The [coupled rough-window estimate](finite_rough_window/Proof.md) concerns the squarefree product of both original arguments. The [smooth-sieve literature note in the twin-prime project](https://github.com/solveathome/twin-primes/blob/main/research/smooth-sieve-literature.md) uses corrected Henriot bounds on a fixed difference; here the determinant and affine small-prime split come from the actual moving target. Compare [Pham’s October preprint](https://www.preprints.org/manuscript/202610.3061) for separate fixed-target rough comparisons. The November search is not a priority claim.
