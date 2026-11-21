# Uniform signed small-core rank transfers in the same-cofactor cell

This advances the fixed-power transfer to an **actual paired, fixed-target signed** estimate. With a small constant macro threshold, the *entire* reflected four-prime small-core cohort has a uniform negative contribution, including its adverse angular chambers and both genuine source ranks. The entire two- through five-prime small-core sum is nevertheless positive. Thus the first negative estimate is not a net allowance credit.

## 1. Literal physical cohorts and theorem

Use \(G_N,C_s(u),M_N,x,L,N,m=N-su\) and fixed marker \(\delta\) from [SameCofactorVaughanCenter](SameCofactorVaughanCenter.md). The genuine source has prime \(s\in[x^{.10},x^{.14}]\), and \(u\) is either prime or a balanced product of two distinct primes, with the two actual opposite scores specified there. Fix \(0<\theta\ll1\), then \(0<\rho\ll1\); put \(U=x^\theta,\ \eta=\rho\theta,\ z=x^\eta\). The \(x\)-limit is last, with both parameters fixed.

This is a different decomposition of the **same** \(G_N\) from [SameCofactorPhysicalMacroCore](SameCofactorPhysicalMacroCore.md), whose cutoff is near the quarter exponent. In the proof of [SameCofactorFixedPowerRoughness](SameCofactorFixedPowerRoughness.md) use the equal cutoff \(U=x^\theta\) and sieve level \(x^{.10}\) for its preliminary \(R_z\)-transfer. Its hypotheses hold for \(2\theta+.10<1/2\). In its inverse-harmonic proof \(\log\sqrt U=\theta L/2\), so the inverse tail is \(e^{-c\theta/\eta}\) rather than \(e^{-c/\eta}\), with no dependence on \(N\). Thus the new whole \(R_z(m)T(m;U)\) represents \(G_N\) with error
\[
 O_\delta\!\left(M_N\{\eta^{-2}H_0^{-H_0/2}
                   +\eta^{-1}e^{-c\theta/\eta}\}\right)
       +o_{\theta,\rho,\delta}(M_N),\qquad H_0=.10/\eta.               \tag{1}
\]
For fixed \(\theta>0\) this relative error can be made arbitrarily small by \(\rho\downarrow0\), before \(x\to\infty\). No near-quarter occupancy claim is borrowed for this smaller cutoff.

For a fixed \(k\in\{2,3,4,5\}\), let \(\mathcal D_k(N)\) be the part of this actual open coefficient, after grouping by \(m\), where the **full small-prime part** \(v\) consists of \(k\) distinct true primes in \([z,U]\). Thus
\[
 m=vM,\quad v=p_1\cdots p_k,\quad p_i\in[z,U]\ \text{distinct},\quad P^-M>U .
\]
There is no restriction on the number of prime factors of \(M\) and no requirement that it be prime. The core is unique and counted unordered. In fact \(M>1\) for large \(x\); also \(m\) is never a prime power here. The all-powers identity of SameCofactorPhysicalMacroCore gives exactly \(-(\log M)S_U(v)\), even with repeated macro factors. Define the angular core score and integrals
\[
 \begin{split}
 S(y)&=\sum_{I\subseteq\{1,\ldots,k\}}(-1)^{|I|}
                              1_{\sum_{i\in I}y_i\le1},\\
 A_k(\rho,\theta)&=\frac1{k!}\int_{[\rho,1]^k}
          (1-\theta\textstyle\sum_i y_i)S(y)\prod_i\frac{dy_i}{y_i},\\
 B_k(\rho,\theta)&=\frac1{k!}\int_{[\rho,1]^k}
          (1-\theta\textstyle\sum_i y_i)|S(y)|\prod_i\frac{dy_i}{y_i}.
 \end{split}
\]
Then, uniformly at the actual fixed even target,
\[
 \frac{\mathcal D_k(N)}{M_N}
 =-\frac{e^{-\gamma}J_\delta}{\theta}A_k(\rho,\theta)
   +O_\delta\!\left(\frac{H_1^{-H_1/2}}{\theta}B_k(\rho,\theta)\right)
   +o_{\theta,\rho,\delta}(1),\qquad H_1=.40/\theta .                 \tag{2}
\]
The absolute masses \(B_k\) are bounded independently of \(\rho\downarrow0\) for these fixed ranks.

In particular \(\theta\) can be fixed sufficiently small, then \(\rho\) fixed sufficiently small (also meeting any requested tolerance in (1)) so that eventually at **every** even target
\[
      \mathcal D_4(N)<-\frac{.001}{\theta}M_N,\qquad
      \sum_{k=2}^5\mathcal D_k(N)>\frac{.030}{\theta}M_N .              \tag{3}
\]
The first is a whole-core-rank negative sign after pairing the true quotient cohorts. The second exhibits other actual signs that it cannot by itself pay. The ranks outside the displayed union and the other whole-low cells are still unpriced.

## 2. Actual progression and sieve proof

Fix the physical core \(v\), and enforce \(P^-(m/v)>U\) after opening the residue \(v\mid m\). Use the dimension-one fundamental lemma as in SameCofactorFixedPowerRoughness, with sift set \(\{p\le U:p\nmid N\}\) and level \(x^{.40}\). For each sieve label \(e\), the exact condition is
\[
                    su\equiv N\pmod{v e}.
\]
It is the product \(v e\), **not** \(\operatorname{lcm}(v,e)\), even when a prime of \(v\) divides \(e\). This ensures that a core prime really occurs to exponent one. Restrict to \((ve,N)=1\) by the physical unit mask; the source \(su\) has all its prime factors \(>U\), since \(\theta<.10\), hence is automatically coprime to \(ve\). In the pointwise coprime principal the density for \(p\mid e\) is \(1/(p-1)\) if \(p\nmid v\), but **\(1/p\)** if \(p\mid v\), from \(\phi(vp)/\phi(v)\). Both satisfy the same uniform dimension-one upper product condition. Thus the sieve factor is \(V_N(U)\) multiplied by \(1+O_k(x^{-2\eta})\) (or a power-small boundary adjustment at \(p=U\)): at a core prime the factor ratio is \((1-1/p)/(1-1/(p-1))=1+O(p^{-2})\). Taking \(\theta\) sufficiently small gives \(ve\le x^{.40+5\theta}<x^{.49}\). No modulus assumption is made for larger \(v\).

Apply [Polymath, Theorem 2.9, journal p.2079](https://msp.org/ant/2014/8-9/ant-v8-n9-p03-p.pdf), at the full \(su\asymp x\) scale with the genuine short prime \(s\) as SW factor, preserving the actual prime and balanced-semiprime \(u\) components and unit masks. Make the exact \(s\)-relative separation of the moving \(u\) gate and central interval as in SameCofactorPhysicalMacroCore §2; source boundary and log coefficients have arbitrary-log reserve from the stated strip bounds. For \(ve=Q\), the number of possible cores is at most \(\tau(Q)\), and each \(S_U(v)\) has modulus at most \(2^k\). To absorb the weighted modulus multiplicity use Cauchy on the **absolute** progression discrepancies \(E(Q)\): \(\sum_Q \tau(Q)^b E(Q)\le(\sum_Q E(Q))^{1/2}(\sum_Q\tau(Q)^{2b}E(Q))^{1/2}\). Every separated source has at most a bounded multiplicity per integer \(su\), including the frozen gate, so \(E(Q)\ll xL^{O(1)}/\phi(Q)\) by the integer progression upper and the coprime principal. The corresponding harmonic divisor moment costs only log powers. This retains arbitrary-log reserve also with a signed \(v\)-weight.

For the log weight use \(\log(m/v)=L(1-\theta\sum_i y_i)+O(1)\) on the central window, \(y_i=\log p_i/\log U\). The \(O(1)\) error is paid by the same positive sieve upper with \(|C_s|\,|S_U(v)|\), of natural size \(O_{\rho,\theta,\delta}(M_N/L)\) without the \(L\) multiplier. Keep the signed coefficient for the main and bracket only the discrepancy between upper and lower rough sieves using **absolute** weights. By the [fundamental lemma in Koukoulopoulos, Theorem 19.1](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf#page=206), this gap costs relative \(O(H_1^{-H_1/2})\) times the absolute harmonic, i.e. the \(B_k\) term of (2). It is not bought by an unproved signed sieve inequality.

Prime Mertens yields the harmonic \(A_k\) over the actual cores: the factor \(1/k!\) corresponds to distinct unordered factors and each prime harmonic is \(dy/y\); the subset-sum walls have measure zero since \(\rho>0\) is fixed in the target limit. The exact \(\phi(v)\) may replace the product \(p_i\) with relative per-term power-small error. Removing \(p\mid N\) loses only a power-small harmonic because \(p\ge x^\eta\) and \(N\) has \(O_\eta(1)\) such prime factors. Similarly the frozen source mass with the unit condition is \((J_\delta+o(1))x/(2L)\), uniformly, by the genuine quotient PNT in SameCofactorVaughanCenter. Its unsigned counterpart is \(O_\delta(x/L)\), as used in the sieve-gap estimate. Finally
\[
 V_N(U)=(1+o(1))\mathfrak S(N)\frac{e^{-\gamma}}{\theta L}
\]
uniformly, by the odd Goldbach Euler factors and Mertens at \(U\). Combining the genuine source mass, \(\log M\), and these actual coprime local factors gives (2). The proof never replaces \(u\) by a surrogate rough variable or assumes positivity of its weight.

## 3. Integral signs and parameter order

Here the scalar constants are the classical Dickman constants of [Broadhurst](https://arxiv.org/abs/1004.0519), proved by [Soundararajan, Proposition 1 and Theorem 1](https://arxiv.org/pdf/1005.3494). To check the identification, put \(\ell=\log(1/\rho)\). On expanding \(S\), an included set of \(j\) indices contributes the integral
\[
 I_j(1/\rho)
  =\int_{\substack{t_i\ge1\\\sum_{i=1}^j t_i\le 1/\rho}}
                                  \prod_{i=1}^j\frac{dt_i}{t_i}
\]
after rescaling by \(\rho\), with \(I_0=1\). Each excluded index integrates to \(\ell\). Thus exactly
\[
 A_k(\rho,0)=\sum_{j=0}^k\frac{\ell^{k-j}}{(k-j)!}
                                      \frac{(-1)^j I_j(1/\rho)}{j!}.
\]
Soundararajan's Theorem 1 expands the last factor as
\(\sum_{i\le j} C_i(-\ell)^{j-i}/(j-i)!+O_j(\rho(1+\ell)^j)\).
The two log exponentials cancel. Consequently
\[
 \lim_{\rho\downarrow0} A_k(\rho,0)
     =C_k=[z^k]\frac{e^{\gamma z}}{\Gamma(1-z)}
     =[z^k]\exp\left(-\sum_{j\ge2}\frac{\zeta(j)}j z^j\right).
\]
The scalar identity is not claimed as new; its use is in the actual shared-\(s\), moving-target transfer above.

There is a uniform **absolute** bound. Fix the smallest \(t=\min y_i\) and pair subsets differing by its index. The absolute difference is bounded by the sum over other subsets \(I\) of \(1_{1-t<\sum_{i\in I}y_i\le1}\). If \(t<1/2\), a qualifying subset is nonempty with a member at least \(1/(2(k-1))\); opening that member and integrating over an interval of length \(t\) costs \(O_k(t)\) in reciprocal measure. The other variables give at most \((\log(1/t))^{k-2}\), and \(dt/t\) leaves an integrable bound. On \(t\ge1/2\) the measure is bounded. For \(k=4\), after dividing by \(4!\) the first bound is at most \(21\int_0^{1/2}\log^2(1/t)\,dt\le42\), and the second is less than 1. In particular \(B_4(\rho,\theta)<43\) for small \(\theta\), and the \(\theta\)-weight changes the unweighted angular integral by at most \(172\theta\), uniformly in \(\rho\). The same argument gives an absolute bound for each of the other fixed \(k\).

The exact first constants needed here are
\[
 C_2=-\frac{\pi^2}{12},\qquad C_3=-\frac{\zeta(3)}3,\qquad
 C_4=\frac{\zeta(2)^2}{8}-\frac{\zeta(4)}4=\frac{\pi^4}{1440},\qquad
 C_5=\frac{\zeta(2)\zeta(3)}6-\frac{\zeta(5)}5 .
\]
We have \(C_4>.067\) and \(C_2+C_3+C_4+C_5<-1.02\); for the latter, for example use \(\pi^2/12>.82,\ \zeta(3)>1.2,\ C_4<.068,\ \zeta(2)<1.65,\ \zeta(3)<1.21,\ \zeta(5)>1+1/32\). Choose \(\theta\) sufficiently small to make all the bounded-integral weight perturbations small and also the fundamental-lemma errors in (2) below a fixed very small fraction of these strict margins. That is possible uniformly in \(\rho\) by the absolute bound. Then choose \(\rho\) sufficiently small for the gamma limits and (1); finally take \(x\) large with both fixed. For instance one can arrange \(A_4>.064\), \(\sum_{k=2}^5 A_k<-1.01\), and the sum of the sieve errors below \(.001/\theta\) (and the individual rank-four error below \(.0005/\theta\)). Since \(J_\delta\ge J_0>.06282\) and \(e^{-\gamma}>1/2\), these margins yield (3) after the \(o(1)\) errors. They show both useful real signed compensation and an explicit larger opposite debt; nothing is credited twice or transferred to the near-quarter ledger.


## 4. The actual whole mixed mean, and the remaining rank-six-plus sign

There is a simpler way to evaluate the entire mixed side without a many-label tail bound. Let \(\mathcal B_N\) sum the whole mixed score with \(v>U,M>1\), including all fixed or growing numbers of small-core prime factors allowed by \(R_z\). For squarefree \(m\) the exact all-powers identity reduces to
\[
 R_z(m)T(m;U)
   =\Lambda(m)-(\log m)1_{P^-m>U}
                         -R_z(m)(\log M)S_U(v)\,1_{v>U,\,M>1}.
\]
Here the prime term is on the central window, so every prime is \(>U\). The nonzero coefficients on squareful physical rows cost power-small at fixed \(\eta\), by the \(z\)-rough square support and divisor moments; the same holds for proper prime powers in the reflected prime term. Thus the actual prime term cancels on subtracting this identity from (1) and the definition of \(G_N\), leaving
\[
 \mathcal B_N=\sum_{s,u}C_s(u)1_{(su,N)=1}
                      \{(\log m)1_{P^-m>U}-b(su)\}
                           +O_\delta(E_{\theta,\rho}M_N)+o_{\theta,\rho,\delta}(M_N),
\]
where \(E_{\theta,\rho}=\eta^{-2}H_0^{-H_0/2}+\eta^{-1}e^{-c\theta/\eta}\) is precisely the transfer bound in (1). This uses the **whole** signed mixed part, not a new estimate for the complementary pure composites.

The true rough term now needs only a single dimension-one sieve on the source, at level \(x^{.40}\), with no core label. The same full-scale BV at residue \(N\), exact local factor \(V_N(U)\), and unsigned bracket give
\[
 \frac{\mathcal B_N}{M_N}=
 J_\delta\left(\frac{e^{-\gamma}}{\theta}-1\right)
 +O_\delta\!\left(\frac{H_1^{-H_1/2}}{\theta}+E_{\theta,\rho}\right)
 +o_{\theta,\rho,\delta}(1).                                          \tag{4}
\]
In particular the whole mixed term has a large positive main. Its genuinely signed higher-rank remainder is determined by subtracting the real ranks 2 through 5 in (2). There is no rank-one \(v>U\) since every core prime is \(\le U\). Let \(\mathcal B_{N,\ge6}\) denote the mixed term with squarefree \(v\) having at least six prime factors; the omitted nonsquarefree cases are power-small as above. Then
\[
 \frac{\mathcal B_{N,\ge6}}{M_N}
 =\frac{e^{-\gamma}J_\delta}{\theta}
                 \left(1+\sum_{k=2}^{5}A_k(\rho,\theta)\right)-J_\delta
 +O_\delta\!\left(\frac{H_1^{-H_1/2}}{\theta}
                    (1+\sum_{k=2}^5B_k(\rho,\theta))+E_{\theta,\rho}\right)
 +o_{\theta,\rho,\delta}(1).                                          \tag{5}
\]
Choosing the same parameter order with total error \(<.0001/\theta\) (before the tending-to-zero target error), and \(\sum A_k<-1.01\), yields
\(\mathcal B_{N,\ge6}<-.0001\,M_N/\theta\)
for every sufficiently large even target. The negative upper applies to the entire higher-rank mixed complement, not just a density-average or selected positive-sign angles.

There is **no double use** of (3), (4), and (5). Either the entire mixed part is paid with its positive main (4), or its rank-specific components can be kept with their own signs. With the whole mixed main paid, the surviving pure component is exactly the genuine \(\Lambda(m)\) term minus the already modeled \(\log m\,1_{P^-m>U}\) term. Thus (4)–(5) by themselves do not improve the unknown pure-composite cap; they show that the rank-four or rank-six-plus negative pieces cannot be counted as new slack without controlling the rest of the same true ledger.

[check_paired_small_core_signs.py](check_paired_small_core_signs.py) verifies the strict scalar margins with rational arithmetic.
