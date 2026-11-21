# Negative reserve forced into genuine high-rank integer quotients

Use the fixed target, physical central intervals, original reflected coefficient \(C(m)\), weight \(W_s(q)\), and the marked family \(\mathcal F_\eta\) of [ActualNegativeThreeMarkReserve.md](ActualNegativeThreeMarkReserve.md). In particular \(m=N-sq\) and \((sq,N)=1\). In this note \(q\) is an **integer**, unless explicitly required prime, and \(s,p,c,a,b\) are still genuine primes. The labels \(p,c,a,b\) certify \(m=pcab w\) with \(P^-(w)>x^{.004}\). A physical pair \((s,q)\) is counted once. The literal cutoff on \(m\) is unchanged, so the sign result refers to \(C\), not \(C^\dagger\). Set
\[
 D_f(q)=\sum_{d\mid q}\mu(d) f(\log d/L),
 \qquad
 B_f(q)=1_{\mathbb P}(q)-D_f(q).
\]
Here \(f\) is real, fixed, smooth and compactly supported on the line, flat with value \(1\) near zero, and supported for \(t\ge0\) in \(t\le .34\).

**Result.** For each fixed integer \(k\ge1\) there is such an \(f\), a fixed admissible \(\eta>0\), and fixed \(\xi,c_k>0\) such that, uniformly for every sufficiently large even \(N\),
\[
 \sum_{\substack{(s,q)\in\mathcal F_\eta,\ C(m)<0,\ D_f(q)<0\\
                 q\ {\rm squarefree},\,P^-(q)>x^\xi\\
                 \#\{r\mid q:\ r\ {\rm prime},\ r\le x^{.34}\}\ge k+1}}
           W_s(q)\,C(m) B_f(q)\le -c_k M_N .
 \tag{1}
\]
This is a one-sign mass bound on true polynomially rough, composite integer quotients of the exact opened row. It is not an assertion of prime \(q\) on these terms, a bound on the other opened terms, or a proof of Goldbach. It rules out funding the marked reserve entirely by the opposite \(C\)-sign or by bounded active rank in this detector. No uniformity as \(k\to\infty\) is asserted.

## 1. The exact opening and the selected transfer

On the entire original row \(x^{.10}<s<x^{.14}\), for any admissible \(f\) above,
\[
 \sum_{\substack{s\ {\rm prime},\,q\ {\rm integer}\\sq\in(x/2,x],\ (sq,N)=1}}
                  W_s(q)\,C(m)\,D_f(q)=O_{A,f}(xL^{-A}) .
 \tag{2}
\]
For completeness, fix the genuine modulus \(A_0=s e\) after opening the \(e\mid q\) bit of \(D_f\). It is coprime to \(N\) on the physical support and \(A_0\le x^{.48}\). Its outside weight has multiplicity at most \(\tau(A_0)\). Use the exact Vaughan expansion
\[
 C(m)=\Lambda(m)-\!\sum_{\substack{d\mid m\\d\le U}}\mu(d)\log(m/d)
      +\!\sum_{\substack{d\ell\mid m\\d\le U,\,\ell\le V}}\mu(d)\Lambda(\ell)
      -\!\sum_{\substack{d\ell\mid m\\d>U,\ \ell>V,\ d\ell\le Q_0}}\mu(d)\Lambda(\ell).
 \tag{3}
\]
Here \(\Lambda_{\le V}(m)=0\) on the central interval. The ordinary prime BV theorem with maximal prefixes (and the standard divisor-weighted log reserve as in [SwitchedLongFreeReverseColumns.md](SwitchedLongFreeReverseColumns.md)) treats the first term in \(m\equiv N\bmod A_0\). Removing prime powers with base dividing \(N\) costs \(O(L^2)\) per modulus, safely below the target after summing. For each other summand with reflected product \(b=d\) or \(d\ell\), \((b,A_0N)>1\) gives no actual row. Otherwise the exact CRT density with \((m,N)=1\) is \(\phi(N)/(N A_0 b)\), with floor \(O(\tau(N))\). All reflected products are \(\le x^{.5}\), and their log/divisor weights are harmless in the \(x^{.48+.5+o(1)}\) floor total. \(W_s((N-m)/s)\) and \(\log m\) are smooth in the physical interval at fixed \(s\), so use ordinary partial summation.

In the first short-density sum of (3), the finite \(\mu(d)/d\) constant moment is \(O_D(L^{-D})\) and the log-weighted moment \(\sum_{d\le U,(d,N A_0)=1}\mu(d)\log(U/d)/d\) is \(N A_0/\phi(N A_0)+O_D(L^{-D})\); these are the uniform polynomial-mask identities used in [WholePositiveSmallCore.md](WholePositiveSmallCore.md). It matches the \(1/\phi(A_0)\) prime main exactly since \((A_0,N)=1\). For the two other sums fix \(\ell\); they have the same log-small constant moment at \(U\) and, where applicable, \(Q_0/\ell>U\). In the last sum \(\ell\le Q_0/U=H^2\). All these \(d\)-endpoints are polynomial and \(\sum_{\ell\le H^2}\Lambda(\ell)/\ell\) is log-bounded. This proves (2) and makes \(B_f\) an exact opening of the original **whole** \(C\) row to arbitrary log accuracy.

The same null (2) holds with the restriction \(\mathcal F_\eta\), by a different argument: below are the precise modifications to [FullScaleMacroPrimeBalance.md](FullScaleMacroPrimeBalance.md). The small prime labels \(a,b\) are unique; presence of \(c,a,b\) and the rough condition on the rest is a \(G\)-only Boolean predicate when \(m=pG\), since \(p,c>x^{.004}\). Choose the least eligible \(p\) canonically, which amounts to a \(G\)-dependent prefix \(p<\min\{r\mid G:r\text{ in the }p\text{-band, }r\text{ prime}\}\) if the set is nonempty. Take out \(p^2\mid m\) at power saving, and treat other squareful \(m\) in the same way if desired. On the marked support all prime bases in \(m\) exceed \(H^2\) for sufficiently large \(x\). Consequently, on this support,
\[
 C(pG)=\sum_{\substack{d\mid G\\d>U}}\mu(d)\big(\log p+\log(G/d)\big)
       -\sum_{\substack{b\mid G\\p b>U}}\mu(b)\log(G/b).
 \tag{4}
\]
This uses the exact \(p\)-bit split with \(p\nmid G\), even for other repeated prime bases. Freeze only the product comparison \(pb>U\) in relative \(L^{-B}\) boxes of \(p\). Any error implies a true physical divisor in \(U(1+O(L^{-B}))\); summed by divisors this occupies \(O(xL^{-B}+x/U)\) physical \(m\)'s. A box hit by a changing canonical \(p\) endpoint contains, for fixed \(G\), \(O((x/G)L^{-B}+1)\) possible \(p\)'s; summed on the pertinent \(G\) dyads this is log-small with adequate \(B\) and a power-small floor since \(G<x^{.79}\). Moments of divisor powers of the physical \(m,n\) absorb all marks and weights.

Use [Maynard I, Lemma 8.9](https://ora.ox.ac.uk/objects/uuid%3A39a52f47-3770-4ddd-b7a2-b2a4f7300931/files/srj4305733), not the elementary imprimitive estimate at the larger \(p\)-scale of the earlier proof. The two long independent factors here are the true SW prime \(p\asymp x^{.218+O(\eta)}\) and the independently restricted divisor-bounded \(G\asymp x^{.782+O(\eta)}\). Fine Cartesian product boxes, ordinary prime SW with the independent unit masks, and coefficient separation for \(\log p,\log(G/b)\) thus give generalized BV at the literal reduced residue \(N\bmod s e\) and full scale \(x\). The weight \(W_s\) separates on the physical boxes as in the cited balance proof. In the resulting principal, fix \(m,s\) with \((s,Nm)=1\). The remaining sum is
\[
 \sum_{(e,Nm)=1}\mu(e)f(\log e/L)/\phi(se).
\]
Terms with \(s\mid e\) have bound \(O(L^C/[s(s-1)])\). Otherwise factor \(1/(s-1)\) and use the finite \(\mu/\phi\) constant moment, uniform in polynomial masks, by expressing \(f\) as a mixture of cutoffs at positive exponent (its derivative vanishes near zero). This estimate does not use a taper with a nonzero derivative at zero. Arbitrary log reserve follows. Hence on the *actual* family, including the original \(C\) and only one witness per physical row,
\[
 \sum_{\mathcal F_\eta,\ q\ {\rm composite}} W_s(q) C(m)D_f(q)
     =-\sum_{\mathcal F_\eta,\ q\ {\rm prime}} W_s(q) C(m)+O_{A,f,\eta}(xL^{-A})
     \ \gg\ \eta L R_N .
 \tag{5}
\]
Here \(R_N=\mathfrak S(N)x\Sigma(x,N)/L^2\) is the labelled harmonic scale (4) of the three-mark proof. That proof supplies (5) for every sufficiently small *fixed* \(\eta\) with a common positive constant.

## 2. Opened one-/two-neck costs with the correct Fourier scale

In every opening of the previous one- and two-neck estimates we fix \(s,p,c,a,b\) and all but one free \(z\)-rough factor \(y\) of \(w\). The true forms are
\[
 y=y_0+s v,\qquad q=(N-D_0y_0)/s-D_0 v,\qquad y_0\equiv N\overline{D_0}\pmod s ,
\]
with \(m=D_0y\) and \(D_0\) the product of all fixed factors. We also use \(y=y_0+s r v\), \(q/r=(N-D_0y_0)/(s r)-D_0v\) when the prime \(r\) is prescribed to divide \(q\). Empty cases where \(r\mid ND_0\) are removed by the physical unit condition. The second form is still valid if \(r=s\) (it is then a congruence modulo \(s^2\)), although the only tiny \(r\) used below lie below \(s\). For both switches the two affine forms are primitive: the constant of the first is a unit modulo its leading coefficient, and that of the second is a unit modulo \(D_0\). Their determinant is \(N\). All roots at primes dividing \(N\) are removed from both multiplicative functions by the physical unit masks; at primes dividing the leading coefficients there is one nonconstant form with a simple root. All additional exceptional primes are among the fixed markers, the fixed number of factors of rough integers \(D_0/K\), and the one prescribed \(r\). Use [Henriot, Theorem 5 and Corollary 2](https://arxiv.org/pdf/1102.1643) with the [published erratum](https://doi.org/10.1017/S0305004114000280), including leading coefficients in the exceptional set. The additional local costs are bounded: at primes of \(N\) the \(\Delta_*\) multiplier has only the zero valuation, at other exceptional primes it is \(1+O(1/p)\). The common two-root sieving product is \(O(\mathfrak S(N)/L^2)\), after including the one-root exceptions (the factor at \(2\) is absorbed absolutely).

Here the variable \(v\) lies in a comparable central interval of length \(\asymp Y=x/(sD_0)\), with \(Y\gg x^{.038}\) in every unsubdivided neck opening from the preceding proof. One may enlarge to a fixed number of comparable intervals satisfying Henriot's \(\alpha=1/2\). In the \(r\)-prescribed switches below we only use \(D_0=K\), and \(Y=x/(s K r)\gg x^{.38}\) for \(r\le x^{.005}\). The norms of each form are \(O(x)\), so the norm of their product is \(O(x^2)\) and the theorem's height exponent \(\delta_{\mathrm H}=.01\) fits even at \(x^{.038}\). The degree is 2. With growth parameter \(\varepsilon_{\mathrm H}=10^{-5}\), \(\varepsilon_{\mathrm H}<\alpha/[50\cdot2(2+\delta_{\mathrm H}^{-1})]\). All the multiplicative functions used below have strongly multiplicative prime values in \([0,2]\), times unit masks, and satisfy its growth condition uniformly by \(2^{\omega(j)}\ll_{\varepsilon_{\mathrm H}} j^{\varepsilon_{\mathrm H}}\).

Use Fourier inversion
\[
 |D_f(q)|\le\int_{\mathbb R}|\widehat f(t)|\,A_t(q)\,dt,\qquad
 A_t(q)=\prod_{r\mid q,\ r\ {\rm prime}}|1-e(t\log r/L)|.
 \tag{6}
\]
By the positive Euler products in Henriot, in the unsubdivided opening the bound is \(O_\gamma(\mathfrak S(N)Y/L^2)\) times
\[
 E_x(t)=\exp\left(\sum_{r\le 2x,\ r\ {\rm prime}}\frac{|1-e(t\log r/L)|}{r}\right).
 \tag{7}
\]
The rough \(y\)-Euler cost already contributes \(O_\gamma(1)\). The same bound applies if one prime's local value in \(A_t\) is replaced by \(1\), provided that prime is the prescribed \(r\) and treated among the exceptional primes.

For fixed \(t\), the PNT and partial summation give
\[
 \log E_x(t)\ \longrightarrow\
      \int_0^1\frac{|1-e(tv)|}{v}\,dv
     \ \le\ \frac4\pi\log(1+|t|)+O(1).
 \tag{8}
\]
The integral estimate follows since \(|1-e(u)|\) is periodic of mean \(4/\pi\), and its mean-zero part has a bounded primitive; integrate it against \(1/u\) above \(u=1\). The small-\(v\) part in the prime limit is uniformly integrable by \(\sum_{r\le T}\log r/r\ll\log T\). For all \(x,t\) one also has \(E_x(t)\ll(1+|t|)^2\), by splitting at \(\exp(L/(1+|t|))\), using the same Chebyshev bound below it and Mertens above it, with the obvious empty-small-prime interpretation when the split is below 2. Dominated convergence is therefore available for each fixed smooth \(f\), uniformly in the other parameters of all applications, with
\[
 \limsup_{x\to\infty}\int |\widehat f(t)| E_x(t)dt
                      \ll \int |\widehat f(t)|(1+|t|)^{3/2}dt=:\mathcal N(f).
 \tag{9}
\]
This improved exponent strictly below 2 will allow the parameter ordering.

The proofs of the one- and ordered two-neck counts, including \(h=1\), now give the identical bound with the factor \(|D_f(q)|\) inserted: only the innermost two-form bound is changed, from true \(q\)-prime Selberg to (6)–(9). All remaining harmonic restrictions and scales are the same. Off seams the positive part of \(C\) costs \(O(\eta L j)\) or \(O(L j(j-1))\); hence
\[
 \sum_{\mathcal F_\eta} W_s(q) C(m)_+|D_f(q)|
  \ \ll_\gamma\ \mathcal N(f)\eta^2 L R_N + o_{f,\eta}(L R_N).
 \tag{10}
\]
The seam and squareful \(m\) costs are still \(o_{f,\eta}(LR_N)\): the first uses the one-neck estimate with interval width \(O(\log H)\), and the second uses all physical \(q\)'s, divisor weights and the power-small repeated \(m\) base. Upper-bounding by labelled rows is legitimate for positive weights; (5) used the separate unlabelling already proved.

## 3. Flat detector, low-rank leak, and parameter ordering

Choose a fixed smooth probability density \(\psi_0\) supported inside \((.31,.34)\) and define
\[
 f_0(t)=\int\psi_0(u)(1-t/u)_+^{k-1}du\quad (t\ge0)
\]
with the truncated power of degree zero interpreted as the step \(1_{t<u}\). Use the smooth compact extension from its polynomial on a neighborhood on the negative side. For \(1\le j\le k\), \((-1)^j f_0^{(j)}\ge0\) on \(t\ge0\); for \(j=k\) this follows from the positive point-mass derivative before averaging, including \(k=1\). The Möbius sum for any \(q\) is the product of the backwards finite differences \(1-T_{\log r/L}\) over **distinct** prime divisors, evaluated at zero. Primes \(>x^{.34}\) can be omitted completely since every divisor containing one gives zero. For at most \(k\) remaining steps of arbitrary positive sizes the \(f_0\) expression is nonnegative, by integrating the corresponding signed derivative on the rectangular step domain. These identities apply even to squareful \(q\).

For \(0<\varepsilon\ll1\) choose a fixed nonnegative smooth cutoff \(\psi_1\) equal to \(1\) on \([-1,1]\), zero outside \([-2,2]\), and put
\[
    f_\varepsilon(t)= f_0(t)+\psi_1(t/\varepsilon)(1-f_0(t)).
\]
Then it is flat at zero and agrees with \(f_0\) for \(t\ge2\varepsilon\). Its Lipschitz norm is \(O_k(1)\), since \(1-f_0(t)=O_k(|t|)\) near zero. The difference is \(\varepsilon g_\varepsilon(t/\varepsilon)\) with \(g_\varepsilon\) supported in \([-2,2]\) and all smooth seminorms \(O_{k,j}(1)\); thus (9)'s weighted Fourier norm is \(O_k(\varepsilon^{-1/2})\). Indeed Fourier scaling gives a factor \(\varepsilon^2\) and the integral against the \(3/2\) weight costs \(O(\varepsilon^{-5/2})\). The unflattened \(f_0\) cannot replace this function in the selected null (5) for \(k\ge2\), since its nonzero slope at zero generally contributes a real \(1/L\) harmonic term.

If \(D_{f_\varepsilon}(q)<0\) but \(q\) has at most \(k\) active primes, then \(r=P^-(q)\le x^{2\varepsilon}\), and \(\omega(q)\le J=k+3\) because the remaining bases exceed \(x^{.34}\) and \(q\le x\). Pairing the \(r\)-bit and using the Lipschitz bound gives
\[
             |D_{f_\varepsilon}(q)|\ll_k \log r/L .
 \tag{11}
\]
Indeed the \(r\)-free divisor terms have at most \(2^{J}\) summands; repeated \(r\) is irrelevant to the Möbius bit. To count these actual \(q\)'s fix \(s,K,r\) and use the \(q/r,w\) affine pair at \(D_0=K\) in §2. Test \(r\)-roughness of \(q/r\) in the non-strict form \(P^-(q/r)\ge r\) (small prime powers of \(r\) may remain). For \(u_r=(1+\log(L/\log r))^{-1}\), the test \(\omega(q/r)\le J\) is bounded by \(u_r^{-J} u_r^{\omega(q/r)}\). By Mertens the entire extra Euler product for \(u_r^{\omega(\cdot)}1_{P^-(\cdot)\ge r}\) is \(O(1)\) since \(u_r\sum_{r\le p\le 2x}1/p\ll1\). Thus Henriot gives
\[
 \ll_k \frac{\mathfrak S(N)x}{s K r L^2}\big(1+\log(L/\log r)\big)^J
\]
for this count. The original pointwise \(|C(m)|\ll_\gamma L\) on the marked support uses the bounded number of factors including multiplicity. Summing (11), and splitting \(t_r=\log r/L\le2\varepsilon\) into log-exponent dyads with \(\sum_{r\le T}\log r/r\ll\log T\), bounds the low active rank leak by
\[
      O_k\big(\varepsilon(1+|\log\varepsilon|)^J L R_N\big).
 \tag{12}
\]
Prime \(r\) sharing any marked base of \(m\) gives no residue by \((m,N)=1\) and \(r\mid sq\). Nothing in this argument discards a repeated \(r\) prematurely.

Now fix a sufficiently small \(\varepsilon>0\) after \(k\) and the two fixed smooth densities, take \(\eta=\varepsilon^{3/4}\), and take \(x\) large depending on these choices. Decrease \(\varepsilon\) as necessary to have \(\eta\le10^{-4}\), \(2\varepsilon<.005\), and the common occupancy coefficient of (5). Relative to \(\eta L R_N\), the opened opposite-\(C\) leak in (10) is \(O_k(\varepsilon^{1/4})+o(1)\), and (12) is \(O_k(\varepsilon^{1/4}(1+|\log\varepsilon|)^J)\). Hence both are less than a fixed fraction of (5). In (5), positive \(C D_f\) with \(C>0\) is already paid by (10); negative signs can simply be discarded in seeking a lower bound on the remaining positive part. We conclude that
\[
 \sum_{\mathcal F_\eta,\ C(m)<0,\ D_f(q)<0,\ \omega_{\rm active}(q)\ge k+1}
                  W_s(q)\,|C(m)D_f(q)| \gg \eta L R_N .
 \tag{13}
\]
The use of (10) is essential: strict total composite mean does not on its own imply strict mass for these two negative signs.

## 4. Genuine polynomial roughness of the high-rank supply

After \(f=f_\varepsilon\) and \(\eta\) are fixed, choose a new fixed \(\xi>0\) sufficiently small. For \(r\le x^\xi\) dividing \(q\), factor \(|1-e(t\log r/L)|\) out of \(A_t(q)\) in (6) and use the \(q/r,w\) switch again at \(D_0=K\), now with the local value at \(r\) in the remaining \(q/r\) envelope set to \(1\). This is exact even if \(r^2\mid q\). The other Euler factors are bounded by (7), and the factored value is \(\le 2\pi |t|\log r/L\). With fixed \(f\) the \(t\)-integral costs a constant by the crude \((1+|t|)^2\) bound. Summing \(\sum_{r\le x^\xi}\log r/(rL)\ll\xi\) costs \(O_{f,\gamma}(\xi L R_N)\), which is less than half of the surviving fixed lower in (13) for a sufficiently small \(\xi\). This estimate uses a separate roughness threshold, not the scale of the plateau splice. Finally squareful \(q\) with every \(r>x^\xi\) is power-small: sum \(\sum_{r>x^\xi}(x/(s r^2)+1)\) up to \(r\le\sqrt{x/s}\), then over \(s\) in its band. Divisor multiplicities and \(D_f\) are \(x^{o(1)}\), so this is \(o(L R_N)\). The sign and mass surviving (13) hold on the exact support of (1). On it \(q\) is composite and \(B_f=-D_f\), giving the required negative signed contribution since \(L R_N=2\Sigma(x,N)M_N\) and \(\Sigma\gg\eta^2\).

Thus the actual negative reserve cannot be accounted for solely by low-rank integer quotients in this legitimate opened row. This does not sign the other \(C,D_f\) chambers or create a genuine prime pair.

## Comparison (through November 21, 2026)

The [marked original negative reserve](ActualNegativeThreeMarkReserve.md)
and [full-scale cofactor balance](FullScaleMacroPrimeBalance.md) distinguish
literal prime-quotient signs from a compensated opened row. Here the addition
is the strict mass at arbitrarily prescribed **fixed** active ranks after
actually opening the same row, with a separately paid (C>0) term.
[Arneth's September 2026 five-factor work](https://zenodo.org/records/23016346)
gives finite compensation tests, and the [October cubic minorant](https://zenodo.org/records/23477014)
and [Bonferroni–Liouville transfer](https://zenodo.org/records/23560521)
address other detecting weights. See also [Pham October 2026 v1](https://www.preprints.org/manuscript/202610.3061)
and [Bahbouhi November 2026 v1](https://www.preprints.org/manuscript/202611.0975)
for distinct reflected or rough-complement decompositions. No published
result on cancellation of the overall signed complement is assumed.
