# Whole reverse-Vaughan modulus columns, including an actual 0.510 profile

Use the double Vaughan III remainder on the actual semiprime cell of [ReverseVaughanDoubleResidual.md](ReverseVaughanDoubleResidual.md). Write \(N=2x,\ I=(x/2,x],\ L=\log x,\ S=x^\alpha\), \(.10\le\alpha\le.14\), \(S<s\le2S\) with \(s\) prime. Denote \(\kappa_s,W_s\) the original label weights and tests (including the exact \(K_{P_3}\)). Put
\[
 C_m^{\rm hi}(m)=\sum_{\substack{d\ell h=m\\d>U,\ \ell>V,\ d\ell>Q}}
                       \mu(d)\Lambda(\ell),
 \quad U=x^{.454},\quad V=x^{.004},\quad Q=x^{.466}.
\tag{1}
\]
These cutoffs obey the forward [dual Weil cap](UnmarkedSemiprimeDualWeilTypeII.md) with e.g. \(\Delta=.002\) across the whole \(s\)-band. On the reverse side one may use a **uniform** \(E=x^{.080}\) instead of \(E_D\) from the reverse note (because \(.495\cdot.454-.14>.080\)), with \(U_q=x^{.070},\ V_q=x^{.010}\). The full conventional quotient-prime normalization \(1/\log q\) is retained.

Our column assertion is: the actual signed sum
\[
 \sum_{\substack{m+s r k j=N,\ s\sim S\ {\rm prime}\\
                     m\in N-I,\ (m,N)=1\\
                     r>U_q,\ k>V_q,\ e=rk>E\\
                     (s,r,k)\ {\rm in\ selected\ columns}}}
  C_m^{\rm hi}(m)\,\kappa_s\mu(r)\Lambda(k)
                  \frac{W_s(r k j)}{\log(r k j)}
       \ll_B xL^{-B}
\tag{2}
\]
for every fixed \(B>0\), uniformly at each target \(N\), for either of these selections:

* **All low columns:** \(A=s r k\le x^{.5-\delta}\) for any fixed \(\delta>0\).
* **A genuinely above-half family, for every \(s\)-dyad:** put
\[
 r_0=.316-1.22\alpha,\qquad k_0=.194+.22\alpha,\qquad w=10^{-5}.
\tag{3}
\]
Take all genuine quotient factors in
\(|\log_x r-r_0|\le w,\ |\log_x k-k_0|\le w\).
Here \(A=x^{.510+O(3w)}\), with \(e>E\) automatic. No additional assumption of smoothness, squarefreeness of \(A\), or of adaptive factorization of the modulus coefficients is imposed. The condition \(\Lambda(k)\ne0\) already restricts \(k\) to the true prime powers of the original Vaughan expansion.

The entire reflected factor range \(d\ell>Q\) is included, even when \(d\ell\) is close to \(x\); (2) is not a result confined to the near-hyperbola strip of [DoubleVaughanReciprocalSeam.md](DoubleVaughanReciprocalSeam.md). It does not estimate all columns just above \(1/2\), or any whole prime-pair count.

## 1. Reassemble before applying any product split

The left side of (2) is the **unsplit** reflected high branch. Use the exact identity on its full central support
\[
 C_m^{\rm hi}(m)
    =\Lambda(m)-(\mu_{\le U}*\log)(m)
       +(\mu_{\le U}*\Lambda_{\le V}*1)(m)
       -\!\!\sum_{\substack{d\ell h=m\\d>U,\ \ell>V,\ d\ell\le Q}}
                      \mu(d)\Lambda(\ell).
\tag{4}
\]
Do not add a condition \(d\ell A>x^{1-\epsilon}\) before (4). For the low columns retain the uniform \(E\) from above so there is no hidden \(d\)-dyad cutoff; for the above-half columns \(e>E_D\) for every \(d\)-dyad of the reverse note anyway, since \(A>x^{.5099}\) while \(2S E_D\le D^{.495}\ll x^{.495}\). After removing complete columns using (2), one may intersect the prior under-hyperbola and seam estimates with the complementary column choices. There is no prime-mask replacement on an individual previously cut residual.

For fixed \(s,r,k\), \(A=s r k\), \(j>0\) and \(q=r k j=(N-m)/s\). The progressions in \(m\) are exactly \(m\equiv N\bmod A\) with \(m\in N-I\), \((m,N)=1\); thus \((A,N)=1\) is forced. The test \(G_s(m)=W_s((N-m)/s)/\log((N-m)/s)\) is smooth on the central interval. For the above-half proof it is convenient to separate the \(s\) variable at arbitrary log precision:
\[
 \frac1{\log((N-m)/s)}
  =\frac1{\log(x/s)+\log((N-m)/x)}
\]
has a rapidly convergent finite log expansion, as in the seam note. Together with the exact finite separation of \(W_s\), this leaves a bounded product test \(G(m/x)\) and an \(s\)-only coefficient. Error in (2) is \(O_B(xL^{-B})\) by the physical majorant \(L^C\tau_2(m)\tau_2(N-m)\), since the \(s\)-label has only \(O(1)\) possible values at each \(N-m\). For low columns ordinary BV can also be applied directly with the \(s\)-dependent uniformly log-power variation test. In either case the sharp central endpoints are kept.

### Short-divisor pieces in (4) are exactly centered

All three right-side divisor expansions other than \(\Lambda(m)\) have divisor \(a\le Q\) (for the first \(a=d\); otherwise \(a=d\ell\)). For both selected families \(aA\le x^{.9761}\) for sufficiently large \(x\). If \((a,A N)>1\) the physical intersection is empty. Otherwise CRT, expanding \((m,N)=1\) by \(f\mid (m,N)\), gives
\[
 \sum_{\substack{m\in N-I\\m\equiv N\bmod A\\a\mid m,\ (m,N)=1}}G_s(m)
  =\frac{\phi(N)}{N a A}\int_{N-I} G_s(y)\,dy
      +O(L^C\tau_2(N)).
\tag{5}
\]
Indeed \((aA,N)=1\), so each \(f\mid N\) specifies a single class modulo \(faA\); the integral follows by summation in the progression and total variation. For the \(\log(m/d)\) test in the first piece the same formula uses that factor inside the integral and in the bounded log-power error. After summing all \(a,A\) selected, the error is \(O(x^{.9761+o(1)})\): each pair allows only the indicated divisor-power factorization counts (all weights at most \(x^{o(1)}\)), and the product is within the displayed bound.

For fixed \(A\), put \(F=A N\). Uniform coprime Mertens and partial summation give, for any polynomially long \(Y\) and any fixed \(B\),
\[
 \sum_{\substack{d\le Y\\(d,F)=1}}\frac{\mu(d)}d=O_B(L^{-B}),
 \qquad
 -\sum_{\substack{d\le Y\\(d,F)=1}}\frac{\mu(d)\log d}d
                =\frac F{\phi(F)}+O_B(L^{-B}).
\tag{6}
\]
The Euler series is \(\zeta(1+z)^{-1}\prod_{p\mid F}(1-p^{-1-z})^{-1}\) and the reciprocal zeta has a simple zero of derivative 1 at \(z=0\); the convergence and uniform tails use exactly the coprime maximal bound (8) of the whole Type I note. Inserting (6) into the first piece of (5) gives **exactly** \(1/\phi(A)\) times the test integral, up to arbitrary log savings after harmonic summation in \(A\). Here the \(\phi(N)/N\) factor in (5) is essential and \((A,N)=1\).

In each other piece fix \(\ell\) and sum \(\mu(d)/d\) over the exact reduced mask in \(d\). For the second term this is the prefix \(d\le U\) (or the empty class if \((\ell,F)>1\)); for the last it is the interval \(U<d\le Q/\ell\). All nonempty upper endpoints are polynomially long, so the first estimate in (6) and \(\sum_\ell\Lambda(\ell)/\ell\ll L\) dispose of these two means. Thus (2) is reduced to the **centered prime progression** at the true residue \(N\), with exactly the original reverse coefficients on \(s,r,k\).

All \(m\asymp x\) with \(\Lambda(m)\ne0\) and \((m,N)>1\) are powers of primes dividing \(N\); removing this mask in the \(\Lambda\) term costs \(x^{1/2+o(1)}\) at most after summing columns, since each \(A\mid N-m\) at a positive \(N-m\in I\) and the factorization multiplicity is divisor-bounded. The same bound removes all proper prime powers at any subsequent stage when needed. In the unrestricted reference at a fixed \(A\) the principal \(1/\phi(A)\) factor pays the analogous error harmonically. Ordinary maximal BV therefore proves the low-column claim, even with sharp endpoints: each modulus has at most divisor-power times log-power weight. The standard weighted reserve follows by Cauchy from unweighted BV and the crude \(O(xL^C/A)\) per modulus bound, summing divisor harmonic moments. This does not use Möbius BV as a substitute for prime BV. Equivalently, if one sums the prime main separately over the true \(r>U_q\), its \(1/\phi(s k r)\) can be split after fixing \(s,k\) by the at most two underlying primes dividing \(s k\) and used with (11) of the whole Type I note; the per-column centering above avoids that additional step.

## 2. Actual large-residue prime distribution in the profile (3)

We verify a weighted \(\Lambda\) progression discrepancy for the chosen **actual** modulus factors. Each \(s,r,k\) slot is independent, with its original weights \(\kappa_s,\mu(r),\Lambda(k)\) and the original \(N\)-unit restrictions. The \(e>E\) constraint in this profile is automatic. Dyadize the \(r,k\) ranges independently and allow truncated dyadic boxes. A merged slot \(s r\) has log-bounded coefficients, since each integer of polynomial size has only \(O(1)\) possible \(s\)-prime divisors in the macro band. The same log bounds apply to the single slots. All numerical exponents below account for the \(\pm w\) widths; for the \(s\)-dyad \(\log_x s=\alpha+O(1/L)\), inside \(\pm w\) eventually.

### 2.1 Source inputs and grouping for the true prime argument

Use [Lichtman, arXiv:2309.08522v1, Proposition 5.2](https://arxiv.org/html/2309.08522v1#S5): for a convolution of a rough \(z_0=x^{1/(\log\log x)^3}\)-rough Siegel–Walfisz short coefficient at length \(X^\beta\) (here \(X=x\)) and an arbitrary long coefficient, it estimates the weighted progression discrepancy for **three independent dyadic modulus slots**. If the slots have exponents \(v_1,v_2,v_3\), then for residue \(N=2x\) and \(\theta=7/32\) its four exponent conditions are, with a small fixed reserve \(\varepsilon>0\),
\[
\begin{split}
 v_1-\beta&<-\varepsilon,\quad
 2\beta+v_2+2v_3<1-8\varepsilon,\\
 \theta+\beta+v_1+5v_2+2v_3&<2-15\varepsilon-o(1),\\
 (1+2\theta)\beta+v_1+(5-2\theta)v_2+(2+2\theta)v_3&<2-15\varepsilon.
\end{split}
\tag{7}
\]
The \(o(1)\) in the third inequality pays the factor \(2^\theta\). In the first line the source uses the usual uniform full residue range \(|a|<x^{1+\varepsilon}\), and its \(a\ne0\) is our actual \(N\). One may take the third slot to be the singleton \(1\). No invocation of its triply well-factorable version is needed.

Apply the source's Heath–Brown identity (Lemma 3.3) at fixed order \(10\). In the \(\Lambda\) term, requiring \(P^-(m)\ge z_0\) removes only proper prime powers in the central interval, at negligible cost as above; then each factor in each Heath–Brown term is individually \(z_0\)-rough. Individual factor weights are \(1\) and \(\mu\), with a log on one of the free factors. The short signed factors have size \(\ll x^{.10}\). Dyadize all factors. There are three possible ways to estimate each resulting box.

1. If some free factor has scale at least \(x^{.512}\), use Lichtman's Lemma 3.4 (fundamental lemma for the free rough variable) at modulus \(A\le x^{.5101}\), on each reduced class. This yields its full centered discrepancy \(O_B(xL^{-B})\) after summing divisor weights. Ordinary partial summation handles its log.
2. If two free factors have product scale at least \(x^{.78}\), use Lichtman's Proposition 3.2. Only needed if no factor is in the first case, so each free factor in the pair has an exponent bounded below. The required \(A\le(x/M)^{2/3-3\epsilon'}\) holds with slack since the two free exponents sum to at least .78, and the remaining product scale is \(M\).
3. Otherwise one can group a subset of all factors to a length of exponent \(\beta\in[.145,.335]\). If a single factor already fits the interval this is immediate. Otherwise there are at most two factors of exponent \(>.335\), all free, and all other factors have exponent \(<.145\). With no more than one large factor their small complement has exponent at least \(1-.512-o(1)>.145\); with two large factors, unless the small complement has enough mass to pass .145, the large pair has exponent \(>1-.145-o(1)>.78\). In any qualifying small complement choose factors greedily until their sum is at least .145, and its first crossing is below .290. Constants and asymptotic dyadic factors leave fixed slack at the comparison boundaries. Use Proposition 5.2 for the grouped subset, with the moduli assignments below.

The comparison is for central prefixes and then the original test. To impose a sharp product bound \(m\in[x,t]\), one can use the separation of variable inequalities in Lichtman Lemma 4.2, or partition each Heath–Brown dyad into boxes of relative widths \(L^{-C_1}\), retain whole allowed boxes, and bound the \(O(xL^{-C_1})\) product edges by his Lemma 4.1 with arbitrary divisor powers. That estimate applies at \(A\le x^{.5101}\), with a fixed power margin between \(xL^{-C_1}\) and \(A\). Its \(\tau_2(A)^{O(1)}\) factor sums with harmonic log reserves in \(A\). The principal/reference edges are easier. There are only a fixed log-power number of such boxes. Times any smooth product test, use its log-power variation, or the same mesh approximation with fixed additional reserve. Therefore sharp prefix endpoints do not impose hidden Mellin oscillations on the short Siegel–Walfisz weight.

### 2.2 Exact allocation across the whole exponent continuum

Let \(\xi=.0005\). For the grouped exponent \(\beta\) in case 3, use the following actual modulus slots in order:
\[
\begin{array}{c|c}
\text{interval of }\beta & (q_1,q_2,q_3)\\ \hline
[.145,\,r_0+\xi] &(s,k,r)\\
[r_0+\xi,\,k_0+\xi] &(r,k,s)\\
[k_0+\xi,\,\alpha+r_0+\xi] &(k,r,s)\\
[\alpha+r_0+\xi,\,.335] &(s r,k,1).
\end{array}
\tag{8}
\]
All stops are in this order throughout \(\alpha\in[.10,.14]\). Each slot keeps its genuine coefficient, so the exact modulus product and signs are unchanged even when several prime labels can represent a merged slot. The following are upper bounds for the four left sides in (7), before the harmless \(o(1)\), incorporating \(w\) once per factor assigned to a slot:
\[
\begin{array}{c|rrrr}
1&-.00499&.99303&1.98133&1.83804875\\
2&-.00049&.95543&1.99333&1.83604875\\
3&-.00049&.99663&1.89933&1.76829875\\
4&-.00048&.89481&1.96302&1.792478125
\end{array}
\tag{9}
\]
For the first column use the lower \(\beta\) endpoint of (8), and for all others its upper endpoint; the resulting expressions are affine in \(\alpha\), so the maxima are computed at \(.10,.14\). The modulus-length factors \(O(1)\) from dyadization only give \(o(1)\). Thus e.g. \(\varepsilon=.00005\) fits with positive fixed margins. This realizes every needed grouped exponent, not a single favorable choice along the prime decomposition.

### 2.3 Siegel–Walfisz and the true bounded-coefficient reduction

The grouped short coefficient in case 3 is a convolution of a fixed number (at most 20) of interval-restricted \(z_0\)-rough \(1\) or \(\mu\) factors, one possibly carrying a log. Since the selected product scale is at least \(x^{.145}\), a selected factor has polynomially large scale. Fix all other selected factors, use this factor to estimate the **true** Siegel–Walfisz discrepancy with the extra coprimality condition of Lichtman's (2.2), and sum the fixed products harmonically or by their box cardinalities. More explicitly, for a grouped variable \(n=a b\) with \(a\) fixed, a reduced class \(n\equiv c\bmod q\) requires \((a,q)=1\). If \((a,d_0)>1\) for the auxiliary unit mask, both main and AP contributions are zero. Otherwise it is the reduced class \(b\equiv c\bar a\bmod q\), \((b,d_0)=1\), with ordinary interval cuts in \(b\) (including the group scale). Log-power errors at the single factor's length sum to the required \(O_B(N_{\rm group}\tau_2(d_0)^C(\log N_{\rm group})^{-B})\).

For clarity, both kinds of single long coefficients have this property on arbitrary prefixes; no prime estimate at factor length under a polynomial modulus is needed here. For \(q\) larger than a sufficiently high log power, a progression count and Cauchy with an ordinary divisor moment give the required bound for the whole grouped coefficient, also including its principal \(1/\phi(q)\) term. For \(q\) at most that log power, handle a long factor of scale \(Y\ge x^c\) as follows:
* For \(1_{P^-(b)\ge z_0}\), expand the coprimality \((b,d_0)=1\) by divisors, at cost \(\tau_2(d_0)\). Terms with such a divisor \(f>Y^{1/4}\) cost \(O(\tau_2(d_0)(Y^{3/4}+1))\). For short \(f\) which are units at \(q\) and already rough, the remaining variable is just rough in a reduced class modulo \(q\), so ordinary fundamental lemma, or bounded-order Bonferroni through \(J\asymp C\log L\) at \(z_0\), gives arbitrary log saving after subtracting its reduced-class average. Nonunit \(f\) or nonrough \(f\) give exact zero.
* For \(\mu(b)1_{P^-(b)\ge z_0}\), expand the \(d_0\)-mask first, into its \(\le\tau_2(d_0)\) squarefree divisors \(f\). Nonrough \(f\) gives zero in the actual rough sum; \(f>Y^{1/4}\) is discarded **before** approximating roughness at the same divisor-by-divisor bound as above. Write \(b=f v\) for the remaining \(f\)'s and use \(\mu(fv)=\mu(f)\mu(v)1_{(f,v)=1}\). Truncate the rough mask on \(v\) through the same order \(J\): for a signed coefficient bound the absolute indicator error by the next elementary symmetric sum of divisibility events. Its total error in a reduced class is arbitrarily log small relative to \(Y/f\) by \((\sum_{p\le z_0}1/p)^{J+1}/(J+1)!\) and a CRT floor at \(z_0^{J+1}=x^{o(1)}\); the extra coprimality may be dropped for this error. Each retained rough-removal divisor \(g\) is coprime to the rough \(f\), and with \(b=fg w'\) the exact coefficient is \(\mu(fg)\mu(w')1_{(w',fg)=1}\). The remaining variable is at scale \(Y/(g f)\ge Y^{.7}\) with fixed unit mask to \(fg\) and a log-small modulus. Uniform masked Möbius Siegel–Walfisz follows from ordinary \(\mu\chi\) Siegel–Walfisz by convolution with the coprimality-mask smooth-divisor indicator, exactly as in the proof of (4) of the reverse note (now only characters with conductor of log size are used). The summed \(g\)-cost is harmonic and polylogarithmic, \(\sum_{g\mid \prod_{p<z_0}p}1/g\ll L^C\). Use one consistent convention at the \(z_0\)-endpoint. A log factor is allowed by partial summation.

The complete grouped coefficients may a priori be divisor-bounded rather than log-bounded. Use the exact reduction in Lichtman's proof of Proposition 3.1: clip each grouped variable to \(\tau_2\le L^J\) with \(J\) sufficiently large after the requested precision. Lemma 4.1 at the true residue \(N\) bounds the removed part by \(O_B(xL^{-B})\) after summing the literal modulus multiplicities: large divisor count in either factor implies large divisor count in its product, and one can spend arbitrarily high fixed divisor moments. Its reduced mean is bounded by the same elementary moments and harmonic modulus weights. Lemma 4.3 gives the required Siegel–Walfisz condition for the clipped rough short coefficient; equivalently the lost whole \(N_{\rm group}\)-scale divisor mass has arbitrary log saving independently of the residue. Now divide both grouped coefficients and the three modulus slots by fixed log powers to make each literally 1-bounded as Proposition 5.2 states. Its arbitrary logarithmic precision absorbs these divisions and the fixed log-power number of boxes. We have not normalized an uncontrolled \(x^{o(1)}\) maximum.

These applications prove an arbitrary-log centered \(\Lambda(m)\) discrepancy over the true \(A=s r k\) profile. At this point replace the principal term \(\phi(A)^{-1}\sum_{(m,A)=1}\Lambda(m)G_s(m)\) by \(\phi(A)^{-1}\int G_s\) using ordinary PNT, harmonic weights in \(A\), and the negligible proper prime powers; since \(m\asymp x>A\), a nonunit ordinary prime cannot occur in this reference. This is exactly the preceding short-divisor center, and proves the second selection in (2).

## 3. Source comparison and scope

The algebraic reassembly in (4) and separation of true progression centers follow the same strategy as the prior [Pan polynomially rough column work](https://github.com/mxym/math/blob/680657f657d6a77117cf144f06f5080afb02f893/research/theory-2026-11-20/strong-goldbach/PanPolynomiallyRoughSurvivors.md), but with the actual three independent reverse-Vaughan modulus factors and the original semiprime test. The .510 profile follows from the published Lichtman **Proposition 5.2** with an explicit allocation at every relevant Heath–Brown grouping, not from assuming a triply well-factorable quotient coefficient. Indeed it would generally be impossible to appeal directly to triple well-factorability at this level: if the actual prime \(k\) is the largest factor then \(k^3\) alone exceeds even \(x^{153/256}\) in this profile. The analogous support criterion is Pham's [*Restricted Chen Sieve*, v1, Theorem D and Proposition 7.8](https://www.preprints.org/manuscript/202611.0694). Moreno Borrallo's May 2026 [*A Parity-Sensitive Liouville Decomposition*, Proposition 15.5](https://www.researchgate.net/publication/403749879_An_Exact_Spectral_Dispersion_Framework_Beyond_the_Classical_Parity_Barrier_in_Sieve_Theory_Exact_Spectral_Dispersion_and_Applications_to_Goldbach_and_Polignac_Conjectures) instead groups an already triprime **input** against modified linear-sieve modulus weights. That is not our true-prime input and reverse-Vaughan modulus profile; none of its claimed full binary conclusions is an input here.

[Arneth's October 2026 HB6 candidate](https://zenodo.org/records/23215269) uses a Heath–Brown expansion on a prime-complement factor but retains a different long-divisor coefficient selected by a prime-versus-central-three-prime identity. Its [later summary](https://zenodo.org/records/23393218) records its own signed-reassembly and dispersion interfaces. The calculation here concerns only (1)–(3), with no reliance on those candidate closures or claim of priority for the method.

Other columns outside the two exact selections, together with any noncovered portions of the original low residual, remain. In particular this is not a contiguous unconditional prime level for unrestricted \(A\), and it does not supply the strict upper against the original semiprime mask or prove binary Goldbach.
