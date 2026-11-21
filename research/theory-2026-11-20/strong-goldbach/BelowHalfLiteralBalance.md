# A first-order literal below-half balance mask, with a second-order overlap debit

This complements [BalancedLargeTagTaper](BalancedLargeTagTaper.md). Here both prime tags lie **below** the square root of their own actual integer, so multiplicity is possible. A flat kernel kills the repeated-mark contribution on the \(q\) leg exactly. On the \(m\) leg the correct affine normalization does not kill it: it leaves the genuine \(\Lambda\) of the small cofactor. We bound that overlap at the fixed-target \(M_N\) scale using the same prime-source phase injection and a new small-prefix sieve upper. This is an estimate for one literal factor mask, not for its full complement.

## 1. The claimed estimate and literal signs

Keep the physical convention and \(E_N\) of the balanced large-tag note. Fix real \(C_c^\infty\) kernels \(h,f\), supported in \([-.002,.002]\), with \(h=1\) and \(f(t)=1-t\) on \([-.001,.001]\). These choices have the **same original** centered ledger \(\sum_{s,q\ {\rm composite},\,m\ {\rm composite}} X_h(s,q)\), where
\[
 X_h(s,q)=W_s(q)(\log m)H_h(q)H_f(m);
\]
the support-reduction proof there applies without change, with the same affine calibration. No previous wide-kernel reserve is used. Keep the order of parameters: fix \(h,f\) first, then fix positive widths \(0<a,b\le.0001\).

For the true \(s\)-dyad \(S<s\le2S\) use actual prime tags
\[
 A_S=\left(x^{-a}\sqrt{x/S},\, .4\,\sqrt{x/S}\right),\qquad
 B=\left(x^{.5-b},\,\sqrt x\right).
\]
Let \(K=\omega_{A_S}(q)\), \(J=\omega_B(m)\), counting *distinct* prime factors. Then, uniformly in the even target,
\[
 \left|\sum_{s,q} X_h(s,q)1_{\{K\ge1,\ J\ge1\}}\right|
 \ \le\ C_h\,a b^2 M_N+o_{h,f,a,b}(M_N),                                 \tag{1}
\]
where the constant multiplying \(a b^2\) is independent of the widths. The signed sum with multiplicities \(KJ\) is \(O_A(xL^{-A})\), by the proof of the large-tag theorem. Indeed the tags are fixed intervals per \(S\)-block, their upper exponents satisfy \(\alpha\le(1-\sigma)/2+o(1)\), \(\beta\le .500+o(1)\), and the two divisor exponents are at most \(.002+o(1)\). The resulting off-diagonal bound is \(.9852+o(1)\), with the same units and zero-mode flatness as in that proof.

Both tags are strictly below half: \(p<.4\sqrt{x/S}<\sqrt q\) for \(q\ge x/(4S)\), and \(r<\sqrt x\le\sqrt m\). Both are proper factors; the mask forces actual composite \(q,m\). There are at most two tags per leg for large \(x\). If \(K=2\), write \(q=p_1p_2u\). Then \(1<u<x^{2a}\) (the strict lower assertion uses \(p_i<\sqrt q\)) and \(\log u/\log q<.001\). All active divisor arguments lie in \(u\), where \(h\) is flat. Thus \(H_h(q)=\sum_{d\mid u}\mu(d)=0\), also if \(u\) is not squarefree. If \(J=2\), write \(m=r_1r_2v\); here \(1<v\le 1.5 x^{2b}\) and \(\log v/\log m<.001\). The exact affine identity instead gives
\[
 \log m\,H_f(m)=\Lambda(v).
\]
These identities do not assume that an unlabelled cofactor is prime. It follows that the difference between the literal mask and \(KJ\) is precisely the subtraction of \(\sum X_h 1_{\{K=1,J=2\}}\). We bound its absolute value by opening one true \(p\mid q\) in \(A_S\), one true \(r\in B\) and the genuine prime power \(v\le 1.5x^{2b}\) with weight \(\Lambda(v)\), and retaining that \(r_2=m/(rv)\) is prime. Replacing its \(B\) band by the full physical range only gives a nonnegative upper. On this enlarged range \(r_2>x^{.49}\) for large \(x\).

## 2. Available small-divisor counts on the actual overlap source

For this upper, consider the actual \(q\)-rows with \(p\mid q\), \(rv\mid m\), and fixed unit conditions. The additional congruences used below are \(d\mid q, e'\mid r_2\), with \(d\le x^{.00402}\) and \(e'\le x^{.002}\); incompatible overlaps are omitted. The geometric principal is the physical \(q\)-interval length times
\[
 \frac{\phi(N)}{N p\, r v\,d\,e'}.                                      \tag{2}
\]
The summed error stays power-small when each \(d\) or \(e=v e'\) has divisor-bounded multiplicity and each coefficient has size \(x^{o(1)}\), with arbitrary dependence on the **fixed outer** \(d,e,r\) and independent of the varying \(s,p\) in their blocks. To see this, repeat the large-tag proof with \(P=r v e'\). Unit removal uses \(g\mid N\) exactly as there. Since \(p,r,s\) are macroscopic distinct primes (the \(p\) and \(r\) bands are disjoint) and \(v,e',d\) are short, the only new mask is \((d,ve')=1\), forced on every actual row with \((n,N)=1\). Also \(v,e'\) are units at \(N\). Before dropping the \(r_2\)-prime condition via an upper sieve, \(r_2\) is just an integer in this geometric count. The nonzero phase is exactly \(kN\overline{s p d g}\bmod P\). Distinct \((s,k)\) are still separated **modulo \(r\)** by \(T<\min s\) and \(ST<r\). Unlike the previous theorem there is no need that \(ve'\) be squarefree: by CRT use Weil at \(r\), the trivial bound at \(ve'\), and get \(\sqrt r\,ve'\) for completed Kloosterman sums (since \(r\nmid ve'\)). Complete inverse periods cost at most \((A_{\rm dyad}/P+1)ve'\) by the Ramanujan bound; here \(A_{\rm dyad}<r\).

The exponent of the complete nonzero range after all labels is at most
\[
 .355+\tfrac54(.500)+.00402+\tfrac32(.00221)+.0002<.988 ,
\]
using \(\alpha/2+\sigma\le.355+o(1)\) and \(\log_x(ve')\le.00221\) eventually; the diagonal stays below .979. The \(g\)-tail is as before. Both sharp endpoints can be smoothed before this upper, using the same divisor-moment bound. Use a nonnegative smooth majorant of the entire physical interval supported in a fixed slightly enlarged central interval, with bounded derivatives; no need here to approximate its endpoints finely. Its principal length is \(O(x/s)\), and its nonnegative main and signs are not altered by using this upper. The sieve coefficients below depend on fixed \(N,v,d_0\) and a threshold attached to \(d_0\) only. The prime labels \(s,p,r\), all much larger than the sieve prime cutoff, introduce no such dependence. Thus the stated errors apply rather than assuming pointwise distribution on any single tiny progression.

## 3. An absolute signed-score upper through a short distinct-prime prefix

We prove the estimate for \(|H_h(q)|\) in the previous nonnegative problem. Fourier inversion, with \(\log q\ge L/2\), gives the pointwise upper
\[
 |H_h(q)|\le \frac{1}{2\pi}\int_{\mathbb R}|\widehat h(\xi)|\,A_\xi(q)\,d\xi,\qquad
 A_\xi(q)=\prod_{\ell\mid q}\min(2,2|\xi|\log\ell/L).
\]
Write \(A_\xi(\ell)\) for the individual factor. These are distinct primes regardless of valuation. They are nonnegative and at most 2, uniformly in the spectral variable. This is the same finite-divisor expansion as in the bilateral rough proof, but we need an averaged bound over the present short-divisor **distribution**, not Henriot on each individual progression.

Let \(D_0=x^{.002}\), \(R=x^{.001}\) and \(z=x^\zeta\) with fixed \(0<\zeta\le .00001\) sufficiently small for the elementary Selberg step below. Order the distinct primes \(\ell\le z\) dividing \(q\). If their full product \(d_0\le D_0\), the actual remaining primes are \(>z\), so
\[
 A_\xi(q)\le 2^{L/\log z} A_\xi(d_0).
\]
In the other case let \(d_0=d_1\ell\) be the *first prefix crossing* \(D_0\), with \(\ell=P^+(d_0)\le z\), \(d_1\le D_0<d_1\ell\). Then the actual remaining primes are \(>\ell\), so
\[
 A_\xi(q)\le 2^{L/\log\ell}A_\xi(d_1)A_\xi(\ell).
\]
These are bounds on each physical row. In both cases we can sum over **all** such prefix candidates \(d_0\), and upper-bound the requirement of no extra primes up to threshold \(w=z\) or \(w=\ell\), respectively, by a Selberg square. This upper only relaxes extraction conditions; the selected divisibility \(d_0\mid q\) is retained. A crossing requires \(\ell\gg L\) since \(\sum_{p\le\ell}\log p\ll\ell\). In particular the factor \(2^{L/\log\ell}=x^{o(1)}\) is uniformly admissible in the summed distribution errors from §2, even before the Rankin estimate below.

For fixed \(v,d_0\) and cutoff \(w\le z\), impose the **joint** upper sieve excluding extraneous primes \(\le w\) from \(q\) and primes \(\le z\) from \(r_2\), leaving out primes dividing \(Nv d_0\) from the tests. Leaving these primes out only increases the upper: outside \(d_0\) the first raw condition holds on the exact prefix, and a true \(r_2>x^{.49}\) always satisfies the second. For an active prime \(\ell\), its local density is \(2/\ell\) below \(w\) and \(1/\ell\) above \(w\), since the two roots are distinct on unit rows outside \(Nv d_0\). In the opened expansion a squarefree test modulus \(k\) is allocated between \(q\) and \(r_2\) into coprime factors \(k_q k_r=k\) according to the violated condition. They are disjoint because no active prime can divide both actual integers. The support of the Selberg square has \(k\le R^2\), so it gives actual divisors \(d=d_0 k_q\le x^{.00401}\) and \(e'=k_r\le x^{.002}\). Each \(d,e=v e'\) has divisor-bounded multiplicity: \(d_0\mid d\), the crossing prime \(\ell\) is its largest prime, and \((k_q,k_r)\) determine the allocated residue condition. The coefficients of the square are divisor-bounded by the standard Selberg formula (for local \(g(p)\le2/p,\ p>2\)); all required masks and weights fall under §2. This supplies an actual fixed-target upper after expansion, not a random-model assumption.

To bound its principal, the standard Selberg quadratic optimum for the local densities \(g(p)=1/p\) or \(2/p\) is \(G_R^{-1}\), where \(G_R=\sum_{k\le R}\mu^2(k)\prod_{p\mid k}g(p)/(1-g(p))\) over active primes. The full sum is the reciprocal of the sieve product. The Gibbs weight on its divisors has expected \(\log k =\sum_{p\le z}g(p)\log p\ll\log z\); choosing \(\zeta\) sufficiently small makes at least half its mass lie below \(R\), by Markov. This shows \(G_R^{-1}\ll\prod_{p\le z}(1-g(p))\) uniformly, also for the two different cutoffs. With the exact unit density \(\phi(N)/N\) the upper principal is consequently at most
\[
 \ll \frac{x\,\mathfrak S(N)}{s p\,r v d_0\,L\log(2w)}\,
                             \Pi(d_0),\qquad
 \Pi(d_0)=\prod_{\ell\mid d_0,\ \ell>2}(1-2/\ell)^{-1}.                 \tag{3}
\]
Indeed omitted primes of \(N\) in the double-root region give just the Goldbach local factor, while omissions in the one-root region are paid by the \(1-1/p\) from \(\phi(N)/N\). The prime 2 changes only an absolute factor. The omitted factor from \(v\) has a single prime base and costs at most 3. Extra omissions from \(d_0\) are bounded by \(\Pi(d_0)\). Ordinary Mertens products give the displayed \(1/(L\log(2w))\).

It remains to sum the prefix weights in this sieve upper. In the full-list case, extending \(d_0\) to all squarefree \(z\)-smooth numbers gives
\[
 \sum_{d_0}\frac{A_\xi(d_0)\Pi(d_0)}{d_0}
       \ll (1+|\xi|)^2.
\]
This follows from \(\sum_{p\le x}\min(2,2|\xi|\log p/L)/p\le2\log(1+|\xi|)+O(1)\), as in the bilateral rough proof; \(\Pi(p)=1+O(1/p)\). In the crossing case, Rankin on \(d_1>D_0/\ell\) with exponent \(c/\log\ell\), where \(c\) is a large **fixed** constant, costs \(e^c e^{-.002c L/\log\ell}\). The weighted Euler sum for \(d_1\) is still \(O_c((1+|\xi|)^2)\): for \(p\le\ell\),
\[
 p^{c/\log\ell}-1\le(e^c-1)\log p/\log\ell ,
\]
so the difference in its Euler logarithm is bounded uniformly by the prime reciprocal-log sum. Choose \(c\) so that \(.002 c>\log2+1\). This pays the factor \(2^{L/\log\ell}\), even after the loss \(L/\log(2\ell)\) from (3). The residual sum
\[
 \sum_{3\le\ell\le z\ {\rm prime}}
        \frac1\ell \frac{L}{\log\ell}\exp(-L/\log\ell)
\]
is uniformly bounded by grouping \(\log\ell\) into factor-two bands and using Mertens. The additional factors \(A_\xi(\ell)\Pi(\ell)\) are \(O(1)\). This proves the overall prefix bound with exactly the two sieve denominators \(L^2\) and only polynomial frequency dependence. The total \(x^{1-c'+o(1)}\) arithmetic errors have uniform frequency bounds before integrating, since \(A_\xi(n)\le2^{\omega(n)}\), including on all prefixes. Integration against \(\widehat h\) is now legitimate and convergent (any fixed \(h\in C_c^\infty\) suffices).

## 4. Size and interpretation of the overlap

In (3) after all prefixes and integration, sum the original physical marks \(s,p,r,v\) with harmonic weights, retaining \(\Lambda(v)\). The first sum is bounded, the \(p\) and \(r\) sums are \(O(a)\), \(O(b)\) for fixed widths (uniformly over the changing \(S\)), and
\(\sum_{v\le1.5x^{2b}}\Lambda(v)/v=O(bL+1)\).
Thus the *actual* overlap is \(O_h(a b^2\,\mathfrak S(N)x/L)+o(M_N)\); this proves (1). In particular a naive use of the second moment of \(H_h\) alone, which loses a square root of \(L\), is not what proves this result.

The literal mask includes real semiprime-by-semiprime adverse rows with \(H_h=H_f=1\). In dyadic actual-pair aggregate their positive weighted mass is \(\gg a b\,Y^2/\log Y\): independently use \(n\in(.70Y,.71Y),m\in(1.30Y,1.31Y)\), select \(s\) in an interior fixed exponent band, and choose the two smaller prime factors a fixed fractional distance inside the logarithmic tag intervals. The final factors are supplied by ordinary PNT on each polynomial product interval, with the harmonic tag masses \(\gg a,b\). The \(q\)-side exponents near .44 and the \(m\)-side exponents near .50 are disjoint, so these are actual even targets with the required unit masks. There is no claimed uniform fixed-target lower occupancy. The bound (1) itself is uniform at each target, and is higher order in \(b\) than the positive balanced semiprime profile mass. It can therefore remove this **literal** profile with an overlap debit controlled by the actual same-target sieve, as opposed to deleting the overlap, squaring a signed test with a lost log, or carrying the first factorial moment as an indicator without justification. The full signed complement and the Goldbach conclusion remain open.
