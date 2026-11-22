# A polynomial prime-cofactor column in the genuine double Möbius identity

Fix \(B>0\), \(0<\alpha<\beta<1/2\), and a compact interval \(J\) of positive length inside \((0,1)\). Write \(L=\log N\). Let \(N\) be any sufficiently large **individual even integer** with \(\operatorname{rad}(N)\leq L^B\). For a moving \(Z\) with \([Z,2Z]\subseteq[N^\alpha,N^\beta]\), let \(\mathcal B\) be any subset of the actual primes in \([Z,2Z]\). There is a fixed \(\kappa>0\) such that
\[
 \sum_{b\in\mathcal B}(\log b)
  \left|\sum_{a\geq1}\log a
     \sum_{\substack{a m+b n=N,\ am\in NJ\\(am,N)=1}}\mu(m)\mu(n)\right|
       \ll_{B,\alpha,\beta,J} N L^{-\kappa}.
 \tag{1}
\]
The positions of \(Z\) and of the selected primes are arbitrary and the implied constants need not be effective. In particular the block remains negligible at the natural weighted binary scale \(N\), with arbitrary bounded masks on \(b\). The \(a\)-sum is the **whole** actual sum, without a cutoff or a mask in \(a\), and its cancellations are used before the absolute value. The \(b\)-cofactors are true primes in a moving **polynomial** range. This is a distinct mixed block from the [simultaneous subpower-width rectangle](../small_radical_reflected_chowla/SubpowerAggregate.md). By summation one may use up to \(L^{\kappa/2}\) fixed-ratio dyadic boxes at an \(O(NL^{-\kappa/2})\) cost. That does not pay a whole interval \([N^\alpha,N^\beta]\) at scale \(N\), or arbitrary composite cofactors \(b\).

Here are more quantitative formulations used in the proof. Take a fixed \(0<\gamma\leq3/20\) and \(w=\exp(L^\gamma)\), or take \(w=1\), which denotes no roughness restriction. Write \(P^-(1)=+\infty\), and define
\[
 E_w(N)=\prod_{\substack{\ell\leq w,\ \ell\ {\rm prime}\\\ell\nmid N}}
            \left(1-\frac1{\ell-1}\right),
 \quad
 S_b(w)=\sum_{\substack{p\in NJ\ {\rm prime},\ p+b n=N\\P^-(n)>w}}
           (\log p)\mu(n).
\]
For any subset \(\mathcal B\) of primes in the **whole** range \([N^\alpha,N^\beta]\), and arbitrary real weights \(0\leq W_b\leq L\), one has
\[
 \sum_{b\in\mathcal B} W_b\,|S_b(w)|
  \ll N E_w(N) L^{-\kappa}\!
      \sum_{b\in\mathcal B}\frac{W_b}{\varphi(b)} + N L^{-10}.
 \tag{2}
\]
Here \(\kappa\) may also depend on the chosen \(\gamma\), and can be taken \(<1/10\); the fixed power \(10\) can be increased at the expense of the choice of \(\kappa\). No tag or multiplicity condition is imposed on \(n\) in (1) or (2).

The exact use of (2) in (1) is that \(\Lambda(x)=\sum_{am=x}\log a\,\mu(m)\). Proper prime powers \(x\) cost \(N^{1/2+o(1)}\) even in the weighted absolute sum over \(b\), because each such \(x\) permits at most \(\tau(N-x)\) prime divisors \(b\) and \(\log x,\log b\leq L\). Central true primes are target units: a prime dividing \(N\) is at most \(L^B\). For \(w=1\), use \(W_b=\log b\) and \(\sum_{Z\leq b\leq2Z}(\log b)/\varphi(b)\ll 1\), by Chebyshev. A whole interval \([N^\alpha,N^\beta]\) instead has this sum of order \(L\), so (2) only gives a relative saving at the larger scale \(NL\) in that interval. Uniformity in \(b\) is averaged in (2), not asserted pointwise for every \(b\).

## 1. Genuine prime moduli and missed-bank mass

Use the bands of §1 of [the true-prime rough parity argument](../true_prime_rough_parity/Proof.md), also allowing \(w=1\) and keeping the same bands above \(\exp(L^{.15})\). Here and below the number \(K\) of colors is fixed and sufficiently large for the projected comparison, before \(N\) grows. There are \(s=\lfloor c\log L/K\rfloor\) disjoint banks for a fixed \(c>0\), each with \(K\) colors among primes \(>\!w\) and at most \(\exp(2L^{.2})\). Within each family the exponents are separated as required in the comparison, and each color has reciprocal prime mass between \(1/4\) and \(1/2\). For a given quotient \(n=(N-p)/b\), set
\[
 U_j(n)=\prod_{\nu=1}^{K}1_{\omega_{j\nu}(n)>0},\qquad
 C(n)=1-\prod_{j\leq s}(1-U_j(n)),
\]
where \(\omega_{j\nu}\) counts the actual distinct prime divisors of \(n\) in its color band. This is a bounded start-to-end mask on the **quotient** \(n\). It never tests \(b\) itself. Every \(b\) is larger than the whole auxiliary bank and every prime dividing \(N\).

For any specified subset \(\mathcal D\) of these bank primes and primes \(\leq w\) not dividing \(N\), one has the weighted genuine prime count
\[
 \sum_{b\in\mathcal B} W_b
    \sum_{\substack{p\in NJ\ {\rm prime}\\p+bn=N\\
                   \ell\nmid n\ (\ell\in\mathcal D)}}\log p
 =
 |J|N\sum_{b\in\mathcal B}\frac{W_b}{\varphi(b)}
       \prod_{\ell\in\mathcal D}\left(1-\frac1{\ell-1}\right)
   +O_A(NL^{-A}).
 \tag{3}
\]
Use upper and lower Bonferroni with successive orders near \(R_0=\lfloor L^{.1}\rfloor\). The conditions for a selected squarefree \(g\) on primes of \(\mathcal D\) are exactly \(p\equiv N\bmod b g\), a reduced class. The modulus is \(\leq N^{\beta+o(1)}\), within ordinary prime Bombieri–Vinogradov, and **uniquely** recovers its one polynomial-sized prime \(b\) and then \(g\). Each fixed truncation on the specified union uses each such modulus once, so the total absolute prime discrepancy is \(O_A(NL^{-A})\) even with \(W_b\leq L\), choosing the input logarithmic accuracy first. This is true prime BV: if written for prime powers, the aggregate difference costs at most \(N^{1/2+o(1)}\), since for each proper prime power \(p^j\) all moduli counted divide \(N-p^j>0\), at most \(\tau(N-p^j)\). The main bracket omission is bounded by
\((C_0\log L)^{R_0}/R_0!\) times \(N\sum_b W_b/\varphi(b)\). Here each forbidden root is nonzero at its prime, and \(\sum_{\ell\in\mathcal D}1/(\ell-1)\ll\log L\). If a roughness prime divides \(N\), it cannot divide \(n\) on these central true-prime rows, and was correctly omitted from \(\mathcal D\). This proves (3).

Use the exact expansion of \(1-U_j\) into nonempty subsets of colors imposing no hit. The product over the families has at most \(2^{Ks}=L^{O(1)}\) terms counted with multiplicity. Apply (3) to these terms with the roughness primes included. All families and the roughness set are disjoint. Conditional on the base rough restriction, the model success probability for each family equals
\[
 u_j=\prod_{\nu=1}^{K}
     \left(1-\prod_{\ell\in\mathcal B_{j\nu}}
                     (1-1/(\ell-1))\right)
       \geq (1-e^{-1/4})^K.
\]
It follows that the total positive prime log weight, with \(W_b\) and \(n\) rough, missed by \(C(n)\) is at most
\[
 O_K\!\left(N E_w(N) L^{-\kappa_0}
                    \sum_{b\in\mathcal B}\frac{W_b}{\varphi(b)}\right)
    +O_A(NL^{-A})
 \tag{4}
\]
for some fixed \(\kappa_0>0\). The BV accuracy can pay all patterns before the limit. For a substantial dyadic prime bank the harmonic mass in (4) is of order \(1/L\) without weights, or of order one with \(\log b\) weights. Nothing identifies an exponent-width window with a single dyadic box.

## 2. The same covered sum in Vaughan Type II

It suffices to bound the covered signed sum for arbitrary complex coefficients \(c_b\) with \(|c_b|\leq W_b\). This allows taking all signs separately after the estimate, not just a cancellation averaged with a prescribed weight. Replace the genuine prime weight by \(\Lambda(x)1_{P^-(x)>z}\), where \(z=\exp(L^{.24})\) and \(x\in NJ\). All genuine central primes are unaffected; proper powers again cost \(N^{1/2+o(1)}\), since for each \(x\) the number of possible \(b\)'s is at most \(\tau(N-x)\), and all weights are bounded by \(L^2\). Write \(R=\operatorname{rad}(N)\leq L^B\). The rough source enforces \((x,R)=1\) and hence \((N-x,R)=1\), which we may keep explicitly in every term.

Use Vaughan's identity (8) of the [true-prime rough proof](../true_prime_rough_parity/Proof.md) with both short parameters
\[
              D=N^{(1-\beta)/16}.
\]
The small \(\Lambda_{\leq D}\) term vanishes centrally. In its Type II term the two actual source slots have length at least \(D\), are \(z\)-rough and target units; one has the genuine \(\mu\) coefficient and the other has the indicated truncated von Mangoldt divisor sum bounded by \(L\). These are exactly the admissible slots in the [projected minor](../target_slope_switch/Proof.md) and [small-radical major](../small_radical_projection/Proof.md). In particular the actual roughness on the expanded source \(x\) implies avoidance of all auxiliary bank primes by both source factors and gives the primitive endpoints of that comparison. No removal of source avoidance from the JLL argument is needed here.

Expand the first-active identity \(C(n)=\sum_j U_j(n)\prod_{i<j}(1-U_i(n))\). In a selected family \(j\), extract \(u\mid n\) with one actual prime from each color, and write \(n=u v\). When \(n\) has no square of a bank prime, the exact reciprocal hit weight is \(\prod_\nu(1+\omega_{j\nu}(v))^{-1}\), earlier-family events are those of \(v\), and \(\mu(n)=(-1)^K\mu(v)\). The rough quotient gate is exactly \(P^-(v)>w\), because \(u\) uses primes above \(w\). On bank square rows the same replacement has total absolute coefficient at most one per \(b\), before \(c_b\): the number of tag choices is \(\prod_\nu\omega_{j\nu}(n)\), the reciprocal denominators are at least those \(\omega_{j\nu}(n)\), and only the first active family contributes. Failure of the sign replacement requires \(r^2\mid n\) for a bank prime \(r\) and thus \(r^2\mid N-x\). There are \(O(N\exp(-c_1L^{.15}))\) such integers \(x\). Their total contribution, for the original and the replaced weight even after the source divisor expansion, is smaller than every logarithmic power, by Cauchy applied to \(L^2\tau(x)\tau(N-x)\), the fourth moments of the divisor function, and the stated count. We can therefore use the replaced coefficients without imposing an extra square mask in the operator.

With \(h=bv\) we have the actual projected equation \(N-x=u h\), and the entire dependence on \(b\) is in the single residual function
\[
 \mathcal H_j(h)=(-1)^K\!\!
 \sum_{\substack{b\in\mathcal B\\b\mid h}}c_b\,\mu(h/b)
     1_{P^-(h/b)>w}\prod_{i<j}(1-U_i(h/b))
        \prod_{\nu=1}^{K}(1+\omega_{j\nu}(h/b))^{-1}.
 \tag{5}
\]
If needed retain \((h,R)=1\) as an extra mask. Neither the mask \(C\) nor its normalization requires any control of how the \(b\)'s distribute within a residue class; \(|\mathcal H_j(h)|\leq L\tau(h)\) and
\(\sum_{h\leq X}|\mathcal H_j(h)|^2\ll X L^5\) for \(X\ll N\). In a tag shell \(u\asymp Y\), the projected packet second moment is \(O_A(NY L^{-A})\) for every requested fixed accuracy after choosing \(K\) sufficiently large. Its Cauchy extraction uses the actual norm on \(h\ll N/Y\) just given. Tag normalization is bounded in terms of fixed \(K\). Narrow multiplicative source mesh boxes handle the central product cutoff: the crossing strips contain \(O(NL^{-F}+1)\) integers for a mesh exponent \(F\), and the same divisor moments and bounded total hit weight before \(c_b\) pay them. Taking the packet accuracy and mesh before \(K\) pays all log counts of boxes, banks, and smooth shells. Thus the signed covered Type II sum is \(O(NL^{-10})\), with any desired enlargement of this fixed exponent by choosing the constants accordingly.

## 3. Exact Type I with squarefree-sensitive quotient Möbius

Use the **same** covered mask \(C(n)\) in Type I, but expand it into the exact signed avoidance patterns of §1; multiply them by the true \(P^-(n)>w\) gate. We do not take the residual (5) into progressions. In the Type I source write \(x=d k\) with \(d\leq D^2\), \(d\) \(z\)-rough, and a grouped coefficient \(O(L)\), using \(\sum_{r\mid d}\Lambda(r)=\log d\); for the first Vaughan term the additional weight \(\log k=\log((N-bn)/d)\) on its central interval also has supremum and total variation \(O_J(L)\). The unit condition can be imposed as \((n,R)=1\) and \((d,R)=1\); it enforces the corresponding unit condition on \(k\).

For a fixed avoidance pattern, open source roughness on \(k\) by squarefree \(e\) with only primes \(\leq z\) outside \(R\), and open the quotient avoidance by squarefree \(g\) on the selected primes outside \(R\) from the pattern. Truncate both inclusion–exclusions at \(R_0=\lfloor L^{.1}\rfloor\). Apply the upper bound on each positive Bonferroni tail after opening the other, using the absolute normalized coefficients. Because \(b\) and all auxiliary choices are units at \(R\), a retained row must have \((de,bg)=1\), else the exact equation forces a common prime of \(de,bg\) to divide \(N\). Hence a specified \(d,e,b,g\) gives at most \(N/(d e b g)+O(1)\) rows (for the first opening take \(g=1\)). The main tail is at most a fixed log power times \(N(C_0\log L)^{R_0+1}/(R_0+1)!\). The absolute reciprocal masses of the other truncated factors are at most fixed powers of \(L\). All floor errors combined, even before discarding incompatible masks, are at most
\[
       N^{\beta+(1-\beta)/8+o(1)}=o(NL^{-A}) \quad(A\text{ fixed}),
\]
since \(d\le D^2\), all counts of \(e,g\) are \(N^{o(1)}\) from their prime bounds and factor caps, and \(b\leq N^\beta\). The same reasoning applies to both Bonferroni tails with \(|\mu(n)|\leq1\). The \(L^{O(1)}\) signed patterns are paid by increasing accuracies.

Fix a retained pair \(b,g\) and write \(n=g v\), with \(X=N/(b g)\geq N^{1-\beta-o(1)}\). The arithmetic conditions on \(v\) are
\[
     v\equiv N\overline{b g}\pmod {de},\qquad(v,R)=1 .
\]
They give reduced classes modulo \(de R\), after splitting the unit mask into at most \(R\) classes. The moduli are \(\leq N^{(1-\beta)/8+o(1)}\). Because \(d\) uses primes \(>z\), \(e\) uses primes \(\le z\), and \(de\) is coprime to \(R\), each such modulus recovers \(d,e\) uniquely. The Möbius weight is not completely multiplicative here. Use the exact Euler-factor identity, valid since \(g\) is squarefree,
\[
 \mu(g v)=\mu(g)\mu(v)1_{(v,g)=1}
        =\mu(g)\sum_{\substack{j\mid v\\
                         r\mid j\Rightarrow r\mid g}}\mu(v/j).
 \tag{6}
\]
The prime condition on \(r\) is understood only for prime divisors. It is the convolution of \(\mu\) with the all-exponent integers supported on the primes of \(g\). The factor \(j\) is automatically a unit modulo \(deR\). For every \(j\leq X^{1/4}\) use the classical Siebert–Wolke maximal-prefix Möbius Bombieri–Vinogradov theorem, in the form [Lü–Wang–Wu, (3.1)](https://arxiv.org/html/2610.20242v2#S3), at actual size \(X/j\geq X^{3/4}\). The moduli lie below \((X/j)^{.42}\), with room. The true residue is \(N\overline{b g j}\bmod de\), and the unit mask modulo \(R\) is still split into at most \(R\) reduced residue classes. The maximal-prefix estimate handles both literal central endpoints and partial summation of \(\log k\) at each \(d,e\). Sum over the factorizations at each modulus as above, and over \(j\) with cost
\(\sum_{j:\,r\mid j\Rightarrow r\mid g}1/j
=\prod_{r\mid g}(1-1/r)^{-1}\ll L^{O(1)}\).

For the remaining \(X^{1/4}<j\leq X\) the count of integers on this fixed \(g\)-support is at most \((1+\lfloor L/\log2\rfloor)^{\omega(g)}=\exp(O(L^{.1}\log L))=N^{o(1)}\); their harmonic mass is at most \(X^{-1/4}N^{o(1)}\). Use \(X/(j de)+1\) rows per retained \(d,e,j\) by the reduced progression. Their contribution has a polynomial saving relative to \(X\): the reciprocal \(de\)-mass is polylogarithmic, and the floor count over \(d,e\) is \(\leq N^{(1-\beta)/8+o(1)}=o(X L^{-A})\). This is why the prime factor cap on \(g\) is used even when opening the exact, unroughened \(\mu\) coefficient. We obtain \(O_A((N/(b g))L^{-A})\) uniformly for fixed \(b,g\), after log coefficient and partial-summation costs. Summing over \(b,g\) in reciprocal mass and paying all patterns proves the required signed covered Type I bound. It is not a progression estimate for arbitrary residual functions.

Types I and II together give \(O(NL^{-10})\) on the covered sum, uniformly in arbitrary \(c_b\). Now (4) pays the uncovered error against \(|\mu(n)|\leq1\). Taking each coefficient to realize \(W_b|S_b(w)|\) by duality proves (2), with \(\kappa\leq\kappa_0\) decreased as necessary. As explained at the start, (1) follows.

## 4. Auxiliary actual quotient sign densities and limits

The exact squarefree main terms hold in summed absolute error across \(b\in\mathcal B\) (fixed \(A>0\) arbitrary):
\[
 \sum_{b\in\mathcal B}
   \left|
    \sum_{\substack{p\in NJ\ {\rm prime},\ p+bn=N\\P^-(n)>w}}
                 (\log p)\mu(n)^2
       -\frac{|J|N}{\varphi(b)}\,D_b(w;N)
   \right|
    \ll_A NL^{-A},
 \tag{7}
\]
where for \(w>1\) take \(D_b(w;N)=E_w(N)\). Indeed (3), with no banks and with arbitrary bounded coefficients on \(b\), also gives this unsigned prime count without \(\mu(n)^2\), using the absolute per-modulus BV errors before duality. The excluded squareful integers contribute at most
\(L\sum_{r>w}\lfloor N/(b r^2)\rfloor\ll NL/(b w)\) per \(b\), by actual integer multiples inside the rough sample. Here \(r\) is prime, and there is no remainder from the floor upper bound.

For \(w=1\) the model is
\[
 D_b(1;N)=
    \left(1-\frac1{b^2}\right)
    \prod_{\substack{\ell\nmid N,\,\ell\ne b\\\ell\ {\rm prime}}}
                 \left(1-\frac1{\ell(\ell-1)}\right).
 \tag{8}
\]
To see this, expand \(\mu^2(n)=\sum_{e^2\mid n}\mu(e)\) and retain \(e\leq N^\delta\) with \(0<\delta<\alpha\) and \(\beta+2\delta<1/2\). These moduli \(b e^2\) lie strictly below the prime BV square-root threshold; \(b\) is the unique prime above \(N^\alpha\), and \(e\) is then determined. Retained \(e\)'s must be coprime to \(N\); nonunit classes contain no central true prime. Actual proper powers in the use of BV are again negligible by the divisor bound. The integer upper bound for the tail \(e>T=N^\delta\) is \(O(NL/(b T))\) per \(b\). The main tail is \(\ll (N/\varphi(b))\sum_{e>T}1/\varphi(e^2)\ll(N/\varphi(b))T^{-1+o(1)}\). In the completed Euler product the ratio \(\varphi(b\ell^2)/\varphi(b)\) is \(\ell(\ell-1)\) for \(\ell\ne b\), and \(b^2\) for \(\ell=b\), which explains the local factor in (8) even though \(e\leq N^\delta\) never contains \(b\). Both models are positive. The unrough model is bounded below by an absolute constant; the rough model is \(\asymp \mathfrak S(N)/\log w\) with the usual binary singular series, including its factor at \(2\), by the product computation in the [true-prime rough proof](../true_prime_rough_parity/Proof.md).

For a full dyadic prime bank, or any chosen bank with \(\sum_{b\in\mathcal B}1/\varphi(b)\gg1/L\), (2) with \(W_b=1\) and (7) show that outside relative \(O(L^{-\kappa/2})\) exceptional \(1/\varphi(b)\)-mass, each of the two signs occurs at the **same exact** \(b\) in the count
\[
   (1+O(L^{-\kappa/2}))
       \frac{|J|N D_b(w;N)}{2\,\varphi(b)\,L}.
 \tag{9}
\]
Indeed \(1_{\mu(n)=\pm1}=(\mu(n)^2\pm\mu(n))/2\), and \(\log p=L+O_J(1)\). Apply Markov's inequality to the individual weighted absolute errors with thresholds \(N D_b(w;N)L^{-\kappa/2}/\varphi(b)\); the summed \(O_A(NL^{-A})\) error is negligible relative to the actual base density, which is bounded below by a fixed negative log power. In particular the two counts are strictly positive for every sufficiently large nonexceptional \(b\) in this harmonic sense. No individual \(b\) is guaranteed nonexceptional without an extra estimate.

Even with the rough gate, (9) includes high-rank squarefree \(n\). The two-form upper sieve for \(n,N-bn\) bounds the **prime** \(n\) contribution to its prime log weight by \(O((N/b)\mathfrak S(N)/L)\) in this polynomial range. The local root counts differ from the ordinary binary ones only at \(b\), where \(N-bn\) is a nonzero constant, giving a bounded factor. The allowed error in (9) is much larger on the weight scale, since \(\gamma+\kappa/2<1\). No assertion about a prime quotient, bounded rank, \(b=1\), or an unconditional binary prime pair follows. Moreover (1) has no arbitrary short-\(a\) mask: summing the complete \(a\)-leg to a true prime or prime power was essential.

The closest inputs are [Lü–Wang–Wu v2, Theorems 1–2](https://arxiv.org/html/2610.20242v2) at a fixed shift, the distinct unconditioned prescribed small-radical true-prime parity in the cited companion, and the direct reflected geometry of the [small-radical comparison](../small_radical_projection/Proof.md). The latter does not by itself pay the unmarked weighted mass at a polynomial cofactor. The reported October Guo reflected parity work is compared with the \(b=1\) companion there; its exact underlying text was unavailable at that audit and no theorem about its polynomial quotient range is inferred. No priority claim is made.
