# A true ternary evaluation for small nonzero aliases of the fixed Goldbach target

A companion to the [exact top delta sector](https://github.com/mxym/math/blob/main/research/theory-2026-11-20/strong-goldbach/LargeConductorDeltaSectors.md). This evaluates actual off-target aliases in a specified prime-modulus tranche. It does not estimate the common target atom, the whole centered delta sector, or the sign required for Goldbach. The proof is a classical three-input circle argument with an explicit short-window treatment of the longer factors.

Let \(X=N\) be even, \(L=\log X\), \(Q=X^{1-\delta}\) with \(0<\delta<1/4\) fixed, and let \(w,g\) be nonnegative smooth fixed compact interior weights in \((0,1)\), with \(\int w>0\) and \(g=1\) near \(1-\operatorname{supp}w\). Let \(u\) be a smooth nonnegative weight supported in a fixed compact subinterval of \((0,1)\), not identically zero. Define the actual two-prime profile
\[
 R(M)=\sum_{p+p'=M}(\log p)(\log p')w(p/X)g(p'/X).
\]
For every fixed \(D,A>0\), uniformly for \(0<|k|\le L^D\),
\[
 \sum_{q\ {\rm prime}}(\log q)u(q/Q)R(N+kq)
 =XQ\,\mathfrak S_k(N)\int w\int u+O_{A,D,\delta,w,g,u}(XQ L^{-A}).
 \tag{1}
\]
Here the true local factors are
\[
 \mathfrak S_k(N)=
 \prod_{\ell\mid k}\left(1+\frac{c_\ell(N)}{(\ell-1)^2}\right)
 \prod_{\ell\nmid k}\left(1-\frac{c_\ell(N)}{(\ell-1)^3}\right),
 \qquad
 c_\ell(N)=\begin{cases}\ell-1&\ell\mid N,\\-1&\ell\nmid N.\end{cases}
\]
The odd \(k\) case is identically zero in the actual count for large \(X\), since all three primes are then odd. For even \(k\), \(\mathfrak S_k(N)\gg1\) uniformly: the factor at \(2\) is \(2\), and every odd factor is at least \(1-1/(\ell-1)^2\).

## Three factors with the genuine phase

Use \(F_w(\alpha),F_g(\alpha)\) for the log-weighted prime polynomials on scale \(X\), and \(U(\alpha)\) on scale \(Q\) for \(u\). The exact signed representation of the left side of (1) is
\[
 \int_{\mathbb T}F_w(\alpha)F_g(\alpha)U(-k\alpha)e(-N\alpha)\,d\alpha .
\]
Take ordinary short-polynomial major arcs at reduced denominators \(\le L^B\) and widths \(L^B/(qQ)\), with \(B\) chosen sufficiently large. Outside their preimage under \(\alpha\mapsto-k\alpha\), the standard Vaughan prime exponential-sum estimate, Dirichlet approximation and partial summation give \(|U(-k\alpha)|\ll QL^{-A-3}\), increasing \(B\) for the claimed precision. Parseval and Cauchy on the two long factors give \(O(XL)\) for their absolute integral over the full circle; this part is \(O(XQ L^{-A})\).

In the preimage there are only \(L^{O_{B,D}(1)}\) neighborhoods, centered at reduced \(a/d\) with \(d\le |k|L^B\), each of half-width at most \(L^B/Q\). A pointwise long-prime Siegel–Walfisz approximation followed by derivative loss at that full width would not justify the next step. Instead, for each true long polynomial and each such rational, one has
\[
 \int_{|\beta|\le L^B/Q}
 \left|F_v(a/d+\beta)
   -\frac{\mu(d)}{\varphi(d)}\int_0^X v(t/X)e(t\beta)\,dt\right|^2d\beta
 \ll_{A',B,D} X L^{-A'}\qquad(v=w,g)
 \tag{2}
\]
for arbitrary fixed \(A'\). To get (2), expand into Dirichlet characters at \(d\le L^{B+D}\), and apply [Mikawa's Lemmas 1 and 2](https://tsukuba.repo.nii.ac.jp/record/15921/files/2.pdf) with short length comparable to \(Q/L^B\). This length is between \(X^{1/5+\epsilon_0}\) and \(X^{1-\epsilon_0}\) for some fixed \(\epsilon_0>0\) depending on \(\delta\). The lemmas apply to the prime-log centered Mangoldt polynomial via its principal mean; fixed smooth weights follow by partial summation over partial intervals. For clarity, a truncated interval endpoint changes the corresponding short-interval integrals only within \(O(Q/L^B)\) of that endpoint, and bounding these rows trivially costs \(O((Q/L^B)L^{O(1)})\) after dividing by the square of the short length. Fixed compact supports can be covered by finitely many such dyads. The discrepancy between the continuous principal integral and its discrete smooth sum is negligible by Poisson summation. The bad nonunit prime powers have total \(O(L^2)\) per \(d\); ordinary Parseval for all true proper prime powers gives squared norm \(O(\sqrt X L^2)\), negligible for (2). Character orthogonality or even a fixed power of \(L\) losses in the Gauss expansion are harmless upon increasing \(A'\).

Now take the long major set defined by denominators \(d\le L^{B+D}\), with \(|\beta|\le L^H/X\), \(H\) fixed sufficiently large. On each preimage neighborhood, its part outside the long major set has \(|\beta|> L^H/X\). By smooth Fourier decay the model part of (2) has squared mass \(O_A(XL^{-A})\) there; the same is therefore true for the entire \(F_v\), with \(A'\) taken large. Use \(U\ll Q\), Cauchy for the two long inputs, and sum over the polynomial-log number of neighborhoods. This pays all of the collar \(L^H/X<|\beta|\le L^B/Q\) in the true three-prime integral, without averaging \(N\).

## Long majors and actual local factors

The long major set is disjoint for sufficiently large \(X\). On each of its arcs all three polynomials have their usual principal approximation by Siegel–Walfisz and partial summation: for the short factor the reduced denominator is \(d'=d/(d,k)\), and \(|k\beta|Q\ll L^{D+H}X^{-\delta}=o(1)\). The uniform resulting product error is \(O_A(XQ L^{-A})\) after summing and integrating over the arcs. The arithmetic coefficient at modulus \(d\) is
\(\mu^2(d)\mu(d')c_d(N)/(\varphi(d)^2\varphi(d'))\). This is multiplicative, so its Euler factors are those displayed in (1). Its absolute tail beyond \(L^{B+D}\) is \(O_\epsilon(|k|L^{-(B+D)(1-\epsilon)})\), using \(|c_d(N)|\le d\) and \(\varphi(d')^{-1}\ll_\epsilon(d')^{-1+\epsilon}\). Increase \(B\) as needed. The real integral can be completed to the line to arbitrary log accuracy by smooth decay of the two long profiles. By Fourier inversion it is exactly
\[
 XQ\int u(t)\,dt\int w(s)\,ds ,
\]
since \(|k|Q/X=o(1)\) and \(g=1\) near the reflected support. This completes (1).

## Scope in the original delta expression

For a prime \(q\) in the top constant-kernel regime, \(c_q(N-p-p')=q\,1_{p+p'\equiv N\bmod q}-1\). In its prime–prime part the actual nonzero aliases are therefore precisely \(R(N+kq)\). Equation (1) genuinely evaluates these aliases after summing over actual prime \(q\) in this tranche. Partial summation permits the smooth extra factor \(1/\log q\) used to change from the log-prime count to the original unweighted modulus sum: on the fixed support the derivatives of \(L/\log(Qt)\) are uniformly bounded, and the same proof is uniform under those bounded derivative norms.

The original range can have \(|k|\) as large as \(X/Q\), not merely a fixed power of \(\log X\). Polynomial \(k\) in the preimage can introduce polynomial conductors, outside the small-modulus collar estimate (2). Likewise this calculation does not include arbitrary composite moduli and does not remove the centered subtraction or the atom with \(k=0\). In particular (1) is a booked true off-target piece, not a bound for the full negative contribution at \(N\).


## A paired positive/negative cancellation in the exact centered prime-modulus tranche

The small-alias result can be inserted after the **actual low-input-conductor deletion** in the linked top delta argument. For a prime modulus \(q\asymp Q\) the only proper inducing conductor is \(1\), so the retained vector is precisely the actual residue prime sum minus its own mean on units. For \(v=w,g\), write
\[
 \Theta_v=\sum_{p\ {\rm prime}}(\log p)v(p/X),\qquad
 \rho_v(q)=\frac{q\Theta_v}{(q-1)X\int v},\qquad
 B_{v,q}(n)=v(n/X)\big((\log n)1_{n\ {\rm prime}}-\rho_v(q)1_{(n,q)=1}\big),
\]
where the weight is on positive indices only. The weighted test \(g\) can be taken identically one on a fixed neighborhood of the reflected support, so both \(\int v\) are positive. For each reduced class \(a\bmod q\), the periodized smooth lattice count in that residue is \(X\int v/q+O_M((X/q)(q/X)^M)\), by Poisson. Hence summing \(B_{v,q}\) in that class gives exactly the retained prime vector up to a uniformly power-small error. Both vectors are zero in the nonunit class since all actual input primes exceed \(q\). Summing these errors against the other vector in the whole top constant-kernel expression, using \(\ell^1\) total \(O(X)\) at each \(q\), is negligible for arbitrarily large \(M\). Thus the true high-character block there is, up to such an error, a sum over literal aliases of \((B_{w,q}*B_{g,q})(N+kq)\) with the original coefficient \(c_Q C_{q/Q}/Q\).

For \(|k|\le L^D\) the archimedean factors of the mixed prime–lattice convolutions and the lattice–lattice convolution are exactly \(\int w\), by the support assumption on \(g\). The actual \(\rho_v(q)=1+O_A(L^{-A})\) by the prime number theorem. Removing nonunit lattice indices costs \(O((X/q+1)L)\) per mixed or lattice term by trivial counting (a fixed number of residue classes), and is power-small. Ordinary smooth PNT for the mixed pairings and integer summation for the lattice–lattice case are uniform in the literal \(kq/X\). Their net contribution at each alias is therefore \(-X\int w+O_A(XL^{-A})\). This uses the unit-lattice subtraction, which includes even integers at odd \(q\); it is not a parity-conditioned mean.

With any fixed smooth \(u\) compactly supported inside the top prime-modulus range, normalized summation and (1) give for every nonzero \(|k|\le L^D\),
\[
 \frac1Q\sum_{q\ {\rm prime}}u(q/Q)(B_{w,q}*B_{g,q})(N+kq)
 = \frac{X\int w}{Q}\left(\sum_{q\ {\rm prime}}u(q/Q)\right)
       \bigl(\mathfrak S_k(N)-1\bigr)+O_A(XL^{-A}).
 \tag{3}
\]
To remove the log on \(q\) exactly in (1), apply it with weight \(u(t)\log Q/\log(Qt)\), which has uniformly bounded derivatives of each fixed order on the support. One may choose \(u\) to incorporate the smooth constant-kernel weight for the chosen tranche. Formula (3) retains the true signs: the even \(k\) term is positive to leading order since \(\mathfrak S_k(N)\ge 2C_2\ge9/8\) (the telescoping product over integers \(n\ge2\) of \(1-n^{-2}\) is \(1/2\), and \(n=3\) is absent from \(n=p-1\) for odd primes); the odd \(k\) term is negative with multiplier \(-1\).

Those two sides can be combined without a loss proportional to their separate sizes. For odd primes put
\[
 P_\ell=1-\frac{c_\ell(N)}{(\ell-1)^3},\qquad
 j(\ell)=\frac{1+c_\ell(N)/(\ell-1)^2}{P_\ell}-1 ,
\]
and extend \(j\) multiplicatively on odd squarefree integers (zero on other indices). Thus \(P_\ell(1+j(\ell)/\ell)=1\) exactly. The bounds \(|j(\ell)|\ll \ell^{-1}\) for \(\ell\mid N\), and \(\ll\ell^{-2}\) otherwise, give
\[
 \sum_d |j(d)|\ll (\log\log(3N))^{O(1)}
\]
uniformly in \(N\); to bound the target-prime reciprocal sum, split at \(\log N\) and use Mertens below it and \(\omega(N)\ll\log N\) above. When \(N\) is dyadic the displayed sum is bounded absolutely. For \(K\ge1\), sum the even formula \(\mathfrak S_{2k}(N)=2\prod_{\ell>2}P_\ell\sum_{d\mid k}j(d)\), comparing each floor of \(\lfloor K/2\rfloor/d\) with its argument (also for \(d>\lfloor K/2\rfloor\)). The product identity gives
\[
 \sum_{1\le k\le K}(\mathfrak S_k(N)-1)
   =O((\log\log(3N))^{O(1)}),
\]
or \(O(1)\) for \(N=2^j\). Negative aliases have the same singular factors. Summing (3) with all \(0<|k|\le L^D\) therefore gives total
\[
 O\!\left(\frac{X}{\log X}(\log\log(3N))^{O(1)}\right)=o(X)
\]
on the chosen prime-modulus tranche, and \(O(X/\log X)\) for the dyadic targets. The errors in (3) are arbitrary-log small before summing \(k\). For \(D>1\) the absolute main contributions of the two parities separately can exceed order \(X\); this is a real signed cancellation, not an absolute deletion of individually small pieces.

No result is claimed for composite moduli, \(|k|\) in the polynomial portion of the range, or \(k=0\). The \(o(X)\) bound here also need not be below the \(X/\log X\) reserve in an extreme exceptional-zero regime. None of these booked aliases gives a lower bound for the common target atom.


For completeness the same estimate covers all **prime** moduli in the top range \(Q/L^{C}\le q\le Q\) of the linked deletion theorem, for fixed \(C\), when summed with its original coefficient. Decompose into fixed-ratio dyadic ranges of scale \(Q'\) between \(Q/L^C\) and \(Q\). The short scale \(Q'\), being \(X^{1-\delta}\) up to a fixed log power, stays in exactly the same uniform Mikawa and prime-sum ranges. Take the sharp dyadic endpoint or given top endpoint by Stieltjes partial summation in the short input; the finitely many needed estimates therein are uniform in partial short intervals, including their archimedean integrals. On a dyadic slice the coefficient \(C_s=\sum_j\omega(sj)/j,\ s=q/Q\), has bounded derivatives under \(s\partial_s\) of all fixed orders, uniformly in \(s\), since \(sj\) stays in the fixed interior support of \(\omega\). Thus this coefficient and \(1/\log q\) introduce no changing-scale loss. Formula (3) on one slice carries size \(X(Q'/Q)/L\) per main coefficient. Summing \(Q'/Q\) geometrically, and absorbing the log-power number of errors with arbitrary input savings, proves the same combined \(o(X)\) bound for all prime moduli in this top range. This calculation is before the product-conductor cut; any previously justified global deletion of that type is a separate operation, not silently commuted with alias selection.


## Extension to top moduli with a large true prime and a polylogarithmic cofactor

Fix \(C,C_0\). The same combined cancellation holds on the top slice \(Q/L^{C_0}\le q\le Q\) restricted to actual \(q=mr\), \(m\le L^C\), \(r\) prime, with modulus weight as in the exact delta expression. Here we take the available high-input-conductor cutoff \(R_0=Q/L^{K_0}\) with \(K_0>C+C_0+2\). In particular \(r>R_0\), \((m,r)=1\), and this large prime label is unique. This statement allows nonsquarefree \(m\).

After input projection all \(r\)-nonprincipal characters remain (their conductors are at least \(r>R_0\)) and all \(r\)-principal ones are absent (their conductors divide \(m<R_0\)). On unit classes the projected vector is therefore the genuine prime AP sum modulo \(q\) minus \(\Theta_v(a\bmod m;m)/(r-1)\), where \(\Theta_v(c;s)=\sum_{p\equiv c\bmod s}\log p\,v(p/X)\). Expand the literal Ramanujan coefficient by the divisor identity
\[
 c_q(N-a-b)=\sum_{\substack{d\mid q\\d\mid N-a-b}}\mu(q/d)d.
\]
When both input vectors are pushed forward to units modulo \(d\), the result is zero if \(r\nmid d\), by their zero sum in the \(r\)-variable at each fixed unit \(m\)-class. Otherwise \(d=sr,\ s\mid m\). Pushing down the subtracted means gives exactly \(\Theta_v(a\bmod s;s)/(r-1)\); this includes all lifts on units. The coefficient at \(sr\) in the constant-kernel expression is consequently \(c_Q C_{mr/Q}\mu(m/s)/(Q(m/s))\), times the congruence form on these two **truly centered** vectors at \(sr\).

Replace each vector by projection of an actual lattice-centered sequence as above, now taking density
\[
 \rho_v(a\bmod s;s,r)=\frac{sr\,\Theta_v(a\bmod s;s)}{(r-1)X\int v}
   =\frac{s}{\varphi(s)}+O_A(L^{-A})
\]
on unit classes. Poisson on the progression modulo \(sr\) makes this replacement arbitrarily power-small, uniformly in the fixed logarithmic ranges. The last equality uses Siegel–Walfisz at \(s\le L^C\). Omitting indices divisible by \(r\) from the actual mixed and lattice terms costs \(O((X/r+1)L^{O(1)})\) per alias, harmless. The remaining lattice congruence modulo \(s\) for the literal target \(N+ksr\) is exactly \(a+b=N\bmod s\). The principal factor for each of the three mixed or pure lattice terms is
\[
 B_s(N)=\frac{s}{\varphi(s)^2}\#\{a\bmod s:(a,s)=(N-a,s)=1\}
       =\prod_{\ell\mid s}\left(1+\frac{c_\ell(N)}{(\ell-1)^2}\right).
\]
This follows by the genuine unit CRT counts, with one prime marginal supplied by ordinary Siegel–Walfisz and the lattice slots by smooth counting. The archimedean factor is still \(X\int w\). The true prime–prime term at this alias is (1) with coefficient \(ks\) and short scale \(Q/m\) up to a fixed log power, so its factor is \(\mathfrak S_{ks}(N)\) without a change of target. Thus the actual centered net coefficient is \(\mathfrak S_{ks}(N)-B_s(N)\).

The primes dividing \(s\) are now forced into the first local factor of \(\mathfrak S_{ks}\), including factor \(2\) when \(s\) is even. At other odd primes averaging over divisibility of \(k\) gives precisely 1 by the previous \(P_\ell(1+j(\ell)/\ell)\) identity; at \(2\) not dividing \(s\) averaging the even and odd \(k\)'s gives 1 as before. The same floor estimate, using only primes not dividing \(s\) in the absolutely summable divisor weights, shows uniformly
\[
 \left|\sum_{1\le k\le T_0}(\mathfrak S_{ks}(N)-B_s(N))\right|
   \ll B_s(N)(\log\log(3N))^{O(1)} .
\]
The same holds for negative aliases. After averaging actual prime labels \(r\) on dyadic slices and removing their log weight, the normalization is \(O(X/(mL))\); the dyadic relative scales sum geometrically as in the prime-modulus case. Multiply by \(1/(m/s)\) from the exact Ramanujan coefficient and use
\[
 \sum_{m\le L^C}\frac1m\sum_{s\mid m}\frac{s}{m}
   =\sum_{m\le L^C}\frac{\sigma(m)}{m^2}\ll\log L .
\]
Also \(B_s(N)\ll(\log\log(3N))^{O(1)}\) uniformly. All other sums range over only fixed log powers in \(m,s,k\), so arbitrary log accuracy absorbs their errors. This pays the combined centered aliases \(0<|k|\le L^D\) for these composite moduli also, by \(O(X(\log\log(3N))^{O(1)}/L)=o(X)\). In the divisor-expanded expression, \(k\) here is the literal alias of the **projected** modulus \(sr\), not of \(mr\) before expansion. No other composite modulus or polynomial alias is covered.
