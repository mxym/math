# A completely multiplicative sparse-target obstruction at every large power of two

Written research note, 2026-11-24. The surrogate below is **not** Liouville: in particular its signs at the true primes are not prescribed to be \(-1\). This only separates complete multiplicativity plus strong one-function Fourier/AP estimates from what is needed for restricted-target G23. All prime slopes, marked windows, rough tests, and planted prime complements are genuine. A separate deterministic conclusion at the end uses actual \(\lambda\).

## 1. The restricted-target claim being tested

Fix \(0<\sigma<1/4,\ 0<\delta<.1,\ J=[a,b]\Subset(0,1)\). Set \(L=\log P\), \(D_P=P^{1/2}e^{-L^{3/5}}\), \(z=e^{L^{.24}}\), \(y=e^{L^\delta}\), and \(\kappa_z=\prod_{\ell\le z}(1-1/\ell)\asymp L^{-.24}\). Use \(W(p,k)=1_{pk\in PJ}\log(pk)/L\). The full true prime slope range is \(P^\sigma<p\le D_P\). For a real arithmetic function \(g\), put
\[
 A_{P,g,C}(k)=\sum_{p\ \mathrm{in\ that\ range}}W(p,k)C(P,pk)R_y(P-pk)g(P-pk),\qquad
 Q_{P,g,C}=\sum_k kR_z(k)|A_{P,g,C}(k)|^2 .
\]
Take an undefined term as zero. Here \(C=1\) or the actual translated first-cover indicator \(C_{>1}\) with a fixed \(M\ge400\) in the [translated-marker note](G23ActualMarkedAverageDispersion.md). The sought pointwise bound on \(Q_{P,\lambda,1}\) is \(o(P^2 V_y(P)^2/(\kappa_z L^5))\), where \(V_y(P)=\prod_{\ell\le y,\ell\nmid P}(1-1/(\ell-1))\). On \(P=2^j\), \(V_y(P)\asymp L^{-\delta}\).

There exists one completely multiplicative \(f:\mathbb N\to\{-1,1\}\) with all of the following properties.

* For every fixed \(A>0\), its true one-function Fourier estimate, uniformly in real \(\alpha\), rough cutoff \(u\ge1\) and prefix \(0\le t\le X\), is
\[
 \sup_{\alpha,u,t}\left|\sum_{n\le t} f(n)R_u(n)e(n\alpha)\right|\ll_A X(\log X)^{-A}.
 \tag{1}
\]
* The corresponding **uncentered** one-function progression bound is
\[
 \sum_{q\le\sqrt X}\max_{a\bmod q}\sup_{u\ge1,\,0\le t\le X}
 \left|\sum_{\substack{n\le t\\n\equiv a\bmod q}}f(n)R_u(n)\right|
 \ll_A X(\log X)^{-A}.
 \tag{2}
\]
In particular (2) gives the centered version, subtracting the mean on reduced residues by the triangle inequality whenever that convention is used. The rough parameter can in fact be any \(u\), because the filter on \([1,X]\) changes at only \(O(X)\) integer thresholds. Comparison to \(\lambda\) concerns its usual shallow rough cutoffs, not an assertion that actual \(\lambda\) obeys (1)–(2) for rough cutoffs selecting only primes.
* For **every sufficiently large** \(P=2^j\), both \(C=1\) and the actual fixed mark satisfy
\[
 Q_{P,f,C}\gg P^2\kappa_z/L^3 .
 \tag{3}
\]
This exceeds the desired G23 scale by a factor \(\asymp L^{1.52+2\delta}\). The model can be made to agree with \(\lambda\) on any prescribed finite list of primes, but not on the true prime basis as a whole. It neither implies (3) for actual \(\lambda\) nor contradicts the [previously proved ordinary-target average](G23AverageWeightedDispersion.md): a logarithmic number of special targets per initial segment is extremely thin.

## 2. A disjoint genuine prime reservoir at each \(P=2^j\)

Choose a smaller fixed source interval \(J_0=[a',b']\subset J\) of positive length near \(a\), with \(c=1-b'>(1-a)/2\), \(d=1-a'\le1-a\). Then \(cP\le m\le dP\) forces \(m\) to exceed half the maximum allowed full reflected argument \((1-a)P\). The bands \([c2^j,d2^j]\) are disjoint because \(2c>1-a\ge d\); all later bands are above the full reflected maximum for the current \(P\).

Choose \(\alpha_0=.40\), and choose a sufficiently small fixed \(\epsilon\in(0,.01]\) below, with \(\beta_0=\alpha_0+\epsilon\). Let \(\mathcal S_P\) be all true primes \(P^{\alpha_0}<p\le P^{\beta_0}\). For large \(P\) this is a subrange of the original slopes. Put \(h_0=\log(\beta_0/\alpha_0)\), so \(\sum_{p\in\mathcal S_P}(p-1)^{-1}\to h_0>0\).

Count genuine rows
\[
 m\in[cP,dP]\text{ prime},\quad n=P-m=pk,\quad p\in\mathcal S_P,\quad R_z(k)=1 .
 \tag{4}
\]
The total of (4), with multiplicity in \(p\), is
\[
 (d-c+o(1))\,\frac{P}{L}\,V_z(P)
       \sum_{p\in\mathcal S_P}\frac1{p-1},
 \qquad
 V_z(P)=\prod_{\substack{\ell\le z\\\ell>2}}\left(1-\frac1{\ell-1}\right)\asymp\kappa_z .
 \tag{5}
\]
Indeed \(m\equiv P\bmod p\), a reduced progression. Since \(P=2^j\) and \(m,p\) are odd, \(k\) is odd automatically. For each odd \(\ell\le z\), the event \(\ell\mid k\) further requires exactly \(m\equiv P\bmod p\ell\), reduced. Open retained squarefree products \(e\) of these primes through depth \(\lfloor L^{.1}\rfloor\) and one more using upper/lower Bonferroni. The model factor in this one true prime variable is \(1/\varphi(pe)=(p-1)^{-1}\prod_{\ell\mid e}(\ell-1)^{-1}\). Truncating this model costs arbitrary log saving since its reciprocal sum is \(O(\log L)\); the first omitted factorial shell is smaller than any \(L^{-A}\). The actual moduli \(pe\le P^{.41+o(1)}\) are all distinct as \(p,e\) vary, since \(p>P^{.4}\) and each \(\ell\mid e\) is \(\le z\). The ordinary maximal [prime Bombieri–Vinogradov theorem](https://www.cambridge.org/core/journals/mathematika/article/abs/on-the-large-sieve/4AE92826645F6F3393D30AF0D2767346) at actual endpoints \(cP,dP\), followed by partial summation to unweighted prime counts, pays the full summed error to arbitrary log powers. The remaining integral \(\int_{cP}^{dP}dt/\log t=(d-c+O(1/L))P/L\) gives (5).

Remove rows in which \(k\) contains any slope prime \(r\in\mathcal S_P\), allowing \(r=p\) in the upper bill. For fixed \(p,r\) write \(k=r t\). Then \(R_z(t)=1\), \(m=P-prt\) is prime, and \(t\) lies in an actual interval of length \((d-c)P/(pr)\) in a fixed interior polynomial range. A direct one-prime and one-rough Selberg upper bound gives
\[
 \#\{t\text{ in that interval}:m=P-prt\text{ prime},\ R_z(t)\}
 \ll \frac{(d-c)P}{pr}\frac{\kappa_z}{L}+P^{.04+o(1)}
 \tag{6}
\]
with constant uniform in \(p,r,\epsilon\le.01\). Here are the explicit parameters and justification. Use divisor level \(R=P^{1/100}\) and sieve prime cutoff \(W_0=P^\theta\) for one sufficiently small fixed \(\theta>0\). All sieve primes are units in \(pr\) and \(W_0>z\). At odd \(\ell\le z\), the two distinct excluded roots are \(0\) and \(P(pr)^{-1}\); at 2 those coincide; at \(z<\ell\le W_0\) only the latter is excluded. A genuine prime \(m\asymp P\) survives \(W_0\). The local counts \(\nu_\ell\) are 1 or 2; CRT yields exactly \(\nu(d')=\prod_{\ell\mid d'}\nu_\ell\) bad residues for a squarefree index \(d'\), with an error \(O(\nu(d'))\) from the real \(t\)-interval.

For completeness let \(g_0(\ell)=\nu_\ell/\ell\), \(g(\ell)=g_0(\ell)/(1-g_0(\ell))\), extended squarefreely to the sieve primes. The Selberg denominator \(G(R)=\sum_{s\le R}g(s)\) satisfies \(G(R)\gg\prod_{\ell\le W_0}(1-g_0(\ell))^{-1}\): in the full normalized squarefree divisor product the expected log-divisor is \(\sum g_0(\ell)\log\ell\ll\log W_0\), and choose \(\theta\) so that Markov puts half the mass below \(R\). The optimum weights \(\ell_s\), supported on \(s\le R\), are obtained by diagonalizing the main square \(\sum_{s,t}\ell_s\ell_t g_0([s,t])=\sum_r g(r)^{-1}(\sum_{s:r\mid s}\ell_s g_0(s))^2\); the diagonal variables at the optimum are \(\mu(r)g(r)/G(R)\), which impose \(\ell_1=1\). Inversion gives \(|\ell_s|\le\prod_{\ell\mid s}(1-g_0(\ell))^{-1}\le L^{O(1)}\). The square is 1 on survivors. Summing residual floors over ordered \(s,t\le R\) uses \(\nu([s,t])\le[s,t]\le R^2\) and costs \(R^4 L^{O(1)}\). This produces (6) since
\[
 \prod_{\ell\le W_0}(1-g_0(\ell))
 =\left(\prod_{\ell\le W_0}(1-1/\ell)\right)
   \left(\prod_{3\le\ell\le z}(1-1/(\ell-1))\right)
 \asymp \kappa_z/L.
\]
All parameter choices in (6) precede the choice of angular width.

Sum (6) over \(p,r\in\mathcal S_P\). Its main is \(O((d-c) P\kappa_z h_0^2/L)\). The floors sum to at most \(P^{.86+o(1)}\). Since (5) has main \(\gg (d-c)P\kappa_z h_0/L\) with a fixed lower constant independent of \(\epsilon\), choose \(h_0>0\) small enough that this deletion keeps a fixed fraction. The remaining \(m\) is uniquely owned by a real \(k\): the corresponding \(n=P-m\) has exactly one prime in \(\mathcal S_P\), occurring to exponent 1. We may also discard every row with \(C(P,n)=0\). By the [true integer simultaneous rough and translated-marker bound](G23ActualMarkedAverageDispersion.md) this costs at most \(O_\sigma(P\kappa_z V_y(P)L^{-M/200}+P L^{-A})\), because \(R_z(k)=R_z(n)\) and each \(n\) has at most \(1/\sigma\) candidate true slopes. For \(M\ge400\) it is \(o(P\kappa_z/L)\). This uses the actual first-cover indicator, not a model independence of prime occurrence.

Create one cluster \(\mathscr C_{P,k}\) of all selected prime complements \(m\) owned by the same \(k\), dropping empties. It has size \(O(P^{\beta_0})\) because each true \(p\in\mathcal S_P\) can contribute only its actual \(m=P-pk\). Let \(T_{P,k}=\#\mathscr C_{P,k}\). We have proved
\[
 \sum_k T_{P,k}\gg P\kappa_z/L,\qquad
 \sum_k kR_z(k)T_{P,k}^2\gg P^2\kappa_z/L^3 .
 \tag{7}
\]
For the second inequality use Cauchy and \(\sum_{k\ \mathrm{in\ scope}}R_z(k)/k\ll\kappa_z L\). The latter follows from the ordinary integer rough sieve on all dyadic \(k\)-intervals at these polynomial scales: the same Bonferroni truncation on primes \(\le z\) gives the Mertens product as density, arbitrary log small model error and \(P^{o(1)}\) total floors in each interval. Here all selected \(k\) have \(R_z(k)=1\).

## 3. Complete multiplicativity and large energy at every selected scale

Group the actual primes in all these pairwise disjoint clusters for all sufficiently large \(P=2^j\). Every other prime is a singleton. Give each class an independent fair sign \(\xi_{\mathscr C}\). For each prime \(p\) in the class set \(f(p)=\xi_{\mathscr C}\) and extend by complete multiplicativity. Finite prescribed prime signs may instead be fixed up front, since no large cluster includes them.

Fix a scale \(P=2^j\) and condition on every sign except those belonging to its own clusters. Every current clustered prime exceeds \((1-a)P/2\). Thus it cannot divide any allowed reflected \(m\le(1-a)P\) unless \(m\) is equal to that very prime. In particular a current sign never appears in a composite value of this argument. Later clustered primes are larger than \((1-a)P\) as well. This physically separates scales; it does not use probabilistic independence between actual prime occurrences. In each actual full-slope row \(k\), after the conditioning,
\[
 A_{P,f,C}(k)=Z_k+\sum_h B_{k,h}\xi_{\mathscr C_{P,h}},
 \qquad B_{k,h}\ge0,\quad B_{k,k}\ge\tfrac12 T_{P,k}.
\]
Other genuine slope representations of a selected \(m\) are allowed to contribute to off-diagonal \(B_{k,h}\). We do not need them to vanish. The positivity follows from every true coefficient \(WCR_y\ge0\), and on the specifically planted rows \(C=1,\ R_y=1,\ \log(pk)/L\ge1/2\). Conditional independence and mean zero therefore give
\[
 \mathbb E[Q_{P,f,C}\mid \mathrm{outside}]
 =\sum_k kR_z(k)\bigl(Z_k^2+\sum_h B_{k,h}^2\bigr)
 \gg P^2\kappa_z/L^3 .
\]
The bound holds also for \(C=1\), using the same actual marked clusters.

Changing one current class sign changes at most \(O_\sigma(\#\mathscr C)\) occurrences across all rows: each genuine \(m\) can occur at most once per slope \(p>P^\sigma\) dividing \(P-m\), and there are at most \(1/\sigma\) such slopes. Each occurrence changes the weighted square by a combined bound \(O_J(P)\); indeed the size of the original \(A(k)\) is at most \(O_J(P/k)\), and changing \(s\) terms in that row changes it by at most \(2s\), with both row values bounded by \(O_J(P/k)\). Thus the per-class bounded difference is \(O_{\sigma,J}(P\#\mathscr C)\). The sum of its squares is \(O(P^{3+\beta_0})\), since cluster maxima are \(O(P^{\beta_0})\) and their total size is \(O(P)\). Bounded differences gives failure probability for (3), at most
\[
  \exp(-c P^{1-\beta_0}\kappa_z^2/L^6)
\]
after reducing the lower bound by a fixed factor. This bound is uniform in the conditioning and summable over \(P=2^j\), both marked and unmarked. By Borel–Cantelli almost every resulting single \(f\) obeys (3) at every sufficiently large power of 2.

## 4. Genuine one-function Fourier and arithmetic progression tests for the same \(f\)

Work first at every dyadic analytical scale \(X\), unrelated to the target used when forming a particular cluster, put \(L_X=\log X\), \(\mathcal T=e^{L_X^{1/3}}\), and condition on signs of classes whose smallest prime is \(\le\mathcal T\). In any nonsingleton class all its primes lie in some \([cP,dP]\), so every prime in the conditioned classes is \(\le (d/c)\mathcal T\). Conditional expectation of \(f(n)\) is zero unless each remaining class contributes even total multiplicity among prime factors of \(n\). Therefore its nonzero conditional mean is supported on a deterministic set \(E_X\subset[1,X]\) contained in the union of:

1. \((d/c)\mathcal T\)-smooth \(n\);
2. \(n\) divisible by \(p^2\) for a prime \(p>\mathcal T\);
3. \(n\) divisible by two distinct primes in the same unconditioned class.

For 1 take Rankin exponent \(1-1/\log((d/c)\mathcal T)\) and use Mertens to bound the Euler product by \((\log\mathcal T)^{O(1)}\), giving \(X\exp(-c L_X^{2/3})\). For 2 sum \(X/p^2\) to get \(O(X/\mathcal T)\). For 3 a clustered scale \(P\gg\mathcal T\) contributes at most \(O(P^{\beta_0-1})\) to the total reciprocal pair mass: use
\(\sum_\mathscr C(\#\mathscr C)^2/P^2\ll P^{\beta_0-1}\).
The dyadic scale sum is \(O(\mathcal T^{-(1-\beta_0)})\), and multiplication by \(X\) bounds all true floors. Thus
\[
 |E_X|\ll X\exp(-cL_X^{1/3}).
 \tag{8}
\]
The same exceptional support controls the conditional means multiplied by any deterministic prefix, additive phase, or rough test.

For the AP contribution of this exceptional support, let \(b(n)=1_{E_X}(n)\). Decompose each AP indicator into additive characters modulo \(q\). Thus the maximum over all residues of its mass is at most \(\frac1q\sum_{h\bmod q}|\widehat b(h/q)|\). The zero modes total \(O(|E_X|\log X)\). On grouping every nonzero \(h/q\) by its reduced denominator \(r\) the coefficient sum is \(\sum_{q\le\sqrt X,\ r\mid q}q^{-1}\ll (\log X)/r\). By Cauchy, \(\sum_{r\le\sqrt X}\varphi(r)/r^2\ll\log X\), and the [additive large sieve](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf) for distinct reduced fractions at denominators at most \(\sqrt X\), the total is
\[
 \ll |E_X|\log X+(\log X)^{3/2}\sqrt{X|E_X|}.
 \tag{9}
\]
Because \(b\ge0\), any actual AP prefix and every rough mask give no greater absolute conditional-mean count than that full AP. Thus no endpoint union loss for (9).

For fluctuations, fix a reduced AP modulo \(q\le\sqrt X\), an endpoint \(t\le X\), and a rough cutoff \(u\). For one independent high class let \(d_{\mathscr C}\) be twice the number of progression points \(n\le X\) divisible by a prime in the class; this bounds the actual coefficient change. For each such prime \(p\) the number is at most \(X/(qp)+1\) by CRT, since \(p\mid q\) would forbid it from any reduced progression instead. For a nonsingleton class with size \(\ll P^{\beta_0}\) and all primes \(\asymp P\ge c'\mathcal T\), the reciprocal class mass is \(O(\mathcal T^{-(1-\beta_0)})\). The same bound holds for a high singleton; nonsingletons relevant to \(n\le X\) have \(P\ll X\). Therefore
\[
 \max_\mathscr C d_\mathscr C\ll \frac{X}{q\mathcal T^{1-\beta_0}}+X^{\beta_0},\qquad
 \sum_\mathscr C d_\mathscr C\ll (X/q)\log X.
\]
For the second inequality each actual progression point is counted by at most \(\log X/\log 2\) classes. The squared-difference sum is bounded by the product of these two bounds. Thus bounded differences in this larger conditional probability space gives failure probability \(O(X^{-C_1})\), for arbitrarily large fixed \(C_1\) by increasing the constant, for the following threshold around the conditional mean:
\[
 O_{C_1}\left(L_X\left(\frac{X}{q\mathcal T^{(1-\beta_0)/2}}
                    +\frac{X^{(1+\beta_0)/2}}{\sqrt q}\right)\right).
 \tag{10}
\]
Apply to all actual integer endpoints, rough cutoff thresholds and all reduced progressions (only polynomially many objects up to \(X\)); the bound is independent of the conditioned signs. Summing (10) over \(q\le\sqrt X\) gives
\[
 O\left(X L_X^2\mathcal T^{-(1-\beta_0)/2}+L_X X^{3/4+\beta_0/2}\right),
\]
where \(3/4+\beta_0/2<1\). The uncentered BV bound for reduced AP follows from (8)–(10), simultaneously at all sufficiently large dyadic \(X\) by Borel–Cantelli. To include nonreduced progressions, write \(d'=(a,q)\), \(q=d'r\), \(n=d'v\). Use \(f(n)R_u(n)=f(d')R_u(d')f(v)R_u(v)\) and sum the reduced bound at scale \(X/d'\) for \(r\le\sqrt X/d'\le\sqrt{X/d'}\), over \(d'\le\sqrt X\); this loses only a logarithm, absorbed by arbitrary saving. A dyadic upper scale \(X'\in[X,2X]\) and uniform real endpoints yield the claimed bound for all \(X\).

For (1) take \(q=1\) in the same fluctuation proof but use real and imaginary parts after a prescribed additive phase. A grid of \(O(X^3)\) phases, all \(O(X^2)\) endpoint and rough cutoffs, and the same union bound and Borel–Cantelli suffice: the derivative in \(\alpha\) is \(O(X^2)\), so grid error is \(O(1/X)\). The conditional mean absolute bound at all these frequencies is \(|E_X|\). This proves (1) and (2) on one probability-one event, independently of the probability-one condition (3). Choose one deterministic outcome in their intersection.

## 5. A concrete necessary cancellation for actual \(\lambda\)

Even without the surrogate, (5) or the positive subreservoir (7) implies a true lower bound at every sufficiently large \(P=2^j\). Write
\[
 B_P(k)=\sum_{p}W(p,k)C(P,pk)1_{\{P-pk\ \mathrm{prime}\}},\qquad
 H_P(k)=\sum_p W(p,k)C(P,pk)R_y(P-pk)\lambda(P-pk)1_{\{P-pk\ \mathrm{composite}\}} .
\]
The full positive prime-reflected layer satisfies \(\|B_P\|_{kR_z}^2\gg P^2\kappa_z/L^3\) even for the genuine \(C\). These are real primes (not assumed prime pairs asymptotics). Since \(\lambda(m)=-1\) for every true prime, the true signed vector is exactly \(H_P-B_P\) (the reflected variable is \(\asymp_J P\), so no \(m=1\)). If the sought G23 pointwise energy bound holds, Cauchy implies
\[
 \langle B_P,H_P\rangle_{kR_z}
 =\|B_P\|_{kR_z}^2+
 o\!\left(\|B_P\|_{kR_z}^2\right),
\]
because the ratio of the required \(\|H_P-B_P\|^2\) bound to the lower bound on \(\|B_P\|^2\) tends to zero. In particular, the genuinely signed composite rough layer must cancel the entire primal bias **in the same \(k\)-weighted test**, not just in a separate unsigned main term at a similar scale. This is a fixed-target, nonnegative true prime-reflected test vector giving a concrete necessary high-composite compensation. The remaining input is an estimate for the joint prime/composite slope correlation (including \(p\ne p'\)), not any deduction from complete multiplicativity alone, (1)–(2), or the ordinary-target average.