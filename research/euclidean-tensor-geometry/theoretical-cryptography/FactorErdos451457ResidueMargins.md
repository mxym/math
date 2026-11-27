# Missing primes in logarithmic products: a counting law and a residue-marginal barrier

For integers $n,k\ge 1$, let $q(n,k)$ be the least prime that does not divide $(n+1)\cdots(n+k)$. A prime $p>k$ divides this product on exactly $k$ residue classes for $n$ modulo $p$; all primes $p\le k$ always divide it. The closely related [Erdős #451](https://www.erdosproblems.com/451) asks for the earliest block that has the opposite behavior at every prime $k<p<2k$: none of these primes divides the block.

Two distinctions are useful: the full-period density need not give the density in a much shorter prescribed interval, and independence of every proper subcollection of residue coordinates need not even imply a positive full-intersection probability.

## 1. A blockwise counting law beyond the full CRT period

Put $I_k=\{n\in\mathbb Z:e^k\le n<e^{k+1}\}$, so $k=\lfloor\log n\rfloor$ for every $n\in I_k$. For every fixed
$$
1<C<1+2\log 2=2.38629\ldots
$$
there exists $\gamma_C>0$ such that, as $k\to\infty$,
$$
\frac{|\{n\in I_k:q(n,k)>Ck\}|}{|I_k|}
=
\left(1+O_C\!\left(e^{-\gamma_Ck/\log k}\right)\right)
\prod_{k<p\le Ck}\frac{k}{p}.
\tag{1}
$$
In particular the logarithm of the proportion is
$$
-\bigl(C\log C-C+1+o(1)\bigr)\frac{k}{\log k}.
\tag{2}
$$
For $C>2$, the full period has size $\exp((C-1+o(1))k)$, which is exponentially larger than the averaging interval. Equidistribution over the full period alone does not prove (1).

### Proof

For $p>k$ let $X_p$ be the binary indicator that $p$ is missing from the block, and put $a_p=1-k/p$. In the independent model the $X_p$ are independent Bernoulli variables with means $a_p$. In the arithmetic law over $I_k$, the model and actual expectations of a monomial $\prod_{p\in S}X_p$ differ by at most
$$
\frac{\prod_{p\in S}(p-k)}{|I_k|}\le \frac{(Ck)^{|S|}}{|I_k|}.
\tag{3}
$$
Indeed, the CRT gives exactly $\prod_{p\in S}(p-k)$ residue classes for the event; each residue class contributes with rounding error at most one. We use (3) only for sufficiently low-degree polynomials, rather than summing over a period containing all the primes.

Split the primes into $A=\{k<p\le \min(2,C)k\}$ and $B=\{2k<p\le Ck\}$, and put $G(X)=\prod_{p\in B}(1-X_p)$. Let $T=\sum_{p\in A}X_p$. For a positive integer $d$, define
$$
\begin{aligned}
K_d&=\sum_{\substack{S\subseteq A\\ |S|\le d}}\ \prod_{p\in S}\frac{a_p}{1-a_p},\\
P_d(X)&=\frac1{K_d}\sum_{\substack{S\subseteq A\\ |S|\le d}}
               \ \prod_{p\in S}\frac{a_p-X_p}{1-a_p}.
\end{aligned}
$$
Thus $P_d(0)=1$. The centered one-coordinate factors in the numerator have model second moments $a_p/(1-a_p)$, and their distinct products are orthogonal. Writing $\mathbf E_*$ and $\mathbb P_*$ for the independent model,
$$
\mathbf E_*P_d^2=\frac1{K_d},\qquad
K_d=D_A^{-1}\mathbb P_*(T\le d),\qquad
D_A=\prod_{p\in A}(1-a_p).
\tag{4}
$$
The second identity follows by expanding the Bernoulli probabilities of the different failure sets $S$. This is the degree-$d$ Selberg quadratic kernel in a centered Bernoulli basis.

Pointwise on the binary cube we have
$$
G(1-T)P_d^2\ \le\ \mathbf 1_{\{X_p=0\text{ for all }k<p\le Ck\}}\ \le\ GP_d^2.
\tag{5}
$$
At $T=0$ both sides equal $G$; otherwise $1-T\le0$. The upper expectation in the model is $D_B/K_d$ with $D_B=\prod_{p\in B}(1-a_p)$. The lower model expectation is at least
$$
D_B\{D_A-|A|(1/K_d-D_A)\}
$$
because $P_d(0)=1$ and the magnitude of the lower polynomial's negative factor on $T\ge1$ is at most $|A|$.

Let $h=k/\log k$, $a=\min(2,C)$, and $u=a-1-\log a$. By the ordinary prime number theorem applied to continuous weights of $p/k$,
$$
\mathbf E_*T=(u+o(1))h,\qquad |B|=((C-2)_++o(1))h.
$$
Take $d=\lfloor(u+\delta)h\rfloor$ with fixed sufficiently small $\delta>0$. For instance, the exponential-moment bound for Bernoulli sums gives
$$
\mathbb P_*(T>d)\le \exp(-\eta_C h)
$$
for some $\eta_C>0$, since $\mathbf E_*e^{tT}\le \exp((e^t-1)\mathbf E_*T)$ and one may choose a small fixed $t>0$. Thus the model expectations of both sides of (5) sandwich $D_AD_B$ to relative error $O(e^{-\eta_C h/2})$.

The larger of the polynomial degrees in (5) is at most $|B|+2d+1$. Indeed $P_d$ has degree at most $d$; reducing powers of binary variables does not increase degree or the sum of absolute coefficients. The usable degree budget is $(1-\kappa)h$ for some $\kappa>0$. The condition
$$
(C-2)_+ + 2u < 1
$$
guarantees this budget for small $\delta$. When $C\le2$ we have $2u\le 2(1-\log 2)<1$. When $C>2$, the left side is $C-2\log 2$, which explains the asserted range.

For the rounding cost, the absolute coefficient sum of $P_d$ is bounded by
$$
\prod_{p\in A}\left(1+\frac{a_p+1}{1-a_p}\right)
\le (2C)^{|A|},
$$
using $K_d\ge1$. The other factors in (5) cost at most $2^{|B|}(1+|A|)$. Hence (3) transfers each expectation with absolute error at most $\exp(-\kappa' k)$ for some $\kappa'>0$. The product $D_AD_B$ is $\exp(-O_C(h))$, and the rounding error is negligible even compared with the relative model error. This proves (1); partial summation gives (2).

The same proof works in any interval of at least $\exp((s(C)+\epsilon)k)$ consecutive integers for fixed $\epsilon>0$, where $s(C)=(C-2)_++2u$. Simply use its length in (3) and take $\delta$ less than $\epsilon/4$. Also (2) is unchanged if one asks for $q(n,k)>C\log n$ on $I_k$: sandwich this event between cutoffs $Ck$ and $Ck+C$. The proof of (1) is uniform for those two cutoffs, and their products differ by bounded factors because the cutoff moves through only $O_C(1)$ integers.

## 2. Typical missing primes: a Poisson process in hazard coordinates

For each prime $p>k$, put $H_k(p)=\sum_{k<\ell\le p,\ \ell\text{ prime}}\log(\ell/k)$. For $n$ uniform in $I_k$, place a point at $H_k(p)$ whenever $p$ is missing. This process converges on bounded hazard intervals to the rate-one Poisson point process: counts in finitely many disjoint intervals of fixed lengths converge jointly to independent Poisson variables with those means. In particular $H_k(q(n,k))$ converges to $\operatorname{Exp}(1)$ as $k\to\infty$ through **all** integers.

Fix an upper hazard cutoff $U<\infty$. For any $\epsilon>0$, the primes in $((1+\epsilon/2)k,(1+\epsilon)k]$ alone contribute $\gg_\epsilon k/\log k$ to the hazard, by the ordinary prime number theorem. Thus all primes involved up to $U$, including the first prime that crosses $U$, lie in $(k,(1+o(1))k]$. The log of their product is $o(k)$ by the same theorem. Consequently the actual joint law over $I_k$ differs in total variation from the full CRT product law by $\exp(-k+o(k))$. The maximal hazard increment is $o(1)$, and $a_p=1-\exp(-\log(p/k))=\log(p/k)+O(\log(p/k)^2)$. In each fixed hazard bin the $a_p$ therefore sum to its length plus $o(1)$, and their squares sum to $o(1)$. The product of their Bernoulli generating functions gives the claimed Poisson limits, jointly by independence on disjoint bins.

One can also recover a familiar scale for a set of $k$ of natural density one:
$$
\mathbb P_{n\in I_k}\bigl(q(n,k)>k+t\sqrt{k\log k}\bigr)\longrightarrow e^{-t^2/2}
\qquad (t\ge0\text{ fixed}).
\tag{6}
$$
To justify the additional almost-all step, use [Guth–Maynard, Corollary 1.4](https://arxiv.org/html/2405.20552#S1) on a dyadic $k$-block $[K,2K]$. Test lengths on an integer grid of mesh $\sqrt{K\log K}/\log K$ up to a fixed multiple of $\sqrt{K\log K}$. Their union of exceptional sets is $O(K\log K\exp(-c(\log K)^{1/4}))$. Monotonicity between grid points then gives $\pi(k+w\sqrt{k\log k})-\pi(k)=(w+o(1))\sqrt{k/\log k}$, uniformly for bounded $w$ on the good starts. Partial summation gives the hazard limit $t^2/2$. For example, if $A(v)=\pi(k+v)-\pi(k)$, then the first-order hazard approximation is
$$
k^{-1}\left(t\sqrt{k\log k}\,A(t\sqrt{k\log k})
         -\int_0^{t\sqrt{k\log k}}A(v)\,dv\right)\to t^2/2;
$$
the sum of the second-order terms in $\log(p/k)$ is $o(1)$. The product law gives (6). The almost-all claim in (6) is about the block label $k$, not a natural-density assertion over all $n$.

## 3. Exact obstruction for #451: even all proper residue marginals may be insufficient

There is a sharp finite statement. Let $m\ge2$, and let coordinate $i$ have a finite uniform space with a nonempty allowed subset occupying fraction $t_i\in(0,1)$. There exists a joint probability measure under which every proper subset of the **full coordinates** is independently uniform, yet all coordinates are never simultaneously allowed, if and only if the largest two $t_i$ sum to at most one.

To prove this, encode a failure by $1$ and let $\mu(S)=D\prod_{i\in S}(1-t_i)/t_i$ be the product-model mass of the binary cell with failure set $S$, where $D=\prod_i t_i$. If all proper marginals are fixed, subtracting the independent model leaves a signed mass whose values on the two cells differing in any one bit sum to zero. Therefore the signed difference is necessarily $c(-1)^{|S|}$. Conversely this perturbation has zero proper marginals, and it is nonnegative after addition to $\mu$ exactly for
$$
-\min_{|S|\ {\rm even}}\mu(S)\ \le c\le\
 \min_{|S|\ {\rm odd}}\mu(S).
\tag{7}
$$
The all-allowed cell can be killed exactly when $\mu(S)\ge D$ for every even $S$. Write $w_i=(1-t_i)/t_i$. The condition is equivalent to the product of the smallest two $w_i$ being at least one: necessity uses that pair, and sufficiency follows by pairing any even nonempty subset. This is exactly the asserted inequality for the largest two $t_i$. Finally, conditional on each binary cell, choose the full coordinates independently and uniformly within their indicated allowed or forbidden sets. This lifts the binary perturbation to the full coordinates while preserving all their proper marginals.

For #451, with endpoint $n$ and block $(n-k)\cdots(n-1)$, the allowed residues for each prime $k<p<2k$ are $0,k+1,\ldots,p-1$, so $t_p=(p-k)/p<1/2$. For all sufficiently large $k$ there are at least two such primes. Thus **even exact joint uniformity modulo every proper subproduct of the primes' moduli cannot on its own force an admissible endpoint in a modeled interval**. The result is a statement about what the specified marginals imply; the constructed measure need not come from consecutive integers. It does not disprove the conjectured subexponential bound and does not preclude a proof using additional arithmetic structure.

## Scope and checks

- [Erdős, *Some unconventional problems in number theory* (1979), pp. 77–78](https://www.renyi.hu/~p_erdos/1979-23.pdf) and [Erdős #457](https://www.erdosproblems.com/457) concern the least missing prime. The infinitude result in #457 already has [a public proof and formalization](https://google-deepmind.github.io/formal-conjectures/src/FormalConjectures/ErdosProblems/%C2%AB457%C2%BB/), and the [#457 discussion](https://www.erdosproblems.com/forum/thread/457) gives a different method with larger extreme thresholds on an infinite subsequence. The contribution of (1) is the rare-event frequency in **every** logarithmic block, not a record for the largest value of $q(n,\lfloor\log n\rfloor)$.
- [Van Doorn and Tang, *Consecutive integers free of certain prime factors*](https://arxiv.org/abs/2606.19863) prove a superpolynomial lower bound for the first admissible endpoint in #451. Section 3 above proves a limitation of a residue-marginal argument; it supplies neither a new first-endpoint lower bound nor the sought subexponential upper bound.
- The [fixed exact checker](verify_factor_erdos451457_residue_margins.js) audits the finite quadratic-kernel formulas, both pointwise polynomial signs, CRT rounding on actual toy intervals, and the parity-perturbation endpoints. It runs 121,371 exact assertions, including the full proper marginals of two toy residue boxes.
