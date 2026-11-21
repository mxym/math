# A rank-uniform two-scale marker and its actual large negative mass

Let $P$ tend to infinity through even integers, $L=\log P$, $m=P-n$, $F=nm$, and sum with weight $W(n/P)\mu^2(F)$, where $W$ is a fixed nonnegative, nonzero smooth function supported in $(1/3,2/3)$. Write $\langle H\rangle$ for this **actual** weighted sum, $X=P\int W$, and $\mathfrak S(P)$ for the ordinary Goldbach singular series. No averaging over targets is used. The leading terms below are on this very same squarefree probability space, not obtained by treating the two physical integers as independent.

Put $C=L^{1/4}$, $\lambda=(\log L)^2$, $T=\log C$, and let the marks $\ell$ be all primes in $[e^{\sqrt L},\sqrt P]$ not dividing $P$. Define
$$
 t_\ell=\frac{\log\ell}{L},\quad s_\ell=\frac{\lambda}{\log\ell},\qquad
 B_v(F)=\prod_{p\mid F}(1-p^{-v})\quad (v>0).
$$
For $p\nmid P$ put $b_p=2/p-2/p^2$, $a_p=1-2/p$, and $g_p(v)=a_p+b_p(1-p^{-v})$. At $p\mid P$ put $g_p(v)=1-1/p$. Set
$$
 U_\ell(v)=b_\ell(1-\ell^{-v})\prod_{p\ne\ell}g_p(v),\qquad
 c_\ell=U_\ell(s_\ell)/U_\ell(Cs_\ell).
$$
These convergent positive Euler products encode the squarefree, target-unit distribution, not an exact finite-$P$ physical expectation. In particular $0<c_\ell\le1$. Consider the two nonnegative **whole-population** weights
$$
 A=L^2\sum_{\ell\mid F}t_\ell^3 B_{s_\ell}(F),\qquad
 D=L^2\sum_{\ell\mid F}t_\ell^3 c_\ell B_{Cs_\ell}(F),\qquad J=A-D
$$
(the sums retain only the indicated marks). Define the single observable
$$
 u=\frac{T^2 L}{C\lambda},\qquad v=\frac{L}{\lambda T^4},\qquad
 N_I(F)=\#\{p\mid F:\ u\le\log p\le v\},\qquad
 m_I=2\log(v/u)=2\log C-12\log\log C.
$$

**Theorem.** For each fixed $E$ one has $\langle J\rangle=O_E(PL^{-E})$. If $Z=X\mathfrak S(P)\lambda^2$, then
$$
 \langle A\rangle\sim\langle D\rangle\sim
 \langle J_+\rangle\sim\langle J_-\rangle\sim Z,
$$
where $J_-=\max(-J,0)$ is taken **after** summing all prime marks. All but $o(Z)$ of the mass of $J_+$ is on $N_I=0$, and all but $o(Z)$ of that of $J_-$ is on $|N_I-m_I|\le T^{3/4}$. Thus the mass that pays for this zero-mean marker lives at a genuinely growing number of explicitly ranged subpower prime factors; it is bigger, by a diverging factor, than the natural Goldbach scale.

There is nevertheless a rank-independent pointwise estimate. On every squarefree composite-pair alternative (at least one leg composite) whose least factor $q$ satisfies $q\ge e^{\sqrt L}$,
$$
  J/L^2\ \geq\ (\log q/L)^3(1-O(Le^{-\lambda}))-O(C^{-2}).
$$
In particular $J>0$ on every such row with $\log q\ge L^{5/6+\epsilon}$ for any fixed $\epsilon>0$ and sufficiently large $P$. The true prime pairs have no marks. The uniform pointwise lower bound does **not** imply that the negative part is negligible; the unconditional asymptotic above proves precisely the opposite.

## Actual CRT sums, including factorial moments

We give the reduction for zero, one and two additional **distinct ordered** prime marks $p_1,\ldots,p_j$ from $I$. The last two cases are used only with $t_\ell\ge1/T$. These extra primes are smaller than $\ell$ there, and any prime dividing $P$ is omitted (impossible on the squarefree rows). Allow any bounded coefficient depending on the distinguished labels, including $c_\ell$. For each such tuple let $R$ be its set of $1+j$ labels; distinguish the original $\ell$, and let $\sigma=s_\ell$ or $Cs_\ell$. Then the weighted physical sum, summed over the labels, equals the corresponding sum of $X$ times
$$
 U_\ell(\sigma)\prod_{i=1}^j
       \frac{b_{p_i}(1-p_i^{-\sigma})}{g_{p_i}(\sigma)}
 \tag{1}
$$
with the same coefficients, up to $O_E(PL^{-E})$ for every fixed $E$. This is an **aggregated absolute discrepancy bound for these sums** (uniform in the bounded label multipliers), not a relative pointwise independence statement for individual $F$. Powers of $L$ in the two outer weights may be restored by increasing $E$.

Here are details. On a marked input satisfying $\mu^2(F)=1$, remove the known factors $\prod_{r\in R}(1-r^{-\sigma})$ from $B_\sigma$ and expand the rest as $\sum_{d\mid F,(d,R)=1}\mu(d)d^{-\sigma}$. Truncate at $d\le\ell^{1/4}$. The omitted absolute tail per tuple is at most $\tau(F)e^{-\lambda/4}$. This is **not** uniformly small pointwise times an arbitrary divisor count. In the physical sum the number of eligible marked tuples is at most $\omega(F)^3+\omega(F)^2+\omega(F)$, so Cauchy and the ordinary fixed moments of $\tau(n),\tau(P-n)$ give total error $P L^{O(1)}e^{-\lambda/4}=O_E(PL^{-E})$. This controls both values of $\sigma$.

For the remaining labels open the unit constraint $(P,n)=1$ and the two squarefree constraints $k^2\mid n$, $j'^2\mid P-n$ with Möbius coefficients, trimming $k,j'\le L^K$. The population with an omitted square divisor is $O(PL^{-K}+\sqrt P)$; use Cauchy and the same fixed divisor moments, including the retained or truncated square-divisor counts and the marked multiplicities. Choose $K$ to absorb the requested log accuracy. Keep $(k j'dR,P)=1$, and reject incompatible systems. Assign each prime of $d$ and $R$ to one of the two root classes of $n(P-n)$. In each compatible CRT class replace the sum of $W$ by its integral density with error $O_W(1)$. The sum of all those errors is at most
$$
 P^{1/2+1/8+o(1)}\,\exp(2v)=P^{5/8+o(1)}:
$$
there are at most $\sqrt P$ choices of $\ell$, at most $P^{1/8}$ untagged divisors, and $\exp(2v)=P^{o(1)}$ additional prime-label choices. All root assignment factors, divisors of $P$ in the unit inclusion-exclusion, and trimmed square labels cost $P^{o(1)}$. The physical cut in $d$ is independent of $n$ after fixing $\ell$; the crude bound covers sharp endpoints.

For the model restoration of $k,j'$ one may use directly the CRT estimate of [the coupled marked-flat calculation](https://github.com/mxym/math/commit/f39f90b2). For clarity: splitting $d=d_1d_2$ across the two roots and writing $c\mid P$ for the unit inclusion-exclusion label, an occupied joint class has density at most
$$
 \frac{(d_1,k)(d_2,j')}{c\, k^2 j'^2\,d_1d_2}
 \prod_{r\in R_1}\frac{(r,k)}r\ \prod_{r\in R_2}\frac{(r,j')}r.
$$
The distinct label sets $R_1,R_2$ are disjoint from $d$. Summing their factors costs $O((1+\log L+\omega(k)+\omega(j'))^3)$, since the reciprocal sum of all available primes is $O(1+\log L)$. Summing the two divisor harmonics costs $L^{O(1)}2^{\omega(k)+\omega(j')}$, and $\sum_{c\mid P}1/c\ll 1+\log L$. The $k^{-2}j'^{-2}$ tails with these divisor weights are $O(L^{-K+O(1)}(1+\log L)^{O(1)})$, so an arbitrarily accurate restoration follows. All constants are uniform in the labels and positive $\sigma$ used here.

After exact model squarefreeness is restored, each $p\nmid P$ has local weights $a_p$ at no root modulo $p$, and $b_p$ at an exactly single prime power of the product (the two distinct roots minus their $p^2$ lifts). Each $p\mid P$ has the unit local factor $1-1/p$. The marks impose the $b_r$ factors. The omitted infinite model tail $d>\ell^{1/4}$ has absolute sum $\ll e^{-\lambda/8}L^{O(1)}$ times $\prod_{r\in R}O(1/r)$: Rankin split $d^{-\sigma}$ in half and bound the absolute remaining series by $\prod_p(1+2p^{-1-\sigma/2})\ll (1+1/\sigma)^2$. This argument can be performed directly on the squarefree CRT density of the tuple and divisor, using the bound $\prod_{r\in R}2/r\prod_{p\mid d}2/p$. Reciprocal summation of the labels and multiplication by $X$ again costs only powers of $L$. The unrestricted local product is (1). This proves the CRT assertion, including exactly the zeroth, first and second factorial moments used below.

## Uniform tag mass and the two distinct populations

Factor $\prod_{p\ne\ell} g_p(w)=\zeta(1+w)^{-2}H_{P,\ell}(1+w)$. At $w=0$ the regular factor is $\mathfrak S(P)/(1-2/\ell)$, by dividing each ordinary $1-2/p$ and each target factor $1-1/p$ by $(1-1/p)^2$, with the missing generic $\ell$ restored by division by $1-2/\ell$. Uniformly on the short real interval $0\le w\le C\lambda/\sqrt L$, its logarithmic derivative is $O(1+\log L)$: the normalized generic factors have logarithmic derivatives summable by $\sum_p O(\log p/p^2)$ (all denominators are bounded below away from 0 for odd $p$), the one missing mark costs $O(\log\ell/\ell)$, and the target-prime factors cost $O(\sum_{p\mid P}\log p/(p-1))\ll1+\log L$ by splitting at $L^2$ and using $\sum_{p\le y}\log p/p\ll\log y$. Hence
$$
 U_\ell(w)=(1+o(1))\frac{b_\ell(1-\ell^{-w})}{1-2/\ell}\,\mathfrak S(P)w^2
 \quad(w=s_\ell,Cs_\ell)
$$
uniformly, and $c_\ell=(1+o(1))C^{-2}$. The signed zeroth moments cancel by the exact defining ratios and (1), not by using this asymptotic in a near-cancellation.

It follows for $A$ or $D$ that its mass is
$$
 (2+o(1))X\mathfrak S(P)\lambda^2
       \sum_{\ell}\frac{\log\ell}{\ell L}=(1+o(1))Z.
$$
Here the elementary weighted prime Mertens estimate gives the limit $1/2$, and the deletion of $\ell\mid P$ above $e^{\sqrt L}$ is negligible by $\sum_{\ell\mid P}\log\ell\le L$. The discarded range $t_\ell<1/T$ contributes $O(Z/T)+o(Z)$ to **each** nonnegative population, by the same calculation on that range. We do not assign any special distribution of $N_I$ to these small original labels.

For the remaining original marks, the probability factors in (1) are denoted by $\pi_p(w)=b_p(1-p^{-w})/g_p(w)$ for the admissible primes, and zero at the target primes. Uniformly, $s_\ell\log p\le T^{-3}$ on $I$, so
$$
 \sum_{p\in I}\pi_p(s_\ell)\ll T^{-3}\sum_{p\in I}1/p=O(T^{-2}).
$$
By the first physical moment in (1), all but $o(Z)$ of $A$ has $N_I=0$. On the other hand $Cs_\ell\log p\ge2T^2$ on $I$ (since $t_\ell\le1/2$). Consequently $\pi_p(Cs_\ell)=2/p+O(e^{-2T^2}/p+1/p^2)$ away from the target primes. Omitting $p\mid P$ costs $O(Le^{-u})$, uniformly. Prime Mertens in $[\exp u,\exp v]$ now gives
$$
 \sum_{p\in I}\pi_p(Cs_\ell)=m_I+o(1).
$$
The two **ordered distinct** marks in (1) give the factorial second moment, so the model variance about its own mean is $\sum\pi_p(1-\pi_p)\ll T$. Apply (1) to $N_I^2=N_I(N_I-1)+N_I$, and then to $(N_I-m_I)^2$; its powers of $m_I$ cost at most powers of $L$ in the absolute CRT error. Thus the nonnegative physical large-mark part of $D$ has centered second moment $O(TZ)$, and all but $o(Z)$ of $D$ has $|N_I-m_I|\le T^{3/4}$ by Chebyshev and the small original mark bound. Eventually this window is disjoint from $N_I=0$. In particular $\langle\min(A,D)\rangle=o(Z)$: bound the minimum by $D$ on the first set and by $A$ on its complement. Subtraction from the two zeroth moments yields both positive/negative-part assertions, with their concentration. No cancellation between different marked primes is neglected.

Finally $0\le B_w\le1$ on each squarefree row, so **each** marked difference is $\ge -c_\ell$. If the least prime $q$ is a retained mark then $B_{s_q}\ge1-\omega(F)e^{-\lambda}$ by the product union bound, and $\omega(F)\ll L$. A squarefree row with a composite leg has its least prime $q\le\sqrt{2P/3}<\sqrt P$. Also $\sum_{\ell\mid F}t_\ell^3\le\sum_{\ell\mid F}t_\ell\le2$. These facts prove the stated rank-uniform lower bound, with no uniform claim anywhere about the pointwise tail of a divisor expansion.

**Interpretation.** This identifies, and prices on each actual target, the many-factor sector that defeats the proposed two-scale correction. It does not estimate the original prime-pair count, eliminate that sector for another detector, or prove that every other attempt at a sign comparison must suffer this loss.
