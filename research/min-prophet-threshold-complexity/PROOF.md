# The price of using only k distinct thresholds for i.i.d. minimum-cost stopping

**Problem.** Livanos and Mehta ask in [SODA 2024, §5](https://par.nsf.gov/servlets/purl/10511091) how the single-choice cost prophet ratio changes if at most $k$ thresholds may be used. We treat every fixed $k\ge1$ for continuous costs with a regularly varying lower quantile, allowing arbitrary slowly varying factors. A threshold is chosen before viewing the current cost, and the first value below it is taken irrevocably. The final draw is compulsory if no earlier draw was accepted; it does not count as a discretionary threshold (as in the source's single-threshold model). The cap counts distinct threshold values, not the number of alternations between them. It may even be imposed path by path, allowing randomized thresholds based on past rejected values. The known nonnegative law has finite positive mean $\mu$, lower endpoint zero and no atoms. Let $H_k(n)$ be the infimum of expected costs in this class and $M_n$ the expected sample minimum.

Write $Q(u)=\inf\{x:F(x)\ge u\}$ for $0<u<1$. Suppose $Q(du)/Q(u)\to d^r$ as $u\downarrow0$ for every fixed $d>0$, with $r\ge0$ (regular variation at zero). Set $b_n=Q(1/n)$, and let $\ell_k(n)$ denote the $k$-fold iterated natural logarithm, used at sufficiently large $n$.

* **Positive index $r>0$.** For every fixed $k$,
  $$
  H_k(n)\sim \frac{Q(r\ell_k(n)/n)}{1+r},\qquad
  \frac{H_k(n)}{M_n}\sim\frac{Q(r\ell_k(n)/n)}{\Gamma(2+r)Q(1/n)}.          \tag{1}
  $$
  In particular $Q(u)\sim c u^r$ gives the ratio $(r\ell_k(n))^r/\Gamma(2+r)$ asymptotically. No pure-power replacement for the quantile ratio is made for general regular variation.
* **Slow variation $r=0$.** Define $v_0(n)=\mu$ and iterate *just $k$ times*:
  $$
  w_j(n)=1+\log^+(v_{j-1}(n)/b_n),\quad
  v_j(n)=Q(w_j(n)/n),\quad 1\le j\le k .
  $$
  Then $H_k(n)\sim v_k(n)$ and $M_n\sim b_n$. This covers all such quantiles, whether or not the ratios at intermediate stages converge. It is not asserted that every slowly varying quantile is in a Gumbel domain, nor is uniformity in growing $k$ claimed.

## Why sorting thresholds loses nothing

A continuous cdf makes a fixed threshold equivalent to a probability $p$ of acceptance; every $p\in(0,1)$ is attainable since $F$ is continuous. The mean on acceptance is $A(p)=p^{-1}\int_0^p Q(u)du$, which is nondecreasing; endpoints can be interpreted as skipping or accepting all (or approximated by finite cutoffs). Ties have probability zero. A single step with given future cost $v$ costs $pA(p)+(1-p)v$. For two successive steps $p,s$ the cost for order $p,s$ minus that for $s,p$ equals $ps(A(p)-A(s))$, independent of $v$. Thus any deterministic schedule can be sorted in nondecreasing order of $p$ and need only use at most $k$ consecutive blocks.

Adaptation to a past *rejected* numerical cost provides no information about future i.i.d. draws. For rigor, produce a random schedule offline along a fictitious all-rejection history. Draw the policy's random seed and, at each threshold, generate an independent sample conditional on rejection to feed to the policy; if rejection has probability zero, repeat the last threshold thereafter. At any prefix in which all rejection probabilities are positive, the real probability of reaching its history weights this fictitious path measure precisely by the product of the preceding rejection probabilities (by successive conditional distributions). The current mean contribution is therefore the schedule's survival product times $pA(p)$; the forced last cost similarly contributes its survival product times $\mu$. Summing and integrating over the fictitious histories reproduces the adaptive policy's expected cost as a mixture of deterministic-schedule costs. Since the product on each reachable prefix is positive, null constraint violations remain null for the fictitious law, for every one of the finitely many prefixes. If a rejection probability is zero, repetition introduces no new threshold. The resulting schedules obey the same $k$ cap almost surely. Conversely deterministic schedules are admissible. Nothing here permits choosing a threshold *after* seeing the current value.

## One block

For integer $N\ge1$ and future expected cost $v$, set
$$
 B_N(v)=\inf_{0\le p\le1}\{A(p)[1-(1-p)^N]+v(1-p)^N\}.
$$
The $p=0$ expression means $v$. The transform is increasing in $v$, decreasing in $N$: cutoffs with $A(p)>v$ cannot improve on skipping. More trials at any remaining cutoff cannot increase its cost. Karamata's integral theorem gives $A(p)\sim Q(p)/(1+r)$. We use the elementary consequences of regular variation: uniform convergence on compact positive multiplier intervals and the Potter bounds. In particular if $a\to\infty$, $u\to0$, $au\to0$, then $\log(Q(au)/Q(u))/\log a\to r$, including $r=0$. See [Bingham, Goldie and Teugels, *Regular Variation*, §§1.2, 1.5](https://doi.org/10.1017/CBO9780511721434).

Suppose $w=\log(v/b_N)\to\infty$ and $w=O(\log N)$. Then
$$
 B_N(v)\sim Q(w/N)/(1+r).                                             \tag{2}
$$
For $0<\epsilon<1$ use $p=(1+\epsilon)w/N$ for the upper bound. Its failure contribution is at most $b_Ne^{-\epsilon w}=o(Q(w/N))$, and its acceptance contribution is at most $A(p)$. For a lower bound, any $p\le(1-\epsilon)w/N$ has failure cost at least $b_N\exp(\epsilon w-O(w^2/N))$, which dominates $Q(w/N)$ by Potter. For larger $p$ the acceptance probability is $1-o(1)$ uniformly and the conditional mean is at least $A((1-\epsilon)w/N)$. Regular variation with the *fixed* multipliers $1\pm\epsilon$ and then $\epsilon\downarrow0$ prove (2).

If $r=0$, $\liminf v/b_N\ge1$ and $v/b_N$ stays bounded, then $B_N(v)\sim b_N$. Indeed choose $s_N\uparrow\infty$ sufficiently slowly that $Q(s_N/N)/b_N\to1$, $s_N=o(N)$: for each fixed integer $s$ the ratio tends to 1, so choose increasing cutoffs $N_s\ge s^2$ beyond which it is within $1/s$, and take the largest eligible $s$. The trial $p=s_N/N$ suppresses the bounded normalized continuation. For the lower bound fix $0<\eta<1$. If $p\ge\eta/N$, both $A(p)\ge A(\eta/N)\sim b_N$ and $v\ge(1-o(1))b_N$, so their convex combination is large enough. Otherwise $(1-p)^N\ge (1-\eta/N)^N\to e^{-\eta}$, so taking $\eta\downarrow0$ gives the same conclusion. Both this argument and (2) apply along arbitrary subsequences.

Finally $M_n\sim\Gamma(1+r)b_n$. Indeed $M_n=n\int_0^1 Q(u)(1-u)^{n-1}du$. On $0<u<d$ for fixed sufficiently small $d$, put $z=nu$ and divide by $b_n$. The integrand tends to $z^r e^{-z}$ and is dominated by an integrable constant times $\max(z^{r-\epsilon},z^{r+\epsilon})e^{-z/2}$ for $0<\epsilon<1$, by Potter. The remaining integral divided by $b_n$ is at most $n(1-d)^{n-1}\mu/b_n=o(1)$ because $\log b_n/\log n\to-r$.

## Matching the actual horizon

For a lower bound enlarge each of the at most $k$ blocks to $n$ trials and retain the forced last cost: optimizing the enlarged blocks backwards gives $H_k(n)\ge B_n^{\circ k}(\mu)$. Missing blocks can be represented by a skip. Formally the monotonicity above gives this bound for each sorted schedule even if an original block itself had a disadvantageous cutoff.

When $r>0$, the first application to $v=\mu$ has $w\sim r\log n$. Iterating (2) a fixed number of times gives the lower bound in (1), because if $v\sim Q(r\ell_j(n)/n)/(1+r)$, Potter implies $\log(v/b_n)\sim r\log(r\ell_j(n))\sim r\ell_{j+1}(n)$, and replacing an argument by a $1+o(1)$ multiple preserves asymptotic equivalence for $Q$.

For the upper bound use induction on $k$, the base using $n-1$ trials and a forced last draw in (2). For $k\ge2$ set $m=\lfloor n/\ell_{k+1}(n)\rfloor$ and give the first block $N=n-m$ trials and the last $m$ observations to an optimal (or arbitrarily nearly optimal) $(k-1)$-threshold policy. By induction its infimal cost is $v\sim Q(r\ell_{k-1}(m)/m)/(1+r)$. Now $N/n\to1$, $\ell_{k-1}(m)/\ell_{k-1}(n)\to1$, and
$$
\log\!\left( r\ell_{k-1}(m)N/m\right)\sim\ell_k(n)
$$
because $\log(n/m)\sim\log\ell_{k+1}(n)=o(\ell_k(n))$. Potter therefore gives $\log(v/b_N)\sim r\ell_k(n)$. Applying (2) to the first block yields precisely the upper bound (1); the first cutoff and the last policy use at most $k$ distinct thresholds, whether ordered or not.

When $r=0$ the lower bound $B_n^{\circ k}(\mu)$ and the attainable upper bound $B_{\lfloor(n-1)/k\rfloor}^{\circ k}(\mu)$ are asymptotically equivalent to $v_k(n)$. For the latter bound use $k$ identical-length blocks, adding any leftover trials to one of them (or use monotonicity of the optimized block lengths). To see both equivalences, let $N=n$ or $N=\lfloor(n-1)/k\rfloor$. Then $b_N/b_n\to1$. Induct on $j$, starting at $\mu$. If the incoming cost is asymptotic to $v_{j-1}(n)$, its ratio to $b_N$ has liminf at least one, since $w_i\ge1$. Along any subsequence on which that ratio stays bounded, $v_j(n)/b_n\to1$ by uniform convergence at bounded multipliers, and the bounded-ratio block lemma applies. Along any subsequence on which it diverges, its log is asymptotic to $w_j(n)$ and is $O(\log N)$ (all these costs are bounded; $b_n=n^{o(1)}$). Formula (2) applies; changing its quantile argument from $w_j/N$ to $w_j/n$ by a bounded factor changes the quantile by $1+o(1)$ because $r=0$. Every subsequence has a further subsequence of one of these types. This proves the assertions without assuming that successive $w_j$ have limits.
