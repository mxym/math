# Two lower bounds for exact envy-freeness of random indivisible chores

**AI-assisted research note, independently checked internally and not externally peer reviewed.** There are $n$ agents and $m>0$ chores; every disutility $D_{iz}$ is drawn independently from a common nonatomic law with distribution function $F$ on $[0,1]$. All chores must be partitioned among the agents; disutility adds within a bundle. An allocation is envy-free (EF) if every agent values its own bundle at cost no greater than any other bundle. In particular, almost surely individual costs are strictly positive and each row has a strict ranking. Agents and chores are labeled.

## Results

1. **All nonatomic laws.** There is a number $C_A\in(1.26016893448,1.26016893449)$ such that, for every fixed $\epsilon>0$, the EF existence probability tends to zero whenever $m\le(C_A-\epsilon)n$, $n\to\infty$. The uniform supremum over such nonatomic laws also tends to zero: the finite rank bound below does not involve the cost distribution. For $m/n\to c\in[1,C_A)$ the upper bound is exponentially small in $n$.
2. **Uniform law and index-one behavior at zero.** There is a number $C_U\in(1.36145148634,1.36145148635)$ such that, for every fixed $\epsilon>0$, the same high-probability nonexistence holds whenever $m\le(C_U-\epsilon)n$ for the uniform law. More generally it holds for each fixed nonatomic $F$ positive on every $(0,x]$, $x>0$, such that $F(tx)/F(x)\to t$ as $x\downarrow0$ for every $t>0$. This includes $F(x)\sim ax$ for any $0<a<\infty$, for instance a finite positive density limit at zero. Convergence is not asserted uniformly over this regular-variation class.
3. **Interpretation.** These numbers are thresholds of explicit *necessary tests*, not the true phase transitions for EF. There is no existence assertion just above either number nor a claim at the endpoints. The 2025/26 Manurangsi–Suksompong model already has nonexistence for all nonatomic laws below approximately 1.1256 and existence for PDF-bounded laws at $m\ge2n$. The [preceding repository note](https://github.com/mxym/math/pull/120) shows that the universal sufficient coefficient 2 cannot decrease, using specially chosen fixed laws on subsequences. That different quantifier does not give either of the two all-size lower bounds here. We reuse its deterministic request lemma and finite local-tree method; variable prefix lengths and the explicit bounds are treated below.

## A. A distribution-free first moment

If $m<n$, some agent is empty and the holder of a nonempty bundle envies it. Take $n\le m<2n$, put $u=(m-n)/n$, and suppose precisely $r$ agents hold nonsingletons; the other $s=n-r\ge 2n-m>0$ are singleton agents. Fix the identities of all agents of each type and an ordered list of sizes $b_i\ge2$ for the $r$ nonsingleton agents, with $\sum_i b_i=m-s$. For this size vector there are $m!/\prod_i b_i!$ candidate allocations (including the specified labeled singleton holders). A row of a singleton holder must rank its own singleton first among the $s$ singles, of probability $1/s$. A row of a nonsingleton holder must rank *each* of its $b_i$ items ahead of all $s$ singles: the individual items are no more expensive than the owner's full bundle. The probability of this necessary ordinal event is $\binom{s+b_i}{b_i}^{-1}$, by symmetry of iid nonatomic draws. All these events use different agent rows and are independent for this fixed assignment. Hence the expected number of EF assignments at these sizes/identities is at most

$$m!s^{-s}\prod_{i=1}^r\frac{s!}{(s+b_i)!}\le m!\,s^{-m}.$$

For $m>n$, writing $b_i=1+h_i$ makes $(h_i)$ a positive ordered composition of $m-n$ into $r$ parts. Summing over identities and compositions gives
$$
\Pr(\mathrm{EF})\le\sum_{1\le r\le m-n}\binom nr\binom{m-n-1}{r-1}\frac{m!}{(n-r)^m}. \tag{A1}
$$
For $m=n$, the bound is $n!/n^n$. No occupancy independence or assumption that all nonsingletons have size two is used.

Set $a=r/n$ and $c=1+u$. With $H(x)=-x\log x-(1-x)\log(1-x)$, continuously extended at 0 and 1, define
$$ J(u,a)=H(a)+uH(a/u)+(1+u)\bigl[\log((1+u)/(1-a))-1\bigr],
\qquad J_*(u)=\max_{0\le a\le u}J(u,a).$$
For $0<u\le1/3$, the log of (A1) is at most $nJ_*(u)+O(\log n)$: bound $\binom{m-n-1}{r-1}\le\binom{m-n}{r}$, use $\binom nk\le e^{nH(k/n)}$, Stirling for $m!$, and at most $n$ summands. The error here is uniform over $u\le1/3$. At $u=0$ take $J_*(0)=-1$.

The maximum is continuous in $u$, including zero (put $a=vu$, $v\in[0,1]$). It is strictly increasing for $u>0$ in this interval. In fact at each interior $a$ with $0<a<u$, the $u$ derivative is $-\log(1-a/u)+\log((1+u)/(1-a))>0$, and the maximizing $a$ is interior. Its two derivatives in $a$ are
$$ J_a=\log\frac{(1-a)(u-a)}{a^2}+\frac{1+u}{1-a},\qquad
J_{aa}=\frac{u+a}{(1-a)^2}-\frac1{u-a}-\frac2a<0 $$
on $0<a<u\le1/3$. Indeed the first summand is at most $3/2$ and the last is at most $-6$. $J_a$ tends to $+\infty,-\infty$ at the respective ends, proving uniqueness and interiority. The exact rational checks show that $J_*(0.26016893448)<0<J_*(0.26016893449)$; thus it has a unique zero $C_A-1$ in that interval. This proves the all-law result, including if the cost law changes with market size while remaining nonatomic.

## B. Finite-depth requests for marked random prefixes

For each agent keep an initial segment of its ranked chores, truncated at $K$, in which every cost is *strictly less* than the sum of the costs of its two cheapest distinct chores. This paragraph concerns $m\ge K\ge2$. The prefix can be shorter than $K$. For any EF allocation, if a singleton occurs inside a row's prefix, the earliest such singleton is cheaper to that agent than every other bundle: earlier nonsingletons cost at least the sum of its two cheapest items, any other singleton is more expensive. Thus that earliest singleton must be its own bundle.

Start all agent-to-chore requests at zero. At round $t+1$ a row requests its item at position $\ell$ if *all* preceding items got at least one round-$t$ request from another agent. The empty conjunction is true. Every requested item, **if singleton**, must belong to the requester: inductively the earliest preceding singleton would be forced both to that row and to a different requester, which is impossible; therefore the requested singleton would be the earliest. A chore requested by two rows cannot be a singleton. An EF allocation has at most $m-s\le2(m-n)$ nonsingleton items. This is the earlier deterministic implication, now applied to individually marked list lengths.

Let $m/n\to c\ge1$ and $K,t$ be *fixed*. In each row let the length mark $L^{(m)}\in\{0,\dots,K\}$ be independent of the ranked permutation, iid across rows, and assume $\Pr(L^{(m)}=j)\to\pi_j$. Write $q_\ell=\sum_{j\ge\ell}\pi_j$. Then the fraction of chores hit by at least two requests at round $t$ converges in probability to
$$ f_t=1-(1+\lambda_t)e^{-\lambda_t},\qquad \lambda_0=0,\quad
\lambda_{t+1}=c^{-1}\sum_{\ell=1}^K q_\ell(1-e^{-\lambda_t})^{\ell-1}. \tag{B1}$$

**Proof of the marked list limit.** Reveal rows as an incidence graph between chores and agents, labeling each row with its length and edges with their ranks. Suppose $b$ chores have been queried and unexposed independent rows have avoided them in their retained prefixes. For one such row the probability of having length $j$ and hitting a specific *new* chore at a specific rank $\ell\le j$, given those avoidances, is
$$\frac{\Pr(L^{(m)}=j)}m + O_{b,K}(m^{-2}).$$
Before conditioning the first term is exact. For a prior forbidden label and another rank, the joint hit probability is at most $1/[m(m-1)]$; conditioning on avoidance divides by $1-O(bK/m)$. Conditioning the unexamined rows retains their independence; previously discovered rows must be explored through their own labels, not treated as fresh random neighbors. For a bounded exposure all but $O(1)$ rows remain. For a new target chore, its incident fresh rows of the finitely many mutually exclusive types $(j,\ell)$ therefore converge jointly to independent Poisson variables of means $\pi_j/c$. For example the joint pgf is $(1+\sum_{j,\ell}p_{j,\ell}(z_{j,\ell}-1))^{n-O(1)}$ with $np_{j,\ell}\to\pi_j/c$. The remaining ranks of a new row are conditionally sampled without replacement among eligible labels. Unintended coincidences among discovered labels or between two root neighborhoods have probability $O_{B,K}(1/m)$ when the number explored is at most $B$. The conditional Poisson limits are uniform for bounded histories. Truncating offspring as needed at $B$ then proves the fixed-cap one- and two-root local limits; the two rooted trees are independent in the limit.

The depth of the event in (B1) is at most $2t$. The cap can be removed: expected counts of distinct simple paths of length $2h$ from one root are at most
$$ n^h m^h\{K(K-1)/(m(m-1))\}^h, $$
since each of the distinct $h$ rows must contain two specified distinct items in its at-most-$K$ list; odd paths have the additional factor $nK/m$. Summing to depth $2t$ gives a uniform bound depending on $K,t,c$, including for two roots. Markov's inequality makes the error $O_{K,t,c}(1/B)$ after the market limit. On a rooted limit tree, a row reached at rank $\ell$ requests upstream with probability $(1-e^{-\lambda_t})^{\ell-1}$ since its earlier chores need requests from *other* rows and are on disjoint branches. At a chore, separately thinning independent Poisson populations of types $(j,\ell)$ gives a Poisson total with the mean in (B1). This is not independent thinning of different ranks in the same row: one row has just one mark $j$. For the empirical fraction, the one-root limit gives its mean and the independent two-root limit makes its variance tend to zero. This proves (B1).

Consequently, for any fixed $K,t$ with $f_t>2(1-1/c)$, there is no EF allocation with probability tending to one. No statement about infinite-depth local convergence is needed.

## C. The uniform prefix and the zero-tail law

Let $D_{(j)}$ be row order statistics. The maximal retained prefix ends just before the first rank with $D_{(\ell)}\ge D_{(1)}+D_{(2)}$ (or at $K$). Length depends only on sorted values, independently of their uniformly random permutation.

For the uniform law couple the order statistics exactly as $D_{(\ell)}=T_\ell/T_{m+1}$, where $T_\ell=\sum_{j=1}^\ell E_j$ for iid rate-one exponentials. For completeness, normalized increments $(E_j/T_{m+1})_{1\le j\le m+1}$ have constant density $m!$ on the standard simplex: changing from increments to total $v$ and the first $m$ proportions gives Jacobian $v^m$, and $\int_0^\infty e^{-v}v^m\,dv=m!$. Their partial sums consequently have the usual constant $m!$ density on $0<u_1<\cdots<u_m<1$. For $\ell\ge2$ the certified inequality is $E_3+\cdots+E_\ell<E_1$, giving
$$q_1=q_2=1,\qquad q_\ell=2^{-(\ell-2)}\quad(\ell\ge2). \tag{C1}$$
This is an *exact* finite-$m$ computation for $\ell\le m$, via $\mathbb E e^{-E_j}=1/2$; the rank tails are nested, not independent.

Suppose next $F$ satisfies the index-one condition in Result 2, and $Q(v)=\inf\{x:F(x)\ge v\}$. Continuity, no atom at zero and positivity near zero imply $x_m=Q(1/m)>0$, $F(x_m)=1/m$, and $x_m\downarrow0$. If a positive sequence $y_m\to y>0$, then $Q(y_m/m)/x_m\to y$: bracket between $(y-\delta)x_m$ and $(y+\delta)x_m$, whose $F$ values times $m$ tend to $y-\delta$ and $y+\delta$. Take $\delta<y$. The bracketing uses strict inequalities for all large $m$, so flat pieces of $F$ cause no issue. Under the same coupling $mT_\ell/T_{m+1}\to T_\ell>0$ almost surely at every fixed rank, by the strong law. Applying the sequential bracket pathwise and mapping the uniform order statistics through $Q$ gives $D_{(\ell)}/x_m\to T_\ell$ jointly for any fixed $K$. At $\ell\ge3$ the boundary $T_\ell=T_1+T_2$ has zero probability since $E_1$ has a density and is independent of $E_3+\cdots+E_\ell$; at $\ell=1,2$ the inequality holds strictly a.s. Thus all finite mark tails converge to (C1), as does the bounded length law (by differences). There is no convergence requirement on the untruncated random list.

## D. Computing the forcing bound

Use the infinite tail sequence (C1) **only** to pick finite $t,K$. If $p=1-e^{-\lambda}$ then
$$\sum_{\ell\ge1}q_\ell p^{\ell-1}=1+\frac p{1-p/2}=\frac{3-e^{-\lambda}}{1+e^{-\lambda}}=:g(\lambda).$$
The scalar iteration $\lambda_{t+1}=g(\lambda_t)/c$ starts at 0 and increases to its unique positive fixed point $\lambda(c)$. Indeed $g$ is positive, bounded above by 3, and $g'(x)=4e^{-x}/(1+e^{-x})^2$ is positive and nonincreasing for $x\ge0$. Therefore $g(x)-xg'(x)\ge g(0)=1$, so $g(x)/x$ strictly decreases from infinity to zero. The limiting obstruction $1-(1+\lambda)e^{-\lambda}>2(1-1/c)$ is equivalent to
$$ (g(\lambda)/\lambda)\,[1+(1+\lambda)e^{-\lambda}] <2. \tag{D1} $$
Both positive factors on the left decrease strictly with $\lambda>0$; their product has limits infinity and zero. Define $x_U$ as the unique equality root and $C_U=g(x_U)/x_U$. Then (D1) holds for all $1\le c<C_U$. First choose a finite $t$ giving a strict excess. For that fixed $t$ take a finite $K$ large enough that the same is true in (B1): the omitted series converges uniformly on $0\le p\le1$ since the tails in (C1) are summable, and finite compositions are continuous. This choice is independent of $n$. Then apply the marked local limit, not the fixed-point equation, to the markets.

If $m/n$ is not known to converge but $m\le(C_U-\epsilon)n$, every subsequence has a further subsequence with convergent ratio; ratios below one are impossible deterministically (for $m>0$), and subsequences with $m\ge n$ use the above argument. The corresponding all-law statement follows directly from (A1) and the uniform entropy bound.

**Benchmark.** At arbitrary positive nonatomic costs retaining only ranks 1 and 2 is always valid. The same calculation with $g_2(\lambda)=2-e^{-\lambda}$ gives a forcing-test crossing in $(1.25532039069,1.25532039070)$. This restricted mechanism is strictly weaker than the all-law first moment in A. It is not presented as the sharp lower bound.

**Numerics versus proof.** The script is an optional exact verification of the decimal brackets and selected finite margins, not a simulation or substitute for the probabilistic argument. The monotone equations themselves define the constants. No external release or priority claim.
