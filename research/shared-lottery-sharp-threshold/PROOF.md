# The sharp competition threshold for group requests in a weighted individual lottery

Yongxian Zhang

Arnosti and Bonet's *Lotteries for Shared Experiences* (EC 2022 extended abstract; [full manuscript, §4.3.1, equations (19)–(22), Conjecture 1](https://arxiv.org/pdf/2205.10942)) asks when the members of one group should each request the entire group's ticket requirement. We derive their conjecture from a subsequent small-deviation theorem. The probabilistic bound itself and the original authors' Poisson relaxation are prior results, not new inequalities of this note.

**Conditional model.** Let a group have $g\ge1$ members and let the integer ticket supply be $k\ge g$. With the outside requests and their realized scores fixed, $t\ge0$ denotes the sufficient cutoff in equation (19). Given a request profile $a_i\in\{1,\ldots,k\}$ and fresh independent $E_i\sim\operatorname{Exp}(1)$ for group members, equation (20) maximizes
\[
 V_t(a)=\Pr\Bigl\{\sum_{i=1}^g a_i\mathbf1_{a_i E_i<t}\ge g\Bigr\}.
\]
The all-$g$ profile has value $1-e^{-t}$, as noted in equation (21). We study this conditional problem at finite cutoffs, not an unconditionally dominant strategy against arbitrary outside profiles.

**Theorem.** For every $0<t\le1$, the all-$g$ profile is the unique maximizer of $V_t$. At $t=0$ every profile has value zero. The constant $1$ is exact uniformly over group sizes: for every fixed finite $t>1$ there is an integer $r$ such that, as $g\to\infty$ and $k\ge\max\{r,g\}$, the all-$r$ profile has success probability tending to $1$. In particular it beats $1-e^{-t}$ for all sufficiently large $g$. This last assertion does not say all-$g$ is suboptimal in each fixed group when $t>1$.

**Proof.** We use the $\delta\ge1$ branch of Fu, Han, Wang, Yan, Zhang and Zhou's [Theorem 1.1](https://arxiv.org/html/2607.23980v1#S1): if $Y_1,\ldots,Y_M$ are independent nonnegative variables of mean one, then $\Pr\{\sum_jY_j<M+\delta\}\ge (1-1/(M+\delta))^M$. Their theorem allows each mean to be at most one and uses the actual total mean; only the equal-mean case is needed here.

Following the Poisson relaxation in Arnosti–Bonet's proof of Proposition 8, take independent $N_i\sim\operatorname{Pois}(t/a_i)$ and realize the success indicators as $\mathbf1_{N_i\ge1}$. The normalized uncapped sum $Z_t=g^{-1}\sum_i a_i N_i$ has mean $t$. The actual sum divided by $g$ is pointwise no larger.

If $0<t<1$, split each $N_i$ into $M$ independent Poisson counts of mean $t/(Ma_i)$, independently across $i$. The resulting $M$ block sums have the same law and add to $Z_t$; multiply each by $M/t$ to get independent nonnegative variables of mean one. With $\delta=M(1/t-1)$, we have $M+\delta=M/t$ and $\delta\ge1$ for every sufficiently large integer $M$. Hence
\[
 \Pr(Z_t<1)\ge (1-t/M)^M\longrightarrow e^{-t}.
\]
At $t=1$, couple the counts at $t<1$ to those at one by adding independent Poisson increments with means $(1-t)/a_i$. The chance that any count changes is at most $(1-t)\sum_i1/a_i\to0$. Thus the same bound holds at one without a continuity assumption on the distribution function at the jump threshold. Consequently $V_t(a)\le 1-e^{-t}$ for $0<t\le1$.

If some $a_i<g$, the positive-probability event $N_i=\lceil g/a_i\rceil$, $N_j=0$ for all $j\ne i$, makes $Z_t\ge1$ but cannot give the group enough tickets when each member's award is capped at one win. This makes the inequality strict. If every $a_i\ge g$, then a single win suffices and $V_t(a)=1-\exp(-t\sum_i1/a_i)$. Because $\sum_i1/a_i\le1$ with equality exactly when all $a_i=g$, this proves uniqueness for $t>0$ in the asserted range.

Finally fix $t>1$. Since $r(1-e^{-t/r})\to t$ as the integer $r\to\infty$, fix an $r$ with $r(1-e^{-t/r})>1$. Give each of $g$ members this same request. The acquired tickets per member are iid random variables taking values $0,r$, of mean strictly greater than one. By the law of large numbers their average is at least one with probability tending to one. No finite profile has success probability one at finite $t$, since every member misses with strictly positive joint probability. This also identifies the supremum over group sizes and admissible profiles for $t>1$. $\square$

The source's Proposition 8 already treats profiles for which success is determined only by the number of winning members, and also identifies profitable deviations at sufficiently high cutoffs. The split into arbitrarily many independent increments lets its coupling cover every request profile at the conjectured cutoff. For fixed $t>1$ the construction above instead varies the group size. Neither the unconditional fairness/efficiency of an equilibrium nor the authors' distinct open extension to non-dichotomous utilities is asserted here.
