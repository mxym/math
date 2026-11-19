# Positive universal constants for the finite-threshold question

Steinerberger's [§1.3](https://arxiv.org/pdf/1801.00663) and [2026 open-problem list, §24](https://faculty.washington.edu/steinerb/openproblems.pdf) also ask whether smaller universal constants work in place of the exponential benchmarks. The following result answers this in the same existential sense as the two displayed questions (some positive threshold), not as a growth assertion for all sufficiently large thresholds or for a sequence tending to infinity.

**Theorem.** Let X,Y be independent with the same absolutely continuous probability law on $[0,\infty)$ having unbounded support, and let $m$ be any median. Set
$$
 G(t)=\frac{\Pr(X+Y\ge 2t,\ \min(X,Y)\le t)}
             {\Pr(X+Y\ge 2t,\ \min(X,Y)\ge t)} .
$$
There exists $0<t\le 2m$ such that
$$
 G(t)>\frac1{24}\ \ge\ \frac{t}{48m}.
$$
If the mean is finite, the same threshold satisfies $G(t)>t/(96\mathbb EX)$. No bound on the density is required and the constants are not claimed optimal. This ratio lower bound is not a universal positive bound on the *unconditional* mixed probability near the median.

**Proof.** Write $S(t)=\Pr(X>t)$ and $T=2m$. Since there are no atoms, $S$ is continuous, $S(0)=1$, $m>0$ and $S(m)=1/2$. Set $q_0=0$, $q_1=m$, and for $j\ge2$ choose any $q_j$ with $S(q_j)=2^{-j}$. These quantiles are strictly ordered even when $S$ has plateaus. They tend to infinity: on every fixed compact interval $S$ is bounded below by a positive constant. Let $J\ge2$ be the first index with $q_J\ge T$, and let $x_j=q_j$ for $0\le j<J$, $x_J=T$. Set $d_j=x_{j+1}-x_j$ for $0\le j<J$. We have $d_0=m$ and $\sum_{j=1}^{J-1} d_j=m$. Some $1\le n<J$ satisfies $d_n>d_{n-1}/2$, since otherwise this finite sum would be bounded by $m\sum_{j=1}^{J-1}2^{-j}<m$.

Put $a=q_{n-1}$, $b=q_n$, $c=x_{n+1}=\min(q_{n+1},T)$. By selection $(c-b)/(c-a)>1/3$. For a realization $X=x\in[a,b]$ and $Y\ge q_{n+1}$, every $t\in[x,(x+c)/2]$ obeys $\min(X,Y)\le t$ and $X+Y\ge2t$. This interval lies inside $[a,c]$ and has length at least $(c-b)/2$. The swapped condition contributes equally and the events are disjoint since $q_{n+1}>b$. By Tonelli and independence, the integral over $[a,c]$ of the numerator of $G$ is at least
$$
 (c-b)\Pr(a\le X\le b)\Pr(Y\ge q_{n+1})
   =(c-b)(2^{1-n}-2^{-n})2^{-n-1}
   =(c-b)2^{-2n-1}.
$$
The denominator is exactly $S(t)^2$ and at most $S(a)^2=2^{2-2n}$ there. Consequently
$$
 \frac1{c-a}\int_a^c G(t)\,dt
 \ge \frac{c-b}{8(c-a)}>\frac1{24}.
$$
A positive threshold in this interval thus satisfies $G(t)>1/24$; since $t\le2m$, it meets the stated median bound. Finally $\mathbb EX\ge m\Pr(X\ge m)=m/2$, proving the mean bound as well. The argument uses the unclipped $q_{n+1}$ for the probability event, so a gap at the upper cutoff does not affect it.
