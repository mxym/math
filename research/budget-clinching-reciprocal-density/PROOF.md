# A strictly increasing-hazard counterexample to optimality of middle-ironed clinching

**Yongxian Zhang.** AI-assisted mathematical research; the argument below is analytical. It gives a strict comparison and does not identify the optimal mechanism.

## The question and an atomless law

Feng and Hartline, *An End-to-end Argument in Mechanism Design (Prior-independent Auctions for Budgeted Agents)*, FOCS 2018, [conference paper](https://ieee-focs.org/FOCS-2018-Papers/pdfs/59f404.pdf), [full version](https://arxiv.org/abs/1804.01977), prove welfare optimality among dominant-strategy incentive-compatible mechanisms for two independent uniform values with a common public budget. In their introduction they conjecture that the welfare result extends to regular distributions. Their welfare regularity condition is concavity of the value CDF, not Myerson virtual-value monotonicity alone (full version, Definition 2.1). We use their two-agent mechanism of Definition 4.1 and Figure 3(a), and their standard utility $vx-p$ for allocation probability $x$ and deterministic payment $p$ at most the budget.

**Theorem.** For two i.i.d. agents with a common public budget of one, there exists a continuous, positive, nonincreasing density on a compact valuation interval, with strictly increasing hazard rate, for which every middle-ironed clinching auction is strictly welfare-dominated in expectation by another feasible DSIC, ex-post individually rational, no-positive-transfer mechanism.

Set $h=28/5$, $r=3/5$, $T=1/10$ and use the following **unnormalized** density on $[0,h]$:
$$f(x)=1+(r-x)_+/6,qquad Z=\int_0^h f=h+Tr/2=563/100.$$
Thus the actual density is $f/Z$. Its CDF is concave. With $S(x)=\int_x^h f(t)dt$ its hazard is $f(x)/S(x)$ on $[0,h)$. The numerator of the derivative of the hazard is $f^2+f'S\ge1-Z/6>0$ on either side of $r$, and the hazard itself is continuous there. This also gives the usual increasing virtual value $x-S(x)/f(x)$; we are not comparing *revenue*.

For two reports $u<v$, let $D(u,v)=2x_{\rm high}(u,v)-1$ for any symmetric fully allocating mechanism. Up to a common additive constant (the welfare of awarding the item by a fair coin), expected welfare multiplied by $Z^2$ is
$$G=\int_{0<u<v<h}(v-u) f(u) f(v) D(u,v)\,du\,dv.$$
Indeed the two label orders cancel the factor $1/2$ in the welfare change.

## The best member of their entire family

Write $a\in[0,1]$, $b=2-a$. From the cited definition and figure, $D=0$ if both bids belong to $[a,b]$, $D=ab/u^2$ if $u,v>b$, and $D=1$ elsewhere off the diagonal. Boundary ties have zero probability for this comparison. Let $G(a)$ be its unnormalized gain, $L=b-a$, $J(u)=\int_u^h(v-u)f(v)dv$, and $A=h(\log(h/2)-1)$, with natural logarithms.

We show $G$ decreases strictly up to $a=1$. In fact, for $0<a<1$, differentiating the moving triangular regions gives
$$
 G'(a)= f(a)\int_a^b(v-a)f(v)dv +
 f(b)\int_a^b(b-u)f(u)du
 +L\left(\int_b^h f(u)J(u)u^{-2}du -f(b)J(b)/b\right).
$$
The first term accounts for the lower side of the zero-gain triangle. The upper cutoff moves downward: newly high bids convert middle-middle comparisons to full gains (second term), while pairs whose lower bid crosses that cutoff change full gain to $a/b$ (the negative boundary term). The remaining integral differentiates $ab$, whose derivative is $L$. All integrands are bounded on the changing high regions, since $b\ge1$. Continuity of $f$ justifies the derivative, and $G$ is continuous at both endpoints.

Since $b>r$, we have $f(b)=1$ and $J(u)=(h-u)^2/2$ for $u\ge b$. Integration by parts shows that the bracket equals $-h\log(h/b)+h-b$. If $a\ge r$, the first two terms sum to $L^2$; hence $G'(a)/L=h(1-\log(h/b))-a\le -A$. If $a<r$, bound the nonnegative terms using $f(v)\le1+T\mathbf1_{v<r}$ and $f(a)\le1+T$. Writing $e=r-a$, this yields
$$
 G'(a)/L\le h(1-\log(h/b))-a+TL/2+Te+T^2 e^2/(2L)
 \le -A+ T(1+r)+T^2r^2/4=-A+1609/10000 .
$$
For the second bound $L\le2$, $b\le2$, and $(r-a)^2/L\le r^2/2$ because $a\le r<1$. The elementary logarithm bounds given below imply $A>1609/10000$. Thus the best family member is exactly $a=0$, including when a threshold is randomized independently of bids.

## A feasible four-band rule

Put $c=d=1/100$, $l=2-d$, $\gamma=c/4$, and $s=cd$. Partition the type space into $P=[0,c)$, $Q=[c,l)$, $R=[l,2)$, and $H=[2,h]$. The following table gives one agent's allocation probability, with her report indexing the row and the opponent's report the column:
$$
\begin{array}{c|cccc}
 &P&Q&R&H\\\hline
P&1/2&1/2&0&0\\
Q&1/2&1/2&1/2&0\\
R&1&1/2&1/2&\gamma\\
H&1&1&1-\gamma&*
\end{array}
$$
In the last cell, the higher report wins with probability $1/2+s/(2u^2)$, where $u$ is the lower report. The lower report gets the complement, and equal reports split equally. The two allocations sum to one at every profile. Each column is nondecreasing in own report: in particular against a high opponent the allocation jumps from $\gamma$ to at least $1/2-s/8$ upon entering $H$ (unless tied there), then increases until the opponent's bid, passes through $1/2$ at the tie, and is constant above it.

Given the opponent's report $t$ and own report $v$, let the **deterministic** payment be $p(v,t)=v x(v,t)-\int_0^v x(z,t)dz$. Monotonicity gives truthful optimality for every $v,t$ by the envelope identity (the gain over reporting $w$ is $\int_w^v(x(z,t)-x(w,t))dz\ge0$). The truthful utility is the nonnegative integral and the payment is nonnegative, including $p(0,t)=0$. This fractional/lottery allocation with a nonrandom payment is the utility convention in the cited paper; we do not assert universal truthfulness conditional on the lottery outcome.

For each fixed $t$, the payment is nondecreasing in $v$. The largest payments against opponents in $P,Q,R$ are respectively $l/2$, $1$, and $c/2+2(1/2-\gamma)=1$, obtained from the jumps in the columns. For $t\in H$, the payment on the upper constant allocation (or the upper bound from the right limit if $t=h$) is
$$
 t\left(\tfrac12+\tfrac{s}{2t^2}\right)-\gamma d-
 \int_2^t\left(\tfrac12-\tfrac{s}{2z^2}\right)dz
 =1-\gamma d+s/4=1.
$$
This bounds the tie payment as well, including $t=2$ and $t=h$. Both agents obey the hard budget profile by profile.

## Strict improvement

Against the best member $a=0$, the gain $D$ changes only for $P$ versus $R$ (increase of $1$), $R$ versus $H$ (decrease of $2\gamma$), and two reports in $H$ (increase of $s/u^2$). Put $m=\int_0^c f(v)dv$, $j=\int_0^c v f(v)dv$. The three respective changes in $G$ are
$$
 d[(2-d/2)m-j],\quad
 -\tfrac{cd}{4}(h-2)(h-2+d),\quad
 cd\int_2^h\frac{(h-u)^2}{2u^2}du.
$$
The last integral is $h^2/4-1-h\log(h/2)$. Substituting $m/c=1+T-c/12$, $j/c=(1+T)c/2-c^2/18$, and collecting, the actual expected-welfare gain is exactly
$$
 \frac{cd}{Z^2}\left[(2-d/2)(T-c/12)-(1+T)c/2+c^2/18-dh/4-A\right]
 =\frac{cd}{Z^2}\left[\frac{128407}{720000}-A\right]>0.
$$
For an elementary rational check of both strict signs take $y=(h/2-1)/(h/2+1)=9/19$ and $P_9=2\sum_{i=0}^{8}y^{2i+1}/(2i+1)$. The positive logarithm series gives
$$
 P_9<\log(h/2)<P_9+2y^{19}/[19(1-y^2)].
$$
Substitution yields $33/200<A<167/1000$ by rational arithmetic. These bounds lie strictly between $1609/10000$ and $128407/720000$.

The example concerns the Bayesian expected *welfare* of direct DSIC mechanisms for this known i.i.d. law. It does not contradict optimal middle ironing for the uniform law, prove optimality of the four-band rule, settle the best prior-independent approximation factor, or address optimal revenue.
