# An inverse-logarithmic deficit

Let $W:[0,1]^2\to[0,1]$ be symmetric and measurable, $p=\int W>0$, and
$$
F(W)=\int W(x,y)W(y,u)W(u,v)(1-W(v,x))\,dx\,dy\,du\,dv.
$$
Write $M(p)=\sup_{\int W=p}F(W)$. In finite graph language this is the labelled-injective count divided by $n^4$ in the limit $n\to\infty$ with red-edge densities tending to $p$. Indeed each finite graph has a step graphon, with a collision error $O(1/n)$; conversely, graphon sampling approximates both the density and the count. Compactness in cut distance and continuity of these fixed-pattern densities give the supremum convention for all such sequences. For the undirected cycles counted per $n^4$ in Basit et al., divide $F$ by two.

## Sample two oriented red edges

Under the product probability law in which $(X,Y)$ and $(U,V)$ are independent with common density $W(x,y)/p$, assign colours to the two bridge pairs $YU,VX$ independently given the four labels, using $W$. Labels are distinct almost surely: the tilted law is absolutely continuous. Even if some labels fall in the same step-graphon class, colours of distinct pairs are conditionally independent. Swapping the two sampled edges exchanges the bridges. Consequently
$$
\Delta(W):=\frac12-\frac{F(W)}{p^2}
=\frac12\Pr(YU,VX\text{ have the same colour}).
$$
Indeed a red $YU$ and blue $VX$ has probability $F(W)/p^2$, equal to the probability of the opposite ordering. In particular the deficit is nonnegative.

## Every graphon has a deficit

Put $d(x)=\int W(x,y)dy$ and $R=6/5$. The law of $X$ is $d(x)dx/p$; its mass on $d<p/2$ is at most $1/2$. Partition $[p/2,1]$ into at most
$$
K=1+\left\lceil\log(2/p)/\log R\right\rceil
$$
bins with upper-to-lower ratio at most $R$ (place the endpoint $1$ in the last bin). By Cauchy–Schwarz the probability that $d(X),d(U)$ occupy the same retained bin is at least $1/(4K)$.

Fix a bin of positive endpoint mass and write $S$ for its preimage under $d$. Use uniform **normalized Lebesgue measure on $S$** for row variables and Lebesgue measure on $[0,1]$ for columns. Let $w$ be the restricted rectangular kernel, $\ell(x)=\int w(x,y)dy$, $h(y)=\int w(x,y)dx$, $b=\int w>0$. In this paragraph all integrals use these probability measures. On $S$ we have $\ell\le Rb$. Given $X,U\in S$, each original edge now has density $w/b$ and the two edges are independent. The single-bridge red marginal $t$ and joint red probability $C$ satisfy
$$
t=b^{-2}\int\ell(x)h(y)w(x,y)\,dx\,dy
\le Rb^{-1}\int h^2,
$$
$$
C=b^{-2}\int\left(\int w(x,y)w(u,y)dy\right)^2dx\,du
\ge b^{-2}\left(\int h^2\right)^2\ge t^2/R^2.
$$
The first identity integrates out the unused original endpoints. The second integrates the two column variables separately; its first inequality is Jensen's inequality on the two row variables. Both bridge marginals equal $t$ by exchangeability. Thus the conditional same-colour probability is at least
$$
1-2t+2C\ge 1-2t+2t^2/R^2\ge 1-R^2/2=7/25.
$$
All other cases contribute a nonnegative probability. Accounting for the half in the identity for $\Delta$ yields $\Delta(W)\ge 7/(200K)$.

## A matching-order construction

Choose $k\ge2$. Let $A$ be a red clique of mass $\alpha=2^{-k}$, $B$ an independent set of mass $1-\alpha$. With $S=\sum_{i=1}^k2^{-i}=1-\alpha$ and $T=\sum_{j=1}^k2^j=2S/\alpha$, give $A_i$ mass $\alpha 2^{-i}/S$ and $B_j$ mass $(1-\alpha)2^j/T$. Put red between $A_i$ and $B_j$ exactly when $j\le i$. Write $L=\sum_{1\le j\le i\le k}2^{j-i}$, so $k\le L\le 2k$. The red density is
$$
p_k=\alpha^2+2\alpha(1-\alpha)L/(ST)=4^{-k}(1+L/S).
$$
A random red edge is within $A$ with probability $\alpha^2/p_k\le1/k$. Otherwise it crosses, and its unoriented index interval $[j,i]$ has mass $2^{j-i}/L$. The expected number of indices in an interval is at most $4$: there are at most $k$ intervals with $i-j=d$ and $\sum_{d\ge0}(d+1)2^{-d}=4$. For each fixed index, the probability of covering it is at most $4/k$, since at most $d+1$ intervals with $i-j=d$ cover that index. Conditional on the first interval, sum these cover probabilities over its indices. The probability of overlap for two independent intervals is therefore at most $16/k$.

For disjoint intervals ordered from earlier to later, the later $A$ to earlier $B$ cross pair is red and the other cross pair is blue. The $AA$ pair is red and the $BB$ pair is blue. These are the two possible opposite-bridge matchings, so either orientation gives different bridge colours. The union bound for at least one clique edge or two overlapping cross intervals yields $\Delta(W_k)\le (2/k+16/k)/2=9/k$.

Finally, for $0<p\le p_k$, shrink the support onto $[0,s]^2$ with $s=\sqrt{p/p_k}$ by rescaling both variables, and set $W=0$ elsewhere. Its density is $p$ and its $F$ equals $s^4 F(W_k)$ because every label meets one of the two required disjoint red edges. The ratio $F/p^2$ is unchanged. For each sufficiently small $p$, choose $k=\lfloor\log_4(1/p)\rfloor\ge2$. Then $p_k\ge4^{-k}\ge p$, and $k$ is comparable to $\log(1/p)$. This gives the required upper bound on the infimum of $\Delta(W)$, complementing the uniform lower bound above. No simultaneous sparse finite-graph approximation is used.
