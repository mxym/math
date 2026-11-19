# Concentration of all global modes

Let $T_n$ be uniform on the $n^{n-2}$ trees on $[n]$. Write $i_k(T)$ for the number of independent vertex sets of size $k$, including the empty set, and $\mathcal M(T)$ for the indices maximizing $i_k(T)$. We show that there exists a constant $\mu$ such that, for every fixed $\varepsilon>0$ and all sufficiently large $n$,

$$
\Pr\left(\exists k\in\mathcal M(T_n): |k/n-\mu|\ge\varepsilon\right)\le e^{-c_\varepsilon n}
\tag{1}
$$

for some $c_\varepsilon>0$. Formula (3) below specifies $\mu$. The numerical argument below gives $0.304684\le\mu\le0.307543$; [the companion calculation](ANNEALED.md) tightens this to $0.305300\le\mu\le0.306955$. The theorem concerns the sampled tree's coefficient sequence, not its independence number, the coefficients averaged over trees, or a locally maximal independent set. It does not require unimodality.

## 1. A differentiable limit from descendant subtrees

For $\lambda=e^t>0$ write $Z_T(t)=\sum_k i_k(T)e^{tk}$. Root a finite tree arbitrarily. In the descendant subtree at $v$, define $R_v(t)$ as the ratio of the total weights of configurations containing its root to those not containing it. Writing $w$ for children of $v$ gives

$$
R_v=e^t\prod_w(1+R_w)^{-1},\qquad
0<R_v\le e^t,\qquad
\log Z_T(t)=\sum_{v\in T}\log(1+R_v(t)).
\tag{2}
$$

Indeed, root-absent configurations factor over the child subtrees. Recursively multiplying their partition functions and the factors $1+R_v$ proves (2). The in/out recursion and log-count factorization are classical; see the [prior-work comparison](SOURCES.md).

Let $\mathcal U$ be an unconditioned Poisson(1) Galton–Watson tree; it is finite almost surely. Order the children of $T_n$, rooted at vertex 1, uniformly at random and erase its labels. This gives a Poisson(1) Galton–Watson tree conditioned on size $n$: both probabilities of a given ordered shape are proportional to $\prod_v 1/d_v!$, where $d_v$ is its number of children.

The empirical proportion of descendant subtrees equal to any given finite ordered shape converges in probability to that shape's probability under $\mathcal U$ (Janson, Theorem 7.12(ii)). This extends to every bounded function on finite shapes: retain a finite collection of total limiting mass greater than $1-\eta$, bound the remainder by its empirical mass times the sup norm, and let $\eta\downarrow0$. The root summand in (2) lies between 0 and $\log(1+e^t)$. Consequently, for each fixed $t$,

$$
n^{-1}\log Z_{T_n}(t)\xrightarrow{\Pr}p(t):=\mathbb E\log(1+R_{\rm root}(\mathcal U;t)).
$$

Write $q_v=R_v/(1+R_v)$ and $D_v=\partial_t\log R_v$. Equation (2) gives the derivative recursion $D_v=1-\sum_wq_wD_w$, also in Fang et al., (4.2). On any bounded interval of $t$, take $a=\sup_t e^t/(1+e^t)<1$. If $N_d(v)$ counts descendants at distance $d$ with $N_0(v)=1$, induction gives

$$
|D_v|\le \sum_{d\ge0}a^dN_d(v)
$$

throughout that interval. The derivative of the root summand is $q_{\rm root}D_{\rm root}$, whose absolute value obeys the same bound. Criticality gives $\mathbb E N_d({\rm root})=1$ for every $d$, so the bound has expectation $1/(1-a)$ even though $\mathbb E|\mathcal U|$ is infinite. The mean value theorem and dominated convergence give differentiability of $p$ at each $t$. In particular set

$$
\mu=p'(0)=\mathbb E\big[q_{\rm root}(\mathcal U;0)D_{\rm root}(\mathcal U;0)\big].
\tag{3}
$$

The fringe-root term $q_{\rm root}$ by itself is not the full occupation probability of a uniform vertex.

## 2. Exponential concentration over the choice of tree

This step also follows from the [Pemantle–Peres spanning-tree concentration theorem](https://doi.org/10.1017/S0963548313000345). Here is an elementary proof. Choose $n-1$ independent uniform labels $P_i\in[n]$ for $i=2,\ldots,n$. Join $i$ to $P_i$; ignore orientation and repetitions but regard a loop as forbidding occupation of its vertex. Let $A$ be the event that every vertex reaches vertex 1 along the parent arrows. Every labeled tree has exactly one suitable orientation, so $\Pr(A)=n^{n-2}/n^{n-1}=1/n$. Conditional on $A$ the graph has exactly the law of $T_n$.

For every outcome, including those outside $A$, let $H(t)$ be the log partition function of the resulting graph. Changing $P_i$ leaves the same graph after deleting $i$. If $B$ is that common subgraph's partition function, the contribution from sets omitting $i$ is $B$, while that from sets containing $i$ lies in $[0,e^tB]$: deleting $i$ gives an injection with weight ratio $e^t$. Hence changing one coordinate alters $H(t)$ by at most $L_t=\log(1+e^t)$, even with loops or repeated edges.

Put $b_n(t)=\mathbb EH(t)/n$ under the *unrestricted* independent choices. Bounded differences, followed by conditioning, gives
$$
\Pr\left(\left|H(t)/n-b_n(t)\right|>u\mid A\right)
\le 2n\exp\left(-\frac{2n^2u^2}{(n-1)L_t^2}\right).
$$
Section 1 already gives convergence under $A$ to $p(t)$, so $b_n(t)\to p(t)$: otherwise disjoint fixed-radius neighborhoods would both have conditional probability tending to one on a subsequence. Thus for fixed $u>0,t$ and large $n$, the probability that $|n^{-1}\log Z_{T_n}(t)-p(t)|>u$ is at most $e^{-c(t,u)n}$, using the last display with $u/2$. No rate for the deterministic bias is required.

## 3. Two tilts force all modes

Fix $\varepsilon>0$. By differentiability choose $h>0$ such that $p(h)-p(0)\le h(\mu+\varepsilon/2)$ and $p(-h)-p(0)\le-h(\mu-\varepsilon/2)$. Except on a set of trees of probability at most $e^{-c_\varepsilon n}$, the three log partition functions per vertex at $0,h,-h$ are each within $h\varepsilon/8$ of their limits; reduce $c_\varepsilon$ to absorb the finite union for large $n$.

Conditional on such a tree, let $X$ be the size of a uniformly sampled independent set. Its conditional exponential moments at $\pm h$ are exactly $Z_T(\pm h)/Z_T(0)$. Markov's inequality bounds each tail beyond $(\mu\pm\varepsilon)n$ by $\exp(-h\varepsilon n/4)$. Every modal atom has probability at least $1/(n+1)$ by pigeonholing. For large $n$ it cannot lie in either tail; this proves (1). The same argument and $0\le X/n\le1$ give $\mathbb E[X/n]\to\mu$ in the two-stage experiment.

## 4. A finite rational enclosure, using the other root limit

By symmetry $\mathbb E[X/n]$ is the probability that vertex 1 is occupied. The fixed-depth neighborhood of that root in the conditioned Poisson tree tends in distribution to the neighborhood of the root of its size-biased Kesten tree (Janson, Theorem 7.1 and Example 10.2). Each spine vertex has one spine child and an independent Poisson(1) number of ordinary children. Ordinary vertices have Poisson(1) ordinary children, and the side subtrees are independent. This is a **whole-root-neighborhood** limit, not the descendant-subtree limit of Section 1.

At $\lambda=1$ all finite-tree odds lie in $[0,1]$. Fix a cutoff depth $h$. Bound the root odds by assigning extreme odds at the cutoff and alternating their order at each level, since (2) decreases in each child. Leaves above the cutoff have odds 1. These bounded endpoint functions depend only on the depth-$h$ neighborhood, so their expectations, also after applying the increasing function $x/(1+x)$, converge to the expectations on the Kesten tree. Hence the latter two expectations bound $\mu$ without any assumption on an infinite-tree Gibbs state.

Here is the [exact enclosure algorithm](interval.py). Odds are multiples of $1/K$ and probabilities multiples of $1/M$; initially take $K=400$, $M=10^{12}$. Bounds are in stochastic order: expectations of increasing tests are ordered.

1. To divide independent ordinates $X/(1+Y)$, use the lower law of $X$ and upper law of $Y$ for a lower bound, the reverse for an upper bound. At grid indices $(i,j)$, multiply their probabilities and round the output index $iK/(K+j)$ down or up as appropriate. Round each bin probability down to a multiple of $1/M$ and move the missing mass to 0 for a lower bound, 1 for an upper bound. The rounding therefore preserves stochastic order.
2. For each ordinary offspring count $d\le10$, start from odds 1 and perform $d$ independent divisions with the child law. For the lower product use upper child odds, and conversely. Keep mixture weight $e_-/d!$, where $e_-=\sum_{j=0}^{15}(-1)^j/j!$ lies in $[0,e^{-1}]$ by the alternating series. Round the mixed bin masses down and put all omitted mass, including the degrees $d>10$, at the safe endpoint. Conditional independence and stochastic order justify both the product and the completion.
3. For the spine root, divide an independently formed ordinary product by 1 plus the old distinguished-child odds, again taking opposite bounds for that child. Initially, at height zero, both types have lower odds 0 and upper odds 1. By induction these steps enclose the depth-$h$ endpoints. At $h=12$ the exact expectations of $x/(1+x)$ under the two grid spine laws, rounded outwards to millionths, give $[0.304684,0.307543]$. [A finer grid](ANNEALED.md) gives the advertised narrower interval.

The limiting maximum independent-set fraction is the root $\rho$ of $\rho e^\rho=1$ (Meir–Moon; Pittel). In particular $\mu>\rho/2$: $\rho<0.6$ since $0.6(1+0.6+0.6^2/2)>1$, whereas $\mu>0.304$. This distinguishes the modal size from half the asymptotic maximum size; it is not a correction to a theorem about the maximum.
