# An annealed-to-typical transition for independent-set counts on uniform labeled trees

**Theorem.** Let $T_n$ be a uniformly chosen tree on $[n]$, $X=i_k(T_n)$ the number of independent sets of size $k=k(n)$, and $Y=X/\mathbb EX$, $1\le k\le n-1$. Our randomness is only the tree. Then:

1. For $k=o(n^{5/6})$, $Y\to1$ in $L^2$.
2. For $k/n^{5/6}\to t\in(0,\infty)$, put $s=t^3/\sqrt2$. Then $Y\Rightarrow \exp(sZ-s^2/2)$, $Z\sim N(0,1)$, and $\mathbb EY^2\to e^{s^2}$. More precisely the standardized tree degree-collision statistic below and $Y$ converge jointly to $(Z,e^{sZ-s^2/2})$.
3. For $k/n^{5/6}\to\infty$ (including any $k\le n-1$ arbitrarily close to $n$), $Y\to0$ in probability despite $\mathbb EY=1$. Hence $\mathbb EY^2\to\infty$; neither a typical-value formula in this region nor an extinction threshold is asserted.

There is a different, smaller scale for comparison to the *path*: if $k/n^{2/3}\to u\ge0$, then $X/i_k(P_n)\to e^{u^3/2}$ in $L^2$. Do not confuse the two normalizations.

## 1. Two planted sets and an exact second moment

Put $a=k/n$, $m=n-k$, $M=k^2/n$. The probability a fixed $k$-set is independent is $(1-a)^{k-1}$ by the classical Bedrosian formula, so $\mathbb EX=\binom nk(1-a)^{k-1}$. Assume $2k<n$ in this section (sufficient through the critical window). For fixed $k$-sets with overlap $j$, put $q=k-j$ and $o=n-2k+j$. The graph of allowed tree edges has four vertex classes: intersection $(j)$, first-only $(q)$, second-only $(q)$, outside $(o)$. Each intersection vertex is adjacent precisely to all outside vertices; each exclusive vertex is adjacent to outside and opposite-exclusive vertices. The outside is a clique adjacent to all.

For $0<j<k$ the within-class zero-sum Laplacian eigenvalues are $o$ with multiplicity $j-1$, $m$ with multiplicity $2(q-1)$, and $n$ with multiplicity $o-1$. The class-constant subspace adds $0,n,o,n-j$: the exclusive antisymmetric mode has eigenvalue $o+2q=n-j$; restricting the two exclusive values to be equal leaves one mode of eigenvalue $o$ (outside value zero, weighted interior mean zero), and the bipartition outside/inside contrast has eigenvalue $n$. Kirchhoff's tree formula divided by the Cayley count now yields
$$
\Pr(\text{both independent})=(1-2a+j/n)^j(1-a)^{2(k-j-1)}(1-j/n).
$$
For $j=k$ this is the one-set formula; for $j=0$ remove the empty intersection class and its $o$ quotient mode, leaving eigenvalues $0,n,n$ on class constants (the exclusive antisymmetric and outside/inside contrasts). The formula persists. Thus, for $J$ hypergeometric (overlap of two independent uniformly random $k$-subsets),
$$
\mathbb E Y^2=\mathbb E g(J),\quad
g(j)=(1-j/n)\left(1+\frac{j-M}{D}\right)^j,qquad D=n(1-a)^2.\tag{1}
$$
Basit and Galvin explicitly point out the matrix-tree route to this variance and that it is often large. The method of computing the finite second moment is prior, not the distinguishing claim.

## 2. Limit and uniform integrability at and below the window

Consider $k/n^{5/6}\to t\ge0$ finite, so $a=o(1)$. Write $V=J-M$ and recall $\operatorname{Var}J=M(1-a)^2 n/(n-1)$. When $M\to\infty$, the hypergeometric CLT gives $V/\sqrt M\Rightarrow Z$ (the usual diverging-variance condition). In particular $V=O_{\mathbb P}(\sqrt M)$. Expanding the logarithm in (1),
$$\log g(J)=\frac{M V}{D}+o_{\mathbb P}(1)\Rightarrow t^3 Z.$$
Indeed $J/n\to0$ and $V^2/D=O_{\mathbb P}(M/n)=o(1)$, while $J V^2/D^2=O_{\mathbb P}(M^2/n^2)=o(1)$; $M^{3/2}/D\to t^3$. If $M$ stays bounded then $J$ is tight by Markov and $g(J)\to1$ in probability.

To justify moment convergence, for every $b\ge0$ the hypergeometric factorial moments satisfy $\mathbb E(J)_r=(k)_r^2/(n)_r\le M^r$ (since $(k-i)/(n-i)\le k/n$). Thus
$$\mathbb E e^{b(J-M)}\le\exp\{M(e^b-1-b)\},\qquad
\Pr(J\ge h)\le (eM/h)^h\quad(h\in\mathbb N).$$
When $M\to\infty$, take a split at $B=4eM$. For $J\le B$ with $V\ge0$, $\log g(J)\le J V/D\le C V/\sqrt M$, because $M^{3/2}/D$ stays bounded. With $V\le0$ the integrand is at most 1. The exponential-moment bound at $2C/\sqrt M$ gives bounded second moments on the first region. On $J=j>B$, $g(j)^2\le\exp(2kj/D)$, and $\Pr(J=j)\le 4^{-j}$. Since $k/D=o(1)$, the sum of these tail bounds tends to zero. If $M$ is bounded then $g(j)^2\le\exp(2kj/D)$ everywhere and the same factorial-moment bound gives a uniform second moment directly. Subsequences of $M$ handle all cases. Therefore $\mathbb E Y^2\to\exp(t^6/2)$. At $t=0$ this gives $\mathbb E(Y-1)^2\to0$. At $t>0$ it is only a second-moment limit; it does **not** itself identify the law of $Y$.

## 3. A degree statistic under ordinary and planted tree laws

Let $\mathbb P$ be the ordinary Cayley law. Let $\mathbb Q$ first choose a uniform $k$-set and then choose a uniform tree making it independent, forgetting the set afterwards. Every $k$-set has the same probability of being independent under $\mathbb P$. Hence
$$d\mathbb Q/d\mathbb P=Y.$$
For the symmetric statistic $W=\sum_v\binom{\deg_T(v)-1}{2}$, its $\mathbb Q$-law can be computed with any one fixed planted set. Under $\mathbb P$ the Prüfer multiplicities $\deg_T(v)-1$ are occupancy counts of $n-2$ iid uniform labels, so $W$ counts equal unordered pairs.

Under planting the tree is a uniform spanning tree of the complete split graph with $k$ independent and $m=n-k$ outside vertices. Its classical weighted tree enumerator, divided by $\prod x_i$, is
$$\left(\sum_{i=1}^n x_i\right)^{m-1}\left(\sum_{i\ \mathrm{outside}}x_i\right)^{k-1}.$$
This is Martin–Reiner's Theorem 4 specialized to the split threshold graph (order the outside first); the degrees are $(n-1)^m,m^k$, so their conjugate partition is $n$ up to index $m$ and $m$ thereafter through $n-1$. Normalizing at all $x_i=1$ shows the degree-minus-one vector has the occupancy law from $U=m-1$ independent unrestricted uniform draws and $R=k-1$ independent uniform draws on the $m$ outside labels, independent of the first group. It is an equality of multiplicity laws, not a claim that ordinary Prüfer words conditional on independence have the restricted draws in specified positions.

Consequently
$$
w_0:=\mathbb E_P W=\binom{n-2}2/n,\qquad
\Delta:=\mathbb E_Q W-w_0=\binom{k-1}2\frac{k}{nm}.\tag{2}
$$
Indeed a restricted/restricted pair collides with probability $1/m$, while every other pair has probability $1/n$. Distinct collision indicators for disjoint pairs are independent. For two pairs sharing an index, condition on its label: each probability of matching an unrestricted opposite draw is constant $1/n$; the probability of matching a restricted opposite draw is $\mathbf1_{\mathrm{outside}}/m$. Hence covariance is zero unless a shared unrestricted draw has two restricted opposite draws, in which case it is $k/(n^2m)$. This gives
$$
\operatorname{Var}_P W=\binom{n-2}2 n^{-1}(1-1/n),\qquad
\operatorname{Var}_Q W\le C(n+k^2/m).
$$
For detail, the diagonal variances are bounded by their means, $O(n+k^2/m)$, and the ordered off-diagonal covariance sum is at most $U R(R-1)k/(n^2m)\le k^3/n^2\le n$. For the sum restricted to pairs involving at least one restricted draw, the bound is $O(k+k^2/m+k^3/n^2)$ by the same count. These bounds include $m=1$, when the restricted labels are identical deterministically.

Here is an elementary CLT for the unrestricted collision count $C_L$ among $L\sim n$ independent uniform draws into $n$ bins. Let $C_j$ denote the prefix collision count. The centered martingale differences are $D_j=C_j-C_{j-1}-(j-1)/n$. Conditional on the previous draws their variance is $(j-1+2C_{j-1})/n-((j-1)/n)^2$, by summing squared occupancies. The sum of their expected variances equals $\operatorname{Var}(C_L)=\binom L2(1-1/n)/n\sim n/2$, since different pair indicators are uncorrelated. The $L^2$-norm of the difference between the sum of their conditional variances and this expectation is at most $2n^{-1}\sum_{j\le L}\sqrt{\operatorname{Var}(C_{j-1})}=O(\sqrt n)$. Unconditionally $C_j-C_{j-1}$ is binomial $(j-1,1/n)$, hence $\sup_j\mathbb E D_j^4=O(1)$. These verify the variance and Lindeberg conditions for the martingale CLT with scaling $\sqrt{n/2}$: the expected normalized quadratic Lindeberg tail is bounded by $O(n^{-2})\sum_j\mathbb E D_j^4=o(1)$ for a fixed positive cutoff. Thus $(C_L-\mathbb E C_L)/\sqrt{n/2}\Rightarrow Z$.

Let $D_n=(W-w_0)/\sqrt{n/2}$. Under $\mathbb P$ it tends to $Z$. If $k/n^{5/6}\to t\in(0,\infty)$, $U\sim n$ and the variance of the contribution of pairs involving restricted draws is $o(n)$. Applying the unrestricted CLT to $C_U$, adding the remaining centered contribution and using (2) yields $D_n\Rightarrow Z+s$ under $\mathbb Q$ with $s=t^3/\sqrt2$. No independence of the two centered contributions is required.

## 4. Matching the likelihood at criticality; separation above it

Write $h(z)=\exp(sz-s^2/2)$ so that $h$ is the density of $Z+s$ relative to $Z$. For fixed $B>0$ let $h_B=\min(h,B)$. The planted CLT yields
$$\mathbb E_P[Yh_B(D_n)]=\mathbb E_Q h_B(D_n)\to\mathbb E[h(Z)h_B(Z)].$$
The ordinary CLT gives $\mathbb E_P h_B(D_n)^2\to\mathbb E h_B(Z)^2$. Since $\mathbb E_P Y^2\to e^{s^2}=\mathbb E h(Z)^2$, expanding the squared difference gives
$$\lim_{B\to\infty}\lim_{n\to\infty}\mathbb E_P|Y-h_B(D_n)|^2=0.$$
Together with the ordinary CLT this implies the claimed joint limit by approximation (e.g. test bounded Lipschitz functions of both variables). We do not replace $h_B(D_n)$ by $h(D_n)$ in an untruncated exponential moment. This norm matching is a one-coordinate version of the Gaussian conditioning argument of Banerjee–Ma, Proposition 1.

If $k/n^{5/6}\to\infty$, then $\Delta/\sqrt n\to\infty$ by (2), since $m\le n$. Also $(k^2/m)/\Delta^2=O(n^2m/k^4)=o(1)$. Both variances above are thus $o(\Delta^2)$. For $H=\{W\le w_0+\Delta/2\}$, Chebyshev gives $\mathbb P(H)\to1$, $\mathbb Q(H)\to0$. For each $\eta>0$, $\mathbb P(Y>\eta)\le\mathbb P(H^c)+\mathbb Q(H)/\eta\to0$. This proves collapse throughout the full supercritical interval; no second moment in the large-density regime is needed. Also $\mathbb E_PY^2\ge\mathbb Q(H^c)^2/\mathbb P(H^c)\to\infty$.

## 5. The distinct path-comparison window

For $k=o(n)$ the path coefficient is positive. Cancellation in the classical Bedrosian expectation gives
$$\frac{\mathbb E X}{i_k(P_n)}
=\frac{\binom nk(1-k/n)^{k-1}}{\binom{n-k+1}{k}}
=\prod_{j=0}^{k-2}\left(1+\frac{kj}{n(n-k-j)}\right).$$
For $k/n^{2/3}\to u<\infty$, the largest term added to one is $O(k^2/n^2)=o(1)$ and their sum is $(1+O(k/n))k(k-1)(k-2)/(2n^2)\to u^3/2$ (empty products at small $k$). Thus the deterministic ratio tends to $e^{u^3/2}$ and part 1 yields the asserted $L^2$ limit. This finite critical-factor statement is not a positive exponential-in-$n$ gain at sublinear $k$.

## 6. Primary sources and scope

* [Basit–Galvin, *On the Independent Set Sequence of a Tree*, EJC (2021)](https://doi.org/10.37236/9896), [author copy](https://academicweb.nd.edu/~dgalvin1/pdf/journal/random_trees_J.pdf), specifically note the matrix-tree variance calculation and its large size; [Heilman, JGT (2025)](https://doi.org/10.1002/jgt.23225) studies ordinary/planted comparisons for this very tree and statistic and credits Bedrosian's exact one-set formula. We do not claim the model, first moment, or use of matrix-tree for a second moment is new. Wingard's minimum path count and the recent macroscopic multiplicative gap concern a different normalization.
* [Martin–Reiner, *Factorizations of some weighted spanning tree enumerators*, Theorem 4](https://arxiv.org/abs/math/0302213) already gives the planted degree generating polynomial used here; [Lewis, *The number of spanning trees of a complete multipartite graph*](https://www.sciencedirect.com/science/article/pii/S0012365X99901115) provides earlier degree-aware multipartite Prüfer enumeration. The planted degree law is thus an application of those formulas.
* [Lahiri–Chatterjee–Maiti](https://www.sciencedirect.com/science/article/pii/S0378375807001188) cover normal approximation of the hypergeometric law including sparse sampling with diverging variance. [Banerjee–Ma, *Asymptotic normality and analysis of variance of log-likelihood ratios in spiked random matrix models*](https://arxiv.org/abs/1804.00567), Proposition 1, formalize Gaussian conditioning via shifted Gaussian limits and second moment matching. We give its elementary bounded-test case, not a new conditioning principle.
* Distinct random variables: the expectation-normalized count at a prescribed $k$, largest feasible size, conditional sample size, and the maximizing index of the coefficient sequence are not interchangeable. The convergence results are for any specified sequence $k(n)$ in the stated ranges; no uniform simultaneous random profile, convergence of lognormal higher moments, or supercritical rate is asserted. A limited search for existing exact threshold/lognormal statements cannot guarantee priority.
