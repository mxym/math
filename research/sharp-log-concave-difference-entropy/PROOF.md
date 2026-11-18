# The entropy of a difference on the integers and on the real line

**AI-assisted research draft, independently reviewed within the project by AI; no external peer review or priority claim.** The relevant questions are [Han–Zhan–Zhou–Zhu, §VIII-A (61) and §VIII-B (63)](https://arxiv.org/html/2610.15716v1). We obtain the exact discrete Shannon entropy constant for a difference, in fact all positive Rényi orders, and the exact continuous constant and its maximizers in dimension one for orders below one. This does not resolve the folklore positive-sum conjecture, the two-different-law question (60), or higher-dimensional orders below one. We use natural logarithms.

**Proof route.** First compare the difference’s mass in an interval of length twice that of a chosen input interval. On the lattice the interval must contain exactly $2k$ sites; keeping one boundary atom instead of both matters. Next turn this comparison into inequalities for *all* ranked partial sums. Finally read off the Rényi entropies using integrals of the mass above each threshold. The continuous proof uses the same comparison with superlevel intervals in place of ranked lists.

For a mass function $w$, write $H_\alpha(w)=(1-\alpha)^{-1}\log\sum_i w_i^\alpha$ for finite $\alpha>0$, $\alpha\ne1$; $H_1(w)=-\sum_i w_i\log w_i$, $H_\infty(w)=-\log\max_i w_i$. For densities use integrals and the essential supremum, denoting the entropies by $h_\alpha$.

## 1. Lattice theorem

Let $X,X'$ be independent with common probability mass function $p_i$ on $\mathbb Z$; its positive support is a nonempty interval of consecutive integers, possibly unbounded in one or both directions, and $p_i^2\ge p_{i-1}p_{i+1}$. Let $D=X'-X$ have masses $g_d=\sum_i p_i p_{i+d}$. Form the comparison sequence $b$ on $\mathbb Z\times\{0,1\}$ with $b_{i,0}=b_{i,1}=p_i/2$. Then **$g$ majorizes $b$**: for every rank $r\ge1$, the $r$ largest masses of $g$ have at least the sum of the $r$ largest masses of $b$. Zero entries may be appended to finite lists. Consequently
$$H_\alpha(D)< H_\alpha(X)+\log2\qquad(0<\alpha\le\infty).$$
For every stated $\alpha$, the constant $\log2$ is optimal; no pmf attains it. If $\alpha=0$ and the support has $N<\infty$ points, the difference support has $2N-1$ points; no finite difference of Hartley entropies is claimed for infinite support. This endpoint is elementary and known.

### The overlap calculation

For $k\ge1$ fix $q_i=p_{i+k}$. For $i<j$,
$$p_i q_j\le q_i p_j.$$
Indeed, if the left side is positive, $i,j+k$ lie in the interval support and so do $i+k,j$. The increments of $\log p$ on that interval are nonincreasing, hence $\log p_{i+k}-\log p_i\ge\log p_{j+k}-\log p_j$; if the left side vanishes the claim is automatic. No division by an endpoint zero is needed.

The overlap of $p\otimes q$ and $q\otimes p$ is no greater than that of their first marginals: sum $\min(p_iq_j,q_i p_j)$ over $j$ first, and bound by $\min(p_i,q_i)$. By the sign rule, symmetry in the two coordinate indices, and independence,
$$\begin{aligned}
2\Pr(D>k)+\Pr(D=k)
 &=2\sum_{i<j}p_i p_{j+k}+\sum_i p_i p_{i+k}\\
 &=\sum_{i,j}\min(p_iq_j,q_i p_j)
 \le\sum_i\min(p_i,q_i).
\end{aligned}$$
Since $g_{-d}=g_d$, the complementary mass on the left is exactly $\Pr(-k<D\le k)$, on **$2k$** consecutive lattice sites (the choice of which boundary atom to retain is immaterial).

The complement of the overlap on the right is the total variation of $p,q$, which is at least the difference on any half-line. For $F(i)=\sum_{j\le i}p_j$,
$$1-\sum_i\min(p_i,q_i)\ge F(a+k)-F(a)=\Pr(a<X\le a+k).$$
It follows that
$$\Pr(-k<D\le k)\ge \sup_{a\in\mathbb Z}\Pr(a<X\le a+k). \tag{1}$$
A log-concave sequence is unimodal. Its $k$ largest masses can be selected in a single interval of length $k$: start at a mode and repeatedly append whichever of the two adjacent masses is larger (choose either in a tie, and append zeros when needed). An $\ell^1$ positive sequence has a mode and tends to zero on each infinite tail. Thus the right side is the sum of the $k$ largest masses of $p$. In particular no log-concavity assumption on $g$ is needed.

Let $A(r)$ denote the sum of the $r$ largest masses of $g$, and $B(r)$ the corresponding sum for $b$, with $A(0)=B(0)=0$. Inequality (1) gives $A(2k)\ge B(2k)$ for all $k\ge1$. The increments of $A$ decrease while the increments of $B$ come in equal pairs, so
$$A(2k+1)\ge [A(2k)+A(2k+2)]/2\ge [B(2k)+B(2k+2)]/2=B(2k+1)$$
also for $k=0$. Both sequences have total mass 1. At rank one the inequality is strict: (1) at $k=1$ gives $g_0+g_1\ge \max_i p_i$ and
$$g_0-g_1=\tfrac12\sum_i(p_i-p_{i+1})^2>0$$
because a nonzero summable sequence cannot be invariant under the unit shift. Hence $\max g\ge g_0>\max b$.

### From concentration to entropy

For any mass sequence $w$ let $J_w(t)=\sum_i(w_i-t)_+$, with $(v)_+=\max(v,0)$. For $t>0$, $J_w(t)=\max_{r\ge0}(S_w(r)-rt)$, where $S_w$ is its ranked prefix sum. Thus $J_g\ge J_b$, strictly on the open interval $(\max b,\max g)$. Equivalently $K_g(t)\le K_b(t)$ there and throughout $t>0$, where $K_w=\sum_i\min(w_i,t)=1-J_w$. Strictness on this interval suffices for every finite positive order. For $0<\alpha<1$, integrate $K$ against $\alpha(1-\alpha)t^{\alpha-2}\,dt$ to obtain $\sum w_i^\alpha$, using the same scalar identity for $\min(u,t)$ and Tonelli. For $\alpha>1$, integrate $J$ against $\alpha(\alpha-1)t^{\alpha-2}\,dt$ to obtain the same power sum; the factor $1/(1-\alpha)$ reverses the comparison. For Shannon entropy use
$$-u\log u=\int_0^1[\min(u,t)-ut ]dt/t,\quad 0\le u\le1,$$
whose integrand is nonnegative. Summing gives $H(w)=\int_0^1 [K_w(t)-t]dt/t$. The order $\infty$ claim is the strict maximum comparison above. Since $b$ is an independent fair-bit split of $p$, $H_\alpha(b)=H_\alpha(p)+\log2$ for every order.

All entropies involved are finite. Indeed on each unbounded tail there is a strictly decreasing step outward (summability), so log-concavity bounds that tail by a geometric sequence. Therefore $p_i\le C e^{-c|i|}$ everywhere for some $C,c>0$. Then $g_d\le C^2 e^{-c|d|/2}\sum_i e^{-c|i|/2}$, by the triangle inequality applied to half the exponent and dropping the remaining $e^{-c|i+d|/2}$. Such envelopes give all positive power integrals and absolute integrability of $w\log w$.

Sharpness is the known one-sided geometric limit: for $p_j=(1-q)q^j$ on $j\ge0$, $g_d=(1-q)q^{|d|}/(1+q)$. For $\alpha\ne1,\infty$ the ratio of the power sums for $g$ and $p$ is $(1+q^\alpha)/(1+q)^\alpha\to2^{1-\alpha}$ as $q\uparrow1$. At Shannon order the difference is $\log(1+q)-q\log q/(1+q)\to\log2$ (as recorded in the source question); the min-entropy difference is $\log(1+q)$. 

## 2. Continuous line and the subunit-order question

Let $X,X'$ be iid on $\mathbb R$ with log-concave probability density $f$, and let $g$ be the density of $X'-X$. Write $b(x)=f(x/2)/2$, the density of $2X$. For every $h>0$ the same overlap calculation, now using $q(x)=f(x+h)$ and integration in $x,y$, gives
$$2\Pr(X'-X>h)=\iint\min(f(x)q(y),q(x)f(y))\,dx\,dy\le\int\min(f(x),q(x))\,dx.$$
Indeed the sign rule for $x<y$ follows from the decreasing $h$-increments of the concave $\log f$ on its interval of support, again handling outside-support zeros directly; the diagonal is Lebesgue-null. Total variation tested on a half-line gives
$$\Pr(|X'-X|\le h)\ge\sup_a\Pr(a<X\le a+h). \tag{2}$$
There are no endpoint atoms. This implies $J_g(t)\ge J_b(t)$, where now $J_w(t)=\int(w-t)_+$. To see it directly, $I_t=\{b>t\}$ is an interval of finite length $2h$ for $t>0$ (if it has zero length the result is immediate). Its $b$ mass equals the $f$ mass of $I_t/2$, an interval of length $h$. By (2), the interval $[-h,h]$ has at least the same $g$ mass. Subtract $2ht$ and then maximize on the $g$ side by integrating its positive part. This argument avoids any regularity of the superlevel boundaries or assumed symmetry of $f$.

The integral version of the identities in Section 1 gives $h_\alpha(g)\le h_\alpha(f)+\log2$ for $0<\alpha<\infty$. For Shannon, after choosing common units to make both $g$ and $b$ bounded by 1, apply the same identity; changing units back adds the same constant to both entropies. The essential maximum comparison follows from the $J$ comparison. An integrable full-dimensional log-concave density on the line is bounded and has at least exponential tail decay: choose two points on each unbounded tail where the later value outward is strictly smaller, and extend their slope as an upper bound for $\log f$ by concavity. Boundedness on bounded portions follows from a supporting line at any interior point. The convolution envelope and finiteness argument carry over with integrals.

For $X$ standard exponential, $g(x)=e^{-|x|}/2$, whereas $b(x)=e^{-x/2}\mathbf1_{x\ge0}/2$. Their positive superlevel sets have equal lengths, so all claimed entropy gaps are exactly $\log2$. This proves **$C_{1,\alpha}=\log2$ for every $0<\alpha<1$** in (61). If a subunit-order equality holds then the nonnegative difference $J_g(t)-J_b(t)$ has zero integral against a strictly positive weight on $t>0$, hence is zero almost everywhere. It is continuous on each compact subinterval of $(0,\infty)$ by dominated convergence (dominate $(w-t)_+$ by $w$), hence zero everywhere. This implies Shannon equality by the same identities. [Han et al., Theorem 4](https://arxiv.org/html/2610.15716v1) therefore gives that $X$ is an affine image with nonzero scale of a one-sided exponential variable. Conversely every such affine image attains equality. **The classification uses their prior theorem.**

## 3. Prior-art and scope cautions

* [Han–Zhan–Zhou–Zhu, arXiv:2610.15716v1](https://arxiv.org/html/2610.15716v1), §VIII-B, explicitly ask (63), crediting Jiange Li in their acknowledgments with suggesting the integer-valued and positive-sum directions, with their integer-valued definition requiring an interval support but not monotonicity. They give the geometric lower-bound sequence. For continuous laws they already prove all dimensions and $1\le\alpha\le\infty$ (Thm. 3), classify finite-order equality for $\alpha\ge1$ (Thm. 4), and show that $\log2$ per coordinate fails in high dimension for every fixed $\alpha<1$ (Thm. 5). Their §VIII-A Eq. (61) asks for the subunit-order optimum at a fixed dimension. The present continuous contribution, if not covered elsewhere, is exactly the dimension-one, unweighted difference case and its maximizers.
* [Melbourne–Tkocz, §VI, Theorems 6.1/6.2](https://arxiv.org/pdf/2005.10930) give continuous high-order sharp bounds, prove weaker discrete bounds generally, and already have sharp discrete endpoints $2,\infty$ and support order 0. Their geometric limit establishes sharpness from below at every positive order. Their comment after (52) notes earlier positive-sum comparisons for symmetric continuous inputs; our formula includes skew/asymmetric laws and should not be described as new on that subclass.
* [Melbourne–Palafox-Castillo, Theorem 2.11](https://arxiv.org/pdf/2111.06997) give the sharp discrete upper bound for monotone log-concave masses at orders $\alpha\ge2$, not the unrestricted discrete Shannon statement. [Fu–Li, Nov 9, 2026 v4, §4](https://arxiv.org/html/2510.09206v4) treat principally the positive sum, the unrestricted discrete order two (also the same for a difference), and monotone discrete min-entropy for positive sums, not the present Shannon theorem. In particular do not attribute the geometric sharpness limit or the endpoints to this work.
* The pivotal statistical inequality is a standard consequence of total-variation contraction under projection and likelihood-ratio ordering; there is **no claim to invent it**. In ROC language it compares a one-threshold rule with discrimination between two observations in random order; see [Zhang–Mueller (2005)](https://doi.org/10.1007/s11336-003-1119-8) and the explicit triangle bound in [Bandos–Rockette–Gur (2010), Appendix (A2)](https://pmc.ncbi.nlm.nih.gov/articles/PMC2980542/); see also [Mueller and Zhang, ROCML 2006](https://sites.lsa.umich.edu/m3lab/wp-content/uploads/sites/1376/2024/11/2006-Mueller-and-Zhang-ICML-proceedings.pdf). Here we use that statistical comparison to turn translations into concentration and entropy bounds for $X-X'$. The [companion audit](REVIEW.md) gives the exact threshold interpretation, including the treatment of lattice ties. The [search record](SEARCH.md) does not certify priority.
* Neither (60) for independent *different* laws nor (62) for positive sums follows. No assertion in $\mathbb Z^d$ or on the continuum in $d\ge2$. No uniqueness of discrete near-extremizers is asserted.
