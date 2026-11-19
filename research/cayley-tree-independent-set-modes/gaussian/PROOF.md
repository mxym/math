# A Gaussian law for the modal index of a uniform Cayley tree

Let $T_n$ be the uniform tree on $[n]$. Let $I$ given $T_n$ be uniform among all its independent vertex subsets, including the empty one, and $A(T)=\mathbb E(|I|\mid T)$. Write $\mathcal M(T)$ for all global coefficient modes and $\mu$ for the deterministic center of the [preceding linear-scale theorem](../PROOF.md). The random variable $A(T_n)$ is a statistic of the sampled **tree**, not an extra sample of $I$.

**Theorem.** There exists $\sigma^2\ge e^{-10}/216>0$ such that
$$
\frac{\operatorname{Var} A(T_n)}n\to\sigma^2,
\qquad \frac{A(T_n)-\mu n}{\sqrt n}\Rightarrow N(0,\sigma^2).
$$
For every choice $M_n\in\mathcal M(T_n)$, even a randomized tie choice, $(M_n-\mu n)/\sqrt n$ has this same limit and $\operatorname{Var}(M_n)/n\to\sigma^2$. In fact all rescaled modes are a deterministic $o(1)$ apart from the rescaled $A(T_n)$. This is a tree-to-tree CLT, not the within-one-tree CLT of Fang et al. There is no local limit theorem, convergence rate, or numerically precise limiting variance asserted.

## 1. A variance estimate for approximating local scores

Use the rigorously established estimates of the [square-root proof](../square-root/PROOF.md), (S1)–(S3). In particular the size $t=|B_h(1)|$ of the whole undirected ball has every fixed moment bounded by a polynomial in $1+h$ uniformly in $n$, both on Cayley trees and on the Poisson Kesten limit. If a possibly signed function on a rooted ball satisfies $|f(B_h)|\le |B_h|$, then with $S_f(T_n)=\sum_v f(B_h(v))$ we have
$$
n^{-1/2}\|S_f-\mathbb E S_f\|_2\le C(1+h)^a.\tag{C1}
$$
Indeed, the one- and two-root versions of (S3) bound $|\mathbb E f_1-\mathbb E_K f|$ and $|\mathbb E(f_1 f_2)-(\mathbb E_K f)^2|$ by a polynomial divided by $n$ for distinct fixed labels. Both individual means grow at most polynomially, so $|\operatorname{Cov}(f_1,f_2)|$ also obeys such a bound. Exchangeability and the diagonal second moment finish. Neither exponent nor multiplicative constant in (C1) depends on $h,n$ or $f$.

Recall the empty-boundary occupation approximants $H_h\in[0,1]$, $H_0=0$, with increments $|H_h-H_{h-1}|\le (\log2)2^{1-h}|B_h|$. On the finite tree they telescope to the exact single-vertex occupation. Hence (C1) and the triangle inequality in centered $L^2$ give
$$
\sup_n n^{-1/2}\|[A-S_{H_h}]-\mathbb E[A-S_{H_h}]\|_2
   \le C'\sum_{j>h}2^{-j}(1+j)^a\longrightarrow0.\tag{C2}
$$
There is no issue with the sum to infinity: for a fixed tree all increments beyond $n$ vanish, and the displayed bound is summable uniformly. Write $F_{h,K}=H_h\mathbf 1_{\{|B_h|\le K\}}$. The discarded score satisfies $K|H_h-F_{h,K}|\le |B_h|$. Thus replacing $S_{H_h}$ with $S_{F_{h,K}}$ costs at most $C(1+h)^a/K$ in the same norm. These centered estimates, not merely a per-vertex probability bound, control the fluctuations.

## 2. Turning an undirected ball test into a descendant-subtree functional

Fix $h\ge1$ and $K$. Temporarily root at vertex 1 and order children uniformly: on forgetting the labels the result is the conditioned Poisson(1) Galton–Watson tree. For a rooted descendant tree $U$, define the toll
$$
g(U)=\sum_{v:\,\mathrm{dist}_U(v,\mathrm{root})=h} F_{h,K}(B_h^U(v)).
$$
Only the first $2h$ levels of $U$ are needed. When $v$ has depth at least $h$ in the original rooted tree, its unique $h$th ancestor $a$ is at the boundary of its ball. The full ball of $v$ agrees with its ball inside the descendant subtree at $a$: any path leaving the latter first traverses the edge above $a$, at distance $h+1$. Therefore $G(T)=\sum_a g(T_a)$ differs from $S_{F_{h,K}}$ only by the contributions of vertices at depth less than $h$. Their absolute sum is at most $|B_{h-1}(1)|$. For fixed $h$ this error has bounded $L^2$ norm, uniformly in $n$.

The count of eligible descendants at depth $h$ is at most $\deg_U(\mathrm{root})K^{h-1}$. Given a first child, each path prefix leading to an eligible endpoint branches at most $K$ ways: each internal vertex on the prefix is at distance strictly less than $h$ from that endpoint and thus has all its own neighbors in the size-at-most-$K$ ball. At a prefix with no eligible endpoints no bound on its actual degree is needed. This also handles $h=1$ and a root with any number of children. Hence $|g(U)|\le K^{h-1}\deg_U(\mathrm{root})$ for every $U$, including a leaf.

Apply Ralaivaosaona–Šileikis–Wagner (RSW), *A Central Limit Theorem for Almost Local Additive Tree Functionals*, [Theorem 1](https://arxiv.org/pdf/1810.00467). With exponent $\alpha=1$, Poisson offspring satisfies all moment hypotheses. To spell out (3)–(5), the two cutoff errors vanish past depth $2h$; for smaller $M$ their expectations are bounded uniformly in the larger cutoff by a constant times the expected Kesten degree using the preceding bound (here $M\ge1$). Take $p_M=C_{h,K}$ there and $p_M=e^{-M}$ thereafter, and $M_n=2h+\lceil3\log(n+1)\rceil$. Their $a_n=O_{h,K}(n^{-1/2}\log^2(n+1))$ tends to zero with $\sum a_n/n<\infty$. Their Proposition 7 allows exact expectation centering. Write $b_{h,K}$ for the nonnegative standard deviation of the resulting Gaussian limit. The proof of their Theorem 1, §5, also gives $\operatorname{sd}(G)/\sqrt n\to b_{h,K}$: their finite-support approximants $W_{N,n}$ have standard deviations tending to $\gamma_N$, with $\gamma_N\to\gamma$, and their Lemma 8 bound shows $\sup_n\|X_n-W_{N,n}\|_2\to0$ for centered normalized variables (pp. 12–13 of arXiv v1). The reverse triangle inequality gives the asserted variance convergence, so no differentiation of a CLT or unwarranted moment convergence from weak convergence is involved. Adding the bounded-$L^2$ root error does not change either conclusion. We have proved, at each fixed $h,K$, both a Gaussian limit and convergence of normalized variances for the centered $S_{F_{h,K}}$.

Choose a deterministic sequence $K_h\to\infty$ so large that $(1+h)^a/K_h\to0$, and let $e_h\to0$ be the sum of the two approximation bounds of §1. The centered normalized variable $X_n=(A-\mathbb EA)/\sqrt n$ and the corresponding $X_{n,h}$ for $S_{F_{h,K_h}}$ differ by at most $e_h$ in $L^2$, uniformly in $n$. Thus $|b_{h,K_h}-b_{j,K_j}|\le e_h+e_j$ by first taking $n\to\infty$ for the fixed approximants. Their limit is some $\sigma\ge0$, and $\operatorname{sd}(A)/\sqrt n\to\sigma$ by the same inequality. For each fixed real $t$, the difference in characteristic functions of $X_n$ and $X_{n,h}$ is at most $|t|e_h$. Taking $n\to\infty$ then $h\to\infty$ yields $X_n\Rightarrow N(0,\sigma^2)$. The [square-root note](../square-root/PROOF.md) proves $\mathbb EA=\mu n+O(1)$, allowing the stated deterministic centering.

## 3. Nondegeneracy by size-ten fringe replacements

We adapt RSW's §6.1 fringe replacement argument for the log *number* of independent sets; a change of the count does not automatically change its logarithmic derivative. Our two gadgets match the root odds at unit activity and shift both root-conditioned size means by the same amount.

Encode a rooted tree by parentheses around the concatenated child encodings, with a leaf represented by `()`. For its root-present and root-absent polynomials $P(\lambda),Q(\lambda)$, the following table gives their values and ordinary derivatives at $\lambda=1$ and the order of the root-preserving automorphism group:

| shape | $P$ | $Q$ | $P'$ | $Q'$ | Aut |
|:---|---:|---:|---:|---:|---:|
| S: `(()(()())(()((()))))` | 40 | 130 | 140 | 395 | 2 |
| R: `((())(())((())(())))` | 36 | 117 | 120 | 336 | 4 |

Both have 10 vertices. The numbers follow by enumerating the $2^{10}$ subsets, or $P=\lambda\prod Q_i$, $Q=\prod(P_i+Q_i)$. Both odds equal $4/13$. The differences $P'_S/P_S-P'_R/P_R$ and $Q'_S/Q_S-Q'_R/Q_R$ each equal $1/6$. Replacing R by S in any fringe position therefore increases $A$ by exactly $1/6$: for every fixed outside configuration and root bit, its integrated weight on the outside/root-bit pair is multiplied by the same constant $10/9$ (the two in-counts and the two out-counts have that ratio). The joint distribution of the outside configuration and root bit remains unchanged. The expected size inside conditional on either bit increases by $1/6$.

Fix root 1 in $T_n$, $n>10$. Find each fringe occurrence of S or R; they are disjoint since an ancestor has strictly larger fringe size than a proper descendant. Remember the host after replacing them by marked leaves, each root label and the original 10-label set at each mark, but not the internal edges. The set of eligible positions is invariant under refilling: proper descendants have size below 10, proper ancestors of any replaced slot have size above 10, and disjoint untouched subtrees are unchanged. Every filling with the given labeled sets and designated roots gives exactly one labeled tree compatible with this host information. Uniformity on labeled trees thus makes the shape choices conditionally independent; their weights are $9!/|\mathrm{Aut}|$ per shape in each slot. Consequently S has probability $2/3$ and, writing $N$ for the number of slots, $A$ conditional on the host is a translate of $\frac16\mathrm{Bin}(N,2/3)$.

Janson's fringe frequency theorem for the conditioned Poisson tree gives $N/n\to\tau$ in probability, where $\tau=e^{-10}(1/2+1/4)=3e^{-10}/4$ is the ordinary PGW probability of either unordered shape. Indeed each finite unordered shape of size $s$ has probability $e^{-s}/|\mathrm{Aut}|$, by grouping the Poisson children. Since $N/n$ is bounded, taking expectations works too. Conditional variance and §2 imply
$$\sigma^2\ge \tau\frac{(2/3)(1/3)}{36}=\frac{e^{-10}}{216}.$$
The gadget alone also shows that no interval of length $o(\sqrt n)$ anywhere can contain $A$ with probability bounded away from zero: with high probability $N\ge\tau n/2$ and the largest atom of a binomial with fixed success probability is $O(N^{-1/2})$ (Stirling). The interval contains at most $6\,\mathrm{length}+1$ points of each translated lattice. This bound is not a local limit theorem.

## 4. Moving from the conditional mean to every mode

Fang–Lu–Nevo–Yao–Zheng [Theorem 1.1 and Proposition 5.1](https://arxiv.org/html/2609.20961v1) imply
$$\sup_{T:\,|T|=n}\max_{m\in\mathcal M(T)} |m-A(T)|=o(\sqrt n)$$
over trees (even forests). Here is the argument for this prior consequence. For a deterministic sequence of forests let $s_n$ be the conditional standard deviation of $|I|$. Their result gives $c\sqrt n\le s_n\le C\sqrt n$ uniformly, weak convergence of $(|I|-A)/s_n$ to a standard Gaussian, and eventually unimodal probabilities. If a mode exceeds $A+\varepsilon\sqrt n$ along a subsequence, take $d=\varepsilon/C$. The two adjacent standardized positive intervals $[d/4,d/2)$ and $[d/2,3d/4)$ lie strictly below that mode. Take adjacent integer blocks, the first starting at $\lceil A+s_nd/4\rceil$ and each of length $\lfloor s_nd/4\rfloor$. Their standardized endpoints tend to those fixed endpoints; their probabilities therefore converge to the Gaussian interval masses. For sufficiently large $n$, unimodality forces the later block's mass to be at least the earlier one's, whereas the Gaussian density strictly decreases there. Reflect below the mean for the opposite case. This argument applies along every possible violating sequence, so the estimate is uniform over the forest and all maximizers. It uses no coupling across different trees.

Thus every mode selector differs from $A$ by $o(\sqrt n)$ deterministically, hence also in $L^2$ after normalization. Slutsky and the triangle inequality for centered standard deviations give both assertions for $M_n$, regardless of ties. This inference uses a known conditional CLT, but the normal fluctuation in the conclusion is instead under the **tree** distribution.

## Sources and scope

For the unrooted two-root comparison, bounded bias, and source boundaries see the [square-root note](../square-root/README.md) plus Heilman's [2025 Question 8.2](https://doi.org/10.1002/jgt.23225). RSW's Theorem 1 and proof of Theorem 10 supply the CLT framework and fringe-slot method; the checked differences are in the statistic, its undirected-score approximation and the replacement gadgets' matched first moments. [Isaev–Southwell–Zhukovskii](https://doi.org/10.1017/S0963548321000523) give a separate martingale CLT for sufficiently stable tree functionals, including local patterns. Their framework is relevant general precedent, not evidence of a specific result for the parameter here. [Andriantiana–Misanantenaina–Wagner](https://arxiv.org/abs/1807.08290) treat the average-size invariant in deterministic graphs. A CLT for maximum size, greedy size, log number, planted law, or a uniform set *conditional on a fixed tree* is not a CLT for $A(T_n)$ or a coefficient mode under the random-tree law. Search cannot certify historical priority.
