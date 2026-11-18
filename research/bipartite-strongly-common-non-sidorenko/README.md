# A bipartite strongly common graph that is not Sidorenko

**Research draft for review · 18 November 2026.** The argument uses the rank-layer limit and explicit kernel construction in the 2026 OpenAI preprint [O]. It has been reviewed internally with AI assistance, not externally refereed or formally verified. No claim of historical priority or optimality of the number of squares is made.

**中文摘要。** 设 $H$ 是文献 [O] 中的 35 顶点二部关联图。将它与 $2^{650}$ 个四圈作不交并，得到强二色 common 但非 Sidorenko 的有限简单二部图。这回答 [G] 第 908 页未要求连通的提问；本文的构造不连通。[后续稿](../connected-bipartite-strongly-common-non-sidorenko/README.md)另外给出了有割边的连通例子，但没有得到二连通例子。下述反例使用 [O] 的有限域引理，不是从其最终反例定理直接推出；这里只独立推导同一族核的四圈密度极限。

## The statement

Let $H$ be the incidence graph of the 22 triples on 13 points specified in [O, Table 1], also listed in [the arithmetic check](verify.py). Points and triples are distinct vertex classes. Thus $H$ has 35 vertices, 66 edges and no isolated vertices. For the vertex-disjoint union, write

$$G_M=H\sqcup M C_4.$$

**Theorem.** With $M=2^{650}$, $G_M$ is strongly common in two colors but is not Sidorenko. In fact $G_M\sqcup \ell K_2$ has both properties for every integer $\ell\ge0$. For every fixed $k\ge2$, some $M=M(k)$ makes $G_M$ simultaneously $j$-common for $2\le j\le k$, while still not Sidorenko.

A graphon $W$ is a measurable symmetric $[0,1]$-valued kernel on the unit square with Lebesgue measure. Write $t(F,W)$ for the integral of the product of the edge kernels, with one independently integrated variable per vertex. The same definition works on probability spaces and for bounded signed kernels. Write $p=\int W$ and $e(F)=|E(F)|$. The properties in the theorem mean:

- **Sidorenko:** $t(F,W)\ge p^{e(F)}$ for every graphon.
- **Strongly common:** $t(F,W)+t(F,1-W)\ge p^{e(F)}+(1-p)^{e(F)}$ for every graphon [N, equation (2)].
- **$j$-common:** $\sum_{i=1}^j t(F,W_i)\ge j^{1-e(F)}$ whenever the graphons $W_i$ sum to 1 almost everywhere. Strong two-color commonness implies two-color commonness by convexity.

Grzesik, Lee, Lidický and Volec [G, p. 908, introduction] asked the converse of the implication from Sidorenko to commonness for bipartite graphs. Their question has no connectedness restriction. The graph here is disconnected; it neither proves that $H$ itself is common nor gives a connected separating example. The multicolor statement does not produce one non-Sidorenko graph common for **all** color counts; that would contradict [K]. A [subsequent draft](../connected-bipartite-strongly-common-non-sidorenko/README.md) ([#49](https://github.com/mxym/math/pull/49)) supplies the connected example by joining the core to a bouquet of squares with one bridge. That construction is not 2-connected and does not decide whether the core itself is common.

## 1. The error in counting a bipartite graph

Let $F$ be a finite simple bipartite graph with $e\ge1$ edges, and part sizes $a,b$ after ignoring isolated vertices. Put $U=W-p$ and $T_Kf(x)=\int K(x,y)f(y)\,dy$. Define

$$s=\|T_U1\|_2^2,\qquad R=s+t(C_4,U),\qquad \Delta=t(C_4,W)-p^4.$$

We need two bounds:

$$|t(F,W)-p^e|\le 2^e R,\qquad R\le (1+2/p^2)\Delta\quad(p>0). \tag{1}$$

For the first, expand $\prod_{uv\in E(F)}(p+U(x_u,x_v))$. A nonempty selected forest with a single-edge component contributes zero, since $\int U=0$. For any other nonempty forest, select two leaves of the same tree component. They are nonadjacent. Integrating out the leaves gives two centered degree factors $T_U1$. All remaining factors have modulus at most 1. If the leaves have the same neighbor, the bound is $s$; if the neighbors are distinct, it is $\|T_U1\|_1^2\le s$.

If the chosen subgraph has a cycle, take a shortest cycle. Its length $m$ is even and at least 4, and it has no chord among the chosen edges. Fix all variables outside this cycle. Edges meeting the cycle in one vertex contribute one-variable multipliers $f_1,\ldots,f_m$ bounded by 1; edges disjoint from it contribute a scalar of modulus at most 1. The cycle integral is the trace of the product of operators $M_{f_i}T_U$, where $M_f$ denotes multiplication. By Schatten Hölder and the ideal norm inequality its absolute value is at most

$$\prod_{i=1}^m\|M_{f_i}T_U\|_{S_m}
\le \|T_U\|_{S_m}^m
\le\|T_U\|_{\mathrm{op}}^{m-4}\|T_U\|_{S_4}^4
\le t(C_4,U).$$

Here $\|T_U\|_{\mathrm{op}}\le\|U\|_2\le1$, and selfadjointness gives $t(C_4,U)=\operatorname{Tr}(T_U^4)$. The trace identity can first be read for step kernels as an ordinary weighted matrix trace. Conditional expectations on refining finite partitions approximate bounded kernels in $L^2$ and $L^1$; telescoping the edge factors bounds the change in a fixed graph integral by the number of edges times the $L^1$ error. This also proves the graphon estimate from the finite case. The remaining powers of $p$ are at most 1; the expansion has fewer than $2^e$ nonconstant terms.

For the second bound, decompose $L^2$ into constants and their orthogonal complement. The matrices of $T_W,T_U$ are, respectively,

$$\begin{pmatrix}p&z^*\\z&D\end{pmatrix},\qquad \begin{pmatrix}0&z^*\\z&D\end{pmatrix},\qquad s=\|z\|^2.$$

Write $B=zz^*+D^2$. Taking Hilbert–Schmidt norms of the squares gives

$$\Delta=(p^2+s)^2-p^4+2\|(pI+D)z\|^2+\|B\|_{\mathrm{HS}}^2\ge 2p^2s+\|B\|_{\mathrm{HS}}^2,$$

$$t(C_4,U)=s^2+2\|Dz\|^2+\|B\|_{\mathrm{HS}}^2\le 3s+\Delta,$$

using $s\le1$ and $\|D\|_{\mathrm{op}}\le1$. Thus $R\le4s+\Delta\le(1+2/p^2)\Delta$. This proves (1). In particular $\Delta\ge0$ for all $p$, with the $p=0$ case immediate.

One further elementary estimate used below is

$$t(F,W)\ge t(K_{a,b},W)\ge p^{ab}. \tag{2}$$

The first inequality inserts more factors in $[0,1]$. For the second, condition on the $a$ left variables $x_i$ and apply Jensen to the $b$th power of $\int\prod_i W(x_i,y)\,dy$. The resulting inner expectation is $\int d_W(y)^a\,dy\ge p^a$ by Jensen again.

## 2. Padding makes the graph strongly common

First work with any $F$ as above and $G=F\sqcup M C_4$. Write $A=2^e$ and $E=e+4M$. Relabel the two graphons as $P,Q=1-P$ so their densities are $p\ge 1/2$ and $q=1-p$. The centered kernels are negatives of each other. Consequently $R$ in (1) is **the same for both colors**.

For $P$, set $h=t(F,P)$, $\Delta_p=t(C_4,P)-p^4$. Equations (1) and (2) give $h-p^e\ge-AR$, $h\ge2^{-ab}$, and $\Delta_p/p^4\ge R/9$. By multiplicativity on disjoint unions and Bernoulli's inequality,

$$
t(G,P)-p^E
=p^{4M}\{h(1+\Delta_p/p^4)^M-p^e\}
\ge R p^{4M}\big(-A+M2^{-ab}/9\big).
$$

If $M\ge18\cdot2^{e+ab}$, the last quantity is at least $ARp^{4M}$. For $Q$, using $t(C_4,Q)\ge q^4$, $t(F,Q)\ge0$ and (1), we have

$$t(G,Q)-q^E\ge q^{4M}\big(t(F,Q)-q^e\big)\ge-ARq^{4M}.$$

The sum is nonnegative because $p\ge q$. This proves strong commonness, including $q=0$, with no division by $q$. If $\ell$ disjoint edges are added, the two lower bounds are multiplied by $p^\ell,q^\ell$, respectively, and their sum is still nonnegative. For $H$, $ab=286$ and $18\cdot2^{66+286}<2^{357}<2^{650}$. Thus even $2^{357}$ is sufficient in the two-color statement; the counts are not optimized.

## 3. Any prescribed finite range of color counts

Given $p_0\in(0,1)$, let $C=2^e(1+2/p_0^2)p_0^{-ab}$. For a color of density $p\ge p_0$, (1) and (2) imply, with $h=t(F,W)>0$ and $x=\Delta/p^4$,

$$p^e/h\le1+2^e(1+2/p_0^2)\Delta/h\le1+Cx.$$

For $M\ge C$, Bernoulli gives $(1+x)^M\ge 1+Cx$ and hence $t(F\sqcup MC_4,W)\ge p^{e+4M}$. Fix $j\ge2$ and take $p_0=1/(2j)$. If every color has density at least $p_0$, sum the last inequality and use Jensen. If a color is rarer, one of the remaining colors has density at least $q_j=(1-1/(2j))/(j-1)>1/j$. In that color alone, (2) and the four-cycle inequality give density at least $q_j^{ab+4M}$, which is at least $j^{1-e-4M}$ once $q_j^{ab}(j q_j)^{4M}\ge j^{1-e}$. This is a finite threshold since $j q_j>1$. Choose the maximum of all thresholds for $2\le j\le k$.

## 4. The same graph is not Sidorenko

This part uses specific intermediate results of [O], **not** just the existence of its 35-vertex counterexample. We spell out the imported statements and why their parameters coincide. For a bipartite graph $J$ with a designated bipartition, write $t_{\mathrm{rec}}(J,W)$ for its rectangular density: independent variables from the first probability space on the first side, from the second space on the second. Unlike the graphons in §§1–3, the rectangular kernels in this section need not take values at most 1.

**Inputs from [O].** For each sufficiently large odd prime $r$ their §3 constructs a nonnegative, mean-one kernel $W_r$ on two finite probability spaces. A vertex carries a type and, at each coordinate $c$ of a fixed finite set $\mathcal K$, an independent uniform symmetric matrix over the field of order $r$. In (3.6), conditional on two endpoint types, an incidence kernel is the expectation over an activation set $S\subseteq\mathcal K$ and signs $\xi_c$ for $c\in S$ of a product of rank-layer factors over the active coordinates. Independently sampling one such package for each incidence expands a product of kernel values. For every nonempty $\alpha\subseteq\mathcal K$ the conditional one-incidence moment satisfies

$$\mathbb{E}\!\left[\mathbf{1}_{\alpha\subseteq S}\prod_{c\in\alpha}\xi_c\ \middle|\ \text{endpoint types}\right]=0. \tag{3}$$

The product with an inactive coordinate is understood as zero. This is [O, (3.7)], preserved by the thinning in (3.20) and by adding a type with empty activation. Each coordinate’s rank-layer integral is approximated by the signed-square formula in [O, Lemma 3.1 and (3.4)]: for any subset of incidences of $H$, and signs on those incidences, its limiting expectation is the product of one factor for each square of the complex whose four incidences are present. Such a factor is 1 plus the product of its four signs. The error is $o(1)$ uniformly for these finitely many subsets and sign choices. The statement applies for each sufficiently large fixed even matrix dimension.

Choose that dimension, the activation parameters, fixed finite type-thinning parameter, and then a small positive dilution $\epsilon$, all as in [O, §§3.3–3.5]. Their (3.24) and (3.25) give, as $r$ tends to infinity through odd primes,

$$t_{\mathrm{rec}}(H,W_r)t_{\mathrm{rec}}(H,W_r^\top)\longrightarrow L=(1+\epsilon^{13}t_0)(1+\epsilon^{22}t_1)<1. \tag{4}$$

The constants $t_0<0$ and $t_1$ do not depend on $r$ or $\epsilon$; $\epsilon$ is fixed *before* passage to the limit. We use the rank-layer estimate and (4) as theorems of that preprint, not as computations verified by the accompanying script.

**The square limit for these parameters.** We claim $t_{\mathrm{rec}}(C_4,W_r)\to1$. View $C_4$ as the four incidences from points 0 and 1 to faces 0 and 1 of the complex. These faces are $(0,1,3)$ and $(0,1,9)$ in [O, Table 1]. All other vertex variables in the rank-layer lemma can be introduced as unused independent variables. Conditional on arbitrary types for the four vertices, sample the four incidence packages independently. Fix the packages as well. The matrix expectations now factor by coordinate. For a particular coordinate $c$ the active incidences form a subset of this single square; no other complex square can be fully present. The rank-layer limit at that coordinate is therefore

$$1+\prod_{h\in E(C_4)}\big(\mathbf{1}_{c\in S_h}\xi_{h,c}\big).$$

The limiting factors are bounded by 2; there are only finitely many coordinates and package choices. Thus their product and subsequent averaging preserve $o(1)$. Expand the product of these limits, selecting the second term at a subset $\alpha$ of coordinates. Its conditional average over the four independent packages equals the product, over incidences $h$, of the single-package conditional moment in (3) for $\alpha$. If $\alpha$ is nonempty those moments vanish, even if some vertex types coincide. The empty choice contributes 1. Averaging over the types proves the claim. The transpose square density is equal by exchanging the two sides of $C_4$.

**Symmetrization and normalization.** On the product of the two finite spaces define

$$V_r((x,y),(x',y'))=W_r(x,y')W_r(x',y).$$

The kernel is nonnegative, symmetric and of mean 1 by independence. For any bipartite $J$, the two sets of coordinate draws used by the two factors are independent, so

$$t(J,V_r)=t_{\mathrm{rec}}(J,W_r)\,t_{\mathrm{rec}}(J,W_r^\top).$$

Consequently $t(H,V_r)\to L<1$ and $t(C_4,V_r)\to1$. For each **fixed** finite $M,\ell$, the density of $H\sqcup MC_4\sqcup\ell K_2$ in $V_r$ tends to $L$ by disjoint-union multiplicativity. Thus choose one finite $r$ at which that density is strictly below 1. Let $B=\max V_r\ge1$; the kernel $U_r=V_r/B$ is now $[0,1]$-valued and has mean $\mu=1/B>0$. On replacing finite atoms by intervals of their respective probabilities, this is a graphon. By homogeneity its pattern density is strictly below $\mu^{e+4M+\ell}$. There is no uniform sup-norm bound or positive uniform density assumption as $r$ varies. In particular the argument does not apply a dense quasirandomness theorem to the unbounded sequence.

**Finite simple graphs.** To record the transfer explicitly, let the violating pattern be $J$, with $v$ vertices, $d$ edges and gap $\delta=\mu^d-t(J,U_r)>0$. Sample $n$ independent labels, then draw each unordered pair of *distinct* vertices as an independent Bernoulli edge conditional on the labels, using $U_r$. In this random simple graph $A_n$, $\mathbb{E} p(A_n)=(1-1/n)\mu$, where $p(A_n)=2|E(A_n)|/n^2$. For injective vertex maps the expected homomorphism indicator is exactly $t(J,U_r)$; at most a fraction $\binom{v}{2}/n$ of all maps have a collision. Therefore $\mathbb{E} t(J,A_n)\le t(J,U_r)+\binom{v}{2}/n$. For $n>(\binom{v}{2}+d\mu^d)/\delta$, Bernoulli and Jensen yield

$$\mathbb{E} t(J,A_n)<(1-1/n)^d\mu^d=(\mathbb{E} p(A_n))^d\le\mathbb{E}[p(A_n)^d].$$

Some finite simple host violates Sidorenko. For the commonness direction, represent a finite coloring of $K_n$ by color step graphons, assigning any color on diagonal blocks. The normalized count of injective monochromatic copies differs from the homomorphism sum by $O_J(1/n)$, since only maps with collisions matter; the uniform random coloring attains the stated asymptotic commonness benchmark. Thus these conclusions concern ordinary simple graphs, not a hypergraph or a system of linear equations.

## Sources, antecedents, and verification boundary

- **[G]** A. Grzesik, J. Lee, B. Lidický and J. Volec, [*On tripartite common graphs*](https://doi.org/10.1017/S0963548322000074), CPC 31 (2022), 907–923. The converse question is unnumbered in the introduction, separate from connected apex-graph questions in the paper.
- **[O]** OpenAI, [*A counterexample to Sidorenko’s conjecture*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Sidorenkos-conjecture-September-23-2026/paper.pdf), 23 September 2026. Its incidence graph, rank-layer theorem, activation laws and negative coefficient are the external input. The additional simultaneous square limit is derived above.
- **[KVW]** D. Král’, J. Volec and F. Wei, [*Common graphs with arbitrary chromatic number*](https://arxiv.org/abs/2206.05800), §1.1. Their analysis already explains how a disjoint complete-bipartite padding component can enforce commonness. We do not claim to introduce the padding idea; our padding uses disjoint four-cycles and a matching sparse normalized witness.
- **[N]** J.-b. Lee and J.A. Noel, [*Disconnected Common Graphs via Supersaturation*](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v33i2p1/pdf/), EJC 33 (2026), P2.1. Their equation (2) is the definition of strongly common used here. Their disjoint-edge invariant $\mathrm{DE}(G_M)$ is infinite in the two-color example by §2, which does not address the analogous pendant-tree invariant.
- **[K]** D. Král’, J.A. Noel, S. Norin, J. Volec and F. Wei, [*Non-bipartite k-common graphs*](https://arxiv.org/abs/2006.09422), Combinatorica 42 (2022), 87–114.
- **Background.** L. Lovász, [*Subgraph densities in signed graphons and the local Simonovits–Sidorenko conjecture*](https://doi.org/10.37236/614), EJC 18 (2011). The argument here does not invoke an unconstrained cut-local theorem for varying unbounded kernels.

The linked script checks the table’s elementary incidence properties and the numerical thresholds by exact integer arithmetic. It does **not** certify the analytic proof or replay the external finite-field estimates. Internal AI-assisted reviews checked the analytic estimates, the parameter order and the finite-graph transfer. This is a draft for mathematical review, not external peer review, a Lean certificate or a proof that no precursor exists.
