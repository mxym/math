# Independent apices over sparse Sidorenko graphs

18 November 2026. AI-assisted research note for review. The argument has had an independent AI-assisted internal review and exact finite diagnostic checks, but no external peer review or proof-assistant certification. No claim of historical priority is made.

## Result

Given a graph $H$, let $H^{+k}$ be obtained by adding $k$ mutually nonadjacent vertices, each adjacent to every vertex of $H$. The Grzesik–Lee–Lidický–Volec conjecture asks whether $H^{+k}$ is common whenever $H$ is connected and Sidorenko. Here *common* means that the fair random two-coloring minimizes its asymptotic monochromatic homomorphism density. The following answers part of the question for cyclic bases.

**Sparse positive-cycle-rank theorem.** For every fixed $k\ge 2$ there is an explicit constant $C_k$ such that the following holds. Let $H$ be a connected simple bipartite graph with $v$ vertices, $e$ edges and cycle rank $r=e-v+1\ge1$. If $H$ has the Sidorenko property and $e\ge C_k r$, then $H^{+k}$ is common. Neither a degree bound nor a restriction on the arrangement of the cycles is required.

One admissible choice, not optimized, is
$$
a=2^{k-1}-1,\quad L_k=\frac{4^k-1-3k}{9},\quad b=\frac{16L_k}{3k},\quad
j=\max\!\left(1,\left\lceil\frac{a-k+2}{k+1}\right\rceil\right),\quad C_k=2abj .
$$
There is also a second sufficient condition, often better for small $k$:
$$
\frac{a}{3k}(v-2)+br\le e.\tag{A}
$$
For $k=2,3,4$, the pairs $(a/(3k),b)$ are $(1/6,8/3)$, $(1/3,32/3)$ and $(7/12,36)$. Unlike the general sparse theorem, (A) uses neither the spectral Sidorenko equivalence nor the tree-apex estimate.

**Example with unbounded treewidth.** Replace every edge of $K_t$, $t\ge4$, by a path of the same even length $n$, with distinct internal vertices on different paths. This base is Sidorenko by [Im–Li–Liu, Theorem 1.3](https://doi.org/10.1017/S0963548325100242), applied to the KNRS graph $K_t$ and the even path. If $h=\binom t2$, then $e=nh$ and $r=h-t+1$. Thus $n\ge C_k$ suffices, uniformly in $t$. The original $K_t$ remains a minor. The hypothesis is that the specific base has the Sidorenko property; the result does not assert that all bipartite graphs do.

**What is already known.** The [original conjecture, 1.3](https://doi.org/10.1017/S0963548322000074) is known for a single apex and for bases of at most five vertices. The same paper proves two apices over bare even cycles. [Kráľ–Krnc–Lamaison](https://doi.org/10.1137/25M177059X) treated trees, and more generally Sidorenko bases with $e=v-1$, for $k\le5$. [Chen](https://arxiv.org/html/2610.29469v1) treated all $k$ for trees and forests of average degree at least one. [Kim’s manuscript, Theorems 1.2–1.4](https://github.com/mekty2012/Apex-Commonality/blob/main/apices_commonness.pdf), dated 2 October 2026, treats all trees and all bare even cycles for every $k$, with an even stronger relative inequality for cycles at $k\ge3$; the [author's repository](https://github.com/mekty2012/Apex-Commonality) includes a Lean formalization. None of those tree, forest, or bare-cycle cases is claimed as new here. A bounded literature and announcement search through 18 November 2026 did not locate the general positive-cycle-rank criterion above. This is not an exhaustive priority determination.

## Proof

For a symmetric graphon $W:[0,1]^2\to[0,1]$ put
$$
 M(F)=t(F,W)+t(F,1-W),\qquad [F]=2^{e(F)-1}M(F).
$$
Here $t$ is the usual homomorphism density. Commonness means $[F]\ge1$ for every $W$; equality holds for $W\equiv1/2$. Sidorenko means $t(H,W)\ge t(K_2,W)^e$ for all graphons. We use $P_j$ for a path with $j$ **edges**, and abbreviate
$$
D=[H^{+k}],\quad B=[K_{1,1,k}],\quad S=[K_{1,k}],\quad Q=[K_{2,k}],\quad P=[P_j^{+k}].
$$

### 1. Two comparisons over common neighborhoods

Integrate over the disjoint union of two copies of $[0,1]^k$, each of mass one. A point specifies the color $V\in\{W,1-W\}$ and the ordered apex tuple $z=(z_1,\ldots,z_k)$. Set $q(x)=\prod_i V(z_i,x)$, $d=\int q$, and $\delta=\iint q(x)V(x,y)q(y)\,dx\,dy$. Let $h$ and $p_j$ denote the $H$ and $P_j$ densities conditional on these apex images: integrate the base vertices against $q(x)\,dx$. The integrals of $h,\delta,d,d^2,p_j$ over the two colors and apex tuples are precisely the unnormalized $M$-values represented by $D,B,S,Q,P$.

At $d>0$ apply Sidorenko in the probability measure $q(x)\,dx/d$ to get $h\ge\delta^e d^{v-2e}$. (This probability measure may equivalently be transported from a uniform variable.) When $d=0$ all conditional densities vanish. Since $v-2+2r=2e-v$ and $1+(v-2)+r=e$, Hölder applied to
$$
 \delta\le h^{1/e}d^{(v-2)/e}(d^2)^{r/e}
$$
gives
$$
 DS^{v-2}Q^r\ge B^e.\tag{1}
$$
Zero powers are omitted. This extends the book/star comparison used by Kráľ–Krnc–Lamaison for $r=0$. At $k=2$ and $e=v$, the same book/star/four-cycle expression appears in the original conjecture paper's proof for even cycles.

For $r\ge1$ and any integer $j\ge1$ with $(r+1)j\le e$, a second comparison is
$$
 D^j S^{e-(r+1)j}Q^{rj}\ge P^e.\tag{2}
$$
It suffices to work with finite simple hosts and then take a graphon limit. In a host on $N$ vertices, let the monochromatic common neighborhood of a fixed tuple have $m$ vertices and induce the graph $F$. For $m>0$ write $A_F$ for its adjacency matrix and $\lambda=\lVert A_F\rVert_{2\to2}$. Since $r\ge1$ gives $e\ge v$, the vertex-spectral version of Sidorenko, [Li–Lin–Liu–Zhang, Theorem 1.1(iii)](https://arxiv.org/html/2605.26614v2), gives
$$
 \operatorname{hom}(H,F)\ge\lambda^e m^{v-e}.
$$
Also $\operatorname{hom}(P_j,F)=\mathbf 1^T A_F^j\mathbf 1\le m\lambda^j$. Divide counts by $N^v$ and $N^{j+1}$, respectively, so $d=m/N$ and
$$
 p_j\le h^{j/e}d^{1+(e-v)j/e}.
$$
The zero-neighborhood and edgeless-neighborhood cases hold directly. Apply Hölder to $h,d,d^2$ with weights $(j,e-(r+1)j,rj)/e$ to obtain (2). Any $W$ is the limit in homomorphism densities of finite $W$-random graphs; the graphon of the simple complement differs from the exact complementary step graphon only on the $N$ diagonal vertex blocks, of total area $1/N$. The error in any fixed homomorphism density is thus $O_F(1/N)$. Both (1) and (2) are unchanged on passing from $M$ to normalized brackets, since the exponents and edge-count scalings match on both sides. This proof requires no spectral convergence of the sampled graphs.

### 2. The degree and codegree estimates

Let $u(x)=2d_W(x)-1$, $A=\int u^2$, and thus $0\le A\le1$. Expanding the star, and bounding every even power of $u$ of degree at least two by $u^2$, gives
$$
 S=\tfrac12\mathbb E[(1+u)^k+(1-u)^k]\le1+aA .
$$
Goodman's identity gives $[K_3]=1+3A$ and $[P_2]=1+A$.

For a uniform pair $(x,y)$ set $V_0=W$, $V_1=1-W$ and $c_i=\int V_i(x,z)V_i(y,z)\,dz$. There are **two different laws** for sampling the color:
* Choose $i$ with conditional probability $V_i(x,y)$. Then $X=4c_i$ has $\mathbb E X^k=B$ and $\mathbb E X=1+3A$. Jensen gives $B\ge1+3kA$ and $B\ge B_2^{k/2}$, where $B_2=[K_{1,1,2}]\ge1$.
* Choose $i$ uniformly, independently of $(x,y)$. Then $Y=4c_i$ has $\mathbb E Y^k=Q$, $\mathbb E Y=1+A$, and $\mathbb E Y^2=Q_2=[C_4]$.

On $[0,4]$, $0\le t^k-1-k(t-1)\le L_k(t-1)^2$: the quotient by $(t-1)^2$ is $\sum_{i=0}^{k-2}(k-1-i)t^i$, maximized at $4$. Therefore
$$
 Q-1\le L_k(Q_2-1)+(k-2L_k)A\le L_k(Q_2-1).
$$
[Grzesik–Lee–Lidický–Volec, Lemma 4.2](https://doi.org/10.1017/S0963548322000074) with $c=3/16\le(3-\sqrt5)/4$ gives $Q_2-1\le(8/3)(B_2-1)$ in our normalization. Using $B\ge1+(k/2)(B_2-1)$, we have proved
$$
 S-1\le aA\le \frac{a}{3k}(B-1),\qquad Q-1\le b(B-1).\tag{3}
$$
In particular $B,S,Q\ge1$, by the moment identities and Jensen.

### 3. Two regimes prove commonness

Under (A), apply arithmetic–geometric mean to $v-2$ copies of $S$, $r$ copies of $Q$, and one copy of $1$. Their number is $e$ and by (3) their sum is at most $eB$. Thus $S^{v-2}Q^r\le B^e$. Inequality (1) gives $D\ge1$.

For the general theorem write $x=B-1\ge0$ and suppose $e\ge2abjr$ with $j$ chosen as above. If $S-1\le x/2$, the same arithmetic–geometric mean bound works provided $(v-2)/2+br\le e$; this follows from $v-2\le e$ and $e\ge 2br$.

Otherwise $x<2(S-1)\le2aA$. Thus $Q\le1+2abA$. By [Chen, Lemma 3.2 (3.8)](https://arxiv.org/html/2610.29469v1), or Kim's Theorem 1.2 and Goodman's inequality $M(K_3)\ge M(P_2)^2$, the apex of a path satisfies
$$
 P\ge(1+A)^{(k+1)j+k-1}.\tag{4}
$$
Indeed $P_j^{+k}$ has $(k+1)j+k$ edges. Since $a,b\ge1$ and $r\ge1$, our assumption implies $(r+1)j\le e$. Using Bernoulli, bound $S\le(1+A)^a$ and $Q\le(1+A)^{2ab}$. Now (2) and (4) yield
$$
 D^j\ge(1+A)^{e[(k+1)j+k-1]-a[e-(r+1)j]-2abrj}.
$$
The exponent is nonnegative because $(k+1)j+k-1-a\ge1$ and $e\ge2abrj$. This finishes the proof.

### 4. A host-restricted consequence without a sparsity assumption

If $d_W(x)=1/2$ almost everywhere, then $c_0-c_1=d_W(x)+d_W(y)-1=0$ almost everywhere. The two laws for the codegree moment now give $B=Q$, and $S=1$. Inequality (1) gives $D\ge B^{v-1}\ge1$. This applies to every connected Sidorenko base on at least two vertices, and to every $k\ge1$, using the direct moments in the $k=1$ case. This is a restriction on the degree *function*, not merely on its mean. No reduction from arbitrary two-color graphons to half-regular ones is asserted.

## Limits, attribution and diagnostics

* The criterion is sufficient, not sharp. It does not cover all dense Sidorenko bases. The full independent-apex conjecture remains outside this note.
* Some further specializations follow from existing inputs. For example at $e=v\ge4$, $k=3$, Kim's Lemma 3.7 gives a mean fourth power of at least one for the conditional test-vector spectral bound used in his Lemma 3.5. The vertex-spectral Sidorenko inequality supplies the corresponding $v$th-power lower bound for every such Sidorenko base, so Jensen already gives this special case. Bare cycles and threshold claims about them are not the contribution.
* As another example, a bouquet of $r$ identical even cycles of length $n$ need not be treated by the general sparse theorem. For $k\ge3$, Hölder over the common hub and the apices bounds its normalized apex density below by $[C_n^{+k}]^r/S^{r-1}$. Kim gives $[C_n^{+k}]\ge[C_n]$. For each color the even trace and the test vector $\mathbf1$ show $t(C_n,V)\ge\lVert T_V\rVert^n\ge t(P_2,V)^{n/2}$, so $[C_n]\ge(1+A)^{n/2}$. All $n\ge2a$ suffice for the bouquet. This short implication is not claimed as an independent novelty.
* The analytic inputs are cited where used. No authors' proof files, certificates or third-party datasets are redistributed. AI assisted with the proof, literature checks, internal adversarial review and diagnostics. No external reviewer or formal proof checker has validated the argument presented here.
* Run `python3 verify.py` from this directory to reproduce [diagnostics.json](diagnostics.json) using only the Python standard library. The checker conditions on **base** images rather than implementing the proof's conditional-apex formulas, and checks selected cases again by direct enumeration of every vertex image. It performs 2,331 book-transfer checks and 3,330 path-transfer checks across 75 weighted two- and three-block kernels, with 280 direct full-graph comparisons. These finite calculations test normalization and the formulas, not the universal theorem.
