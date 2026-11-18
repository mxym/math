# A connected strongly common bipartite graph without the Sidorenko property

**Research draft for review · 18 November 2026.** One bridge joins the 35-vertex OpenAI graph to a bouquet of squares. This gives a connected example, unlike the [earlier disjoint-union construction](https://github.com/mxym/math/blob/0deb2d848775ea6a76b5aee6da61374e9129286c/research/bipartite-strongly-common-non-sidorenko/README.md). The two constructions are not the same graph. The rank-layer theorem and negative core-density limit come from [O]; their proofs are not reproduced here. Two separate AI-assisted internal reviews found no gap in the stated argument. No external peer review, Lean verification, optimality claim, or guarantee of priority.

**中文摘要。** 由一条桥将已知 35 顶点二部图连接到若干共顶点四圈，所得有限简单连通二部图是 strongly common，却不具备 Sidorenko 性质。原提问不要求连通。这是对不交并结果的加强；构造本身有割边，**不解决二连通版本**，也不判定原 35 顶点图是否 common。

## Result and notation

Let $H$ be the incidence graph in OpenAI [O, Table 1]: point and face classes of sizes 13 and 22, with 66 incidences. Let $o$ be the vertex for point 0. Add a new vertex $w$, the bridge $ow$, and $M$ squares through $w$, otherwise vertex-disjoint from each other and from $H$. Denote the result by $B_M$. It has $36+3M$ vertices and $67+4M$ edges. It is connected since $H$ is connected, and it is simple and bipartite. In particular this is **not** the disjoint union of $H$ and $M$ squares.

**Theorem (research draft).** With $M=2^{3850}$, $B_M$ is strongly common but not Sidorenko. Strong commonness means $t(B_M,W)+t(B_M,1-W)\ge p^{67+4M}+(1-p)^{67+4M}$ for every graphon $W$ with $p=\int W$. Non-Sidorenko means a strict violation of $t(B_M,W)\ge p^{67+4M}$ for some such $W$ (equivalently some finite simple host). In particular this answers the connected restriction of the unnumbered converse question of [G, p. 908]; GLLV did not require connectedness. No claim about a **2-connected** example: our graph deliberately uses a bridge.

Throughout, $t(J,W)$ is the product of edge factors integrated over independent uniform labels for the vertices of the simple graph $J$. Rooted densities condition on the label of one marked vertex. For $E=e(J)$, Jensen gives $p^E+(1-p)^E\ge 2^{1-E}$, so the strong two-color inequality implies ordinary commonness. The graphon condition gives the usual labelled injective-copy bound asymptotically: at most $O_J(1/n)$ of the maps into an $n$-vertex coloring identify two vertices.

## 1. Fixed-pattern estimates

In the commonness proof $W$ is symmetric, $0\le W\le1$ on the square over a probability space; take $[0,1]$ with Lebesgue measure. Let $U=W-p$, $T=T_W$ and $L=T_U$ be the corresponding integral operators, $z=L1=d_W-p$, $s=\|z\|_2^2$, and
$$
 R=s+\operatorname{Tr}(L^4),\qquad \Delta=t(C_4,W)-p^4 .
$$
Let $J$ be any simple bipartite pattern with $j\ge1$ edges. We use
$$
 |t(J,W)-p^j|\le 2^j R,\qquad R\le (1+2/p^2)\Delta\quad (p>0).
 \tag{1}
$$
For completeness, expand the integral in centered edges $U$. Nonempty selected forests either contain an isolated-edge component of integral zero, or a nontrivial tree; integrating two leaves of that tree gives at most $s$ in absolute value because other factors are bounded by 1 (shared neighbor: degree square, otherwise use $\|z\|_1^2\le s$). In a cyclic chosen subgraph select a shortest cycle. It is chordless and has length $l\ge4$. Fix variables outside it; the remaining cycle edges carry $U$, with at most one multiplicative function of absolute value at most 1 per cycle vertex after collecting all off-cycle incident edges. Its trace integral is bounded by Schatten Hölder by $\|L\|_{S_l}^l\le\|L\|_{\mathrm{op}}^{l-4}\operatorname{Tr}(L^4)\le\operatorname{Tr}(L^4)$; $\|L\|_{\mathrm{op}}\le\|U\|_2\le1$. At most $2^j$ terms occur. This argument may first use finite step kernels, then $L^1$ approximation of bounded graphons for each finite graph integral.

In the orthogonal decomposition into constants and zero-mean functions, $T=[p,z^*;z,D]$, $L=[0,z^*;z,D]$, and $s=\|z\|^2\le1$. Put $A=zz^*+D^2$. From the block entries of $T^2,L^2$ one gets $\Delta\ge 2p^2s+\|A\|_{\mathrm{HS}}^2$, and $\operatorname{Tr}L^4=s^2+2\|Dz\|^2+\|A\|_{\mathrm{HS}}^2\le3s+\Delta$. This proves (1), and $\Delta\ge0$ also holds at $p=0$. In particular $\eta=\|L\|_{\mathrm{op}}\le R^{1/4}$.

We now work with $p\ge p_0=1/4$ unless explicitly noted otherwise. Write $C_j=33\cdot2^j$. Then (1) bounds the counting error by $C_j\Delta$. Let $h(x)$ be the rooted density of $H$ conditional on $o=x$, $m=\int h=t(H,W)$, $g=h-m$, and $b=T h$. Thus $b$ is the rooted density of $H$ plus its bridge, marked at the new vertex $w$. Put $n=\int b$. Let $c(x)$ be the rooted density of a square, marked at any corner. Thus $\int c=p^4+\Delta$ and, with $K(x,y)=\int W(x,v)W(v,y)\,dv$ the codegree kernel,
$$
 c(x)=\int K(x,y)^2\,dy,\qquad t(B_M,W)=\int b(x)c(x)^M\,dx .
 \tag{2}
$$
All these rooted densities are nonnegative. Complete-bipartite completion and twice Jensen give $m\ge p^{286}\ge 2^{-572}$ and $n\ge p^{13\cdot23}>0$. Also $n-p^{67}\ge-C_{67}\Delta$.

Both $h$ and $c$ have controlled rooted fluctuations. The second moment of $h$ is the density of two copies of $H$ identified only at their marked vertex, a simple bipartite graph with 132 edges. Thus
$$
 \|g\|^2=\int h^2-m^2\le (C_{132}+2C_{66})\Delta\le 2^{140}\Delta .
$$
Here $|m^2-p^{132}|\le2|m-p^{66}|$. Similarly $\int c^2\le p^8+C_8\Delta$ by the two-square bouquet, and $\int c=p^4+\Delta$, so
$$
 \|c-p^4\|_2^2\le C_8\Delta\le 2^{14}\Delta. \tag{3}
$$

## 2. A positive first-order gain across the bridge

We claim that for $\Delta\le\delta=2^{-2706}$ one has
$$
 I:=\int b(x)(c(x)-p^4)\,dx \ \ge\ \kappa\Delta,\qquad \kappa=2^{-598}. \tag{4}
$$
The case $\Delta=0$ is covered without division; then (1) gives $L=0$.

For the main term define $B=\int d_W(c-p^4)$. Let $r(x)=\int(K(x,y)-p^2)^2dy\ge0$. Since $T d_W=p^2+pz+Lz$ and $\int Lz=s$, expanding $c$ yields the exact identities
$$
 c(x)-p^4=2p^3 z(x)+2p^2 (Lz)(x)+r(x),\qquad \int r=\Delta-2p^2s.
$$
In particular
$$
 B=p\Delta+2p^3s+2p^2\langle z,Lz\rangle+\int zr
 \ \ge\ (4p^3-2p^2\eta)s ,
 \tag{5}
$$
because $z\ge -p$ and $r\ge0$. Also $B\ge p\Delta-2^7\sqrt{s\Delta}$ by (3) and Cauchy–Schwarz. Under $\Delta\le\delta$, $\eta\le(33\delta)^{1/4}\le2^{-675}\le p$. If $s\ge2^{-20}\Delta$, (5) gives $B\ge2p^3s\ge2^{-25}\Delta$. If $s<2^{-20}\Delta$, the alternative estimate gives $B\ge(p-1/8)\Delta\ge\Delta/8$. Thus $B\ge2^{-25}\Delta$ uniformly for all $p\ge1/4$.

Finally $b=T(m1+g)=m d_W+Lg$, because $g$ has mean zero. By (3),
$$
 I\ge m B-\eta\|g\|_2\|c-p^4\|_2
 \ge (2^{-572-25}-2^{-675+70+7})\Delta=2^{-598}\Delta.
$$
This proves (4). The single bridge is used precisely in turning the residual rooted function $g$ into $Lg$.

Since $b/n$ is a probability density, Jensen and the tangent bound for the $M$th power at $p^4>0$ give
$$
 t(B_M,W)\ge n(p^4+I/n)^M
 \ge p^{4M}\bigl(n+M I/p^4\bigr).
$$
Thus if $\Delta\le\delta$,
$$
 t(B_M,W)-p^{67+4M}\ \ge\ p^{4M}(M\kappa-C_{67})\Delta. \tag{6}
$$
No implicit smallness parameter depends on $M$.

## 3. A global pointwise bound for the decorated root

If $d=d_W(x)>0$, complete $H$ plus the bridge to a complete bipartite graph with root $x$ in a class of $\alpha=23$ vertices and with $\beta=13$ vertices in the other class. The rooted density can only decrease. For the complete graph, integrate the $\alpha-1$ unmarked vertices on the root side first and draw the other $\beta$ vertices with density $W(x,y)/d$. Jensen gives the following lower bound for its rooted density:
$$
 d^{\beta}\left(\int \left[\frac{K(x,u)}{d}\right]^{\beta}du\right)^{\alpha-1}
 =d^{\beta(2-\alpha)}\left(\int K(x,u)^\beta du\right)^{\alpha-1}
 \ge c(x)^{\beta(\alpha-1)/2}.
$$
The last step uses $d\le1$, $\alpha,\beta\ge2$ and Jensen for the $\beta/2$th power of $K^2$. If $d=0$, then $K(x,\cdot)=0$ for almost every other variable and $c(x)=0$, so the bound still holds. Consequently
$$
 b(x)\ge c(x)^{143},\qquad t(B_M,W)\ge (p^4+\Delta)^{M+143} \tag{7}
$$
by (2) and Jensen. If $p\ge1/4$ and $\Delta\ge\delta$, divide (7) by $p^{4M}$. The ratio is at least
$$
 p_0^{572}(1+\delta)^M\ge 2^{-1144}(1+M\delta)\ge1
$$
for $M=2^{3850}$. This gives the stronger estimate $t(B_M,W)\ge p^{4M}$ in the far regime. Combining with (6) yields $t(B_M,W)\ge p^{67+4M}$ at every $p\ge1/4$.

## 4. Both colors, including a very sparse one

Let $P,Q=1-P$ have densities $p\ge q=1-p$, and put $E=67+4M$. If $q\ge1/4$, the fixed-density estimates just proved for each color give the strong sum directly. Suppose $q<1/4$, so $p>3/4$, and write $\Delta=t(C_4,P)-p^4$.

If $\Delta\ge\delta$, (7) gives $t(B_M,P)\ge p^{4M}$. This is at least $p^E+q^E$, because $q/p\le1$ and $p^{67}+q^{67}\le1$. This case does not use any assumption on the sparse side.

If $\Delta\le\delta$, (6) gives $t(B_M,P)-p^E\ge (M\kappa/2)p^{4M}\Delta$, since $M\kappa\ge2C_{67}$. For $Q$ define $b_Q,c_Q,n_Q,I_Q$ analogously, with $I_Q=\int b_Q(c_Q-q^4)$. Its centered kernel is minus the centered kernel for $P$, so its invariant $R$ in (1) equals that of $P$ and is $\le33\Delta$. Crucially, we require counting estimates on the two **fixed** simple bipartite graphs with 67 and 71 edges, not on a graph with $E$ edges:
$$
 n_Q-q^{67}\ge-C_{67}\Delta,\qquad I_Q\ge-(C_{71}+C_{67})\Delta .
$$
Indeed $\int b_Qc_Q$ is the bridged graph with just one square, and $\int b_Q$ is the bridged graph with no squares. Their constant-kernel terms cancel after subtraction. The pointwise tangent inequality for the $M$th power on $[0,\infty)$ yields
$$
 t(B_M,Q)-q^E
 \ge-[C_{67}q^{4M}+M(C_{71}+C_{67})q^{4M-4}]\Delta .
$$
This remains valid at $q=0$ since $M>1$; no division by $q$ is used. The bracket divided by $p^{4M}$ is at most
$$
 M\,2^{81}(1/3)^{4M-4}\le M2^{-599}=M\kappa/2 ,
$$
using $C_{67}<2^{73}$, $C_{71}+C_{67}<2^{78}$, $p^{-4}<4$, $q/p<1/3$, $M\ge1$, and $4M-4\ge680$. The big-color margin absorbs the small-color loss. This proves strong commonness in all cases.

## 5. Why the non-Sidorenko kernel still works with a bridge and a marked bouquet

We need **rooted, uniform control** rather than mere convergence of the ordinary square density. All facts about the external construction below are read from [O], not inferred from its final counterexample in a single finite host.

Fix the even rank parameter, finite set of matrix coordinates $\mathcal K$, vertex type priors, thinning and sufficiently small positive dilution in [O, §§3.1–3.5] **before** passing to infinity in odd primes $r$. Write $W_r$ for its nonnegative finite rectangular kernels, from the point space $X$ to the face space $Y$. Each vertex carries one type and a tuple of independent uniform matrices. Per [O, (3.6)] an incidence kernel, conditional on endpoint types, is the expectation of a product of mean-one rank-layer functions of $x_c-y_c$ over a random set of active coordinates with sign marks. Consequently $W_r$ has each row mean and each column mean exactly 1: fix either endpoint, average over the independent uniform coordinate matrices on the other side, and then average the activation package. This is valid for every type, including the inactive type.

Let $C_r^X(a,x)$ be the rectangular square density rooted at $(a,x)\in X$, with the other three vertices drawn in the prescribed sides of the square; likewise $C_r^Y(b,y)$. For each fixed root type, the rooted value is independent of its entire matrix tuple. Indeed simultaneously translate all four vertices' matrix vectors by the same additive vector, separately by coordinate: every difference $x_c-y_c$ is preserved and uniform draws of each of the other vertices remain uniform. Thus it suffices to analyze the square conditional on the four types with the root matrix uniform, without any uniform-in-matrix estimate from [O].

Take the square whose points are 0 and 1 and whose faces are 0 and 1 in [O, Table 1]. Conditional on the types, draw the four incidence activation/sign packages independently, as allowed in the product of expectations in [O, (3.6)]. At a fixed coordinate, after conditioning on packages, Lemma 3.1 and (3.4) apply with active set contained in this square (adjoin the unused independent matrix variables for the other source vertices). Hence the limiting coordinate integral is 1 plus the product of four active signs, with inactive factors defined as zero: the chosen square is the only full square possible. Multiply over the fixed finite set of independently integrated coordinates. The errors remain $o(1)$, uniformly over the finite package possibilities. In the expansion of the limiting product, choosing signs on a nonempty set $\gamma$ of coordinates gives a product of four independent single-incidence conditional expectations of $\mathbf{1}_{\gamma\subseteq S}\prod_{c\in\gamma}\xi_c$. Each vanishes by (3.7), preserved by their thinning (3.20) and dilution. Only the empty choice remains, contributing exactly one. This holds for any assignment of the four vertex types (including repeated types), on either rooted side. Types are from fixed finite sets, so the convergence to 1 of both $C_r^X$ and $C_r^Y$ is uniform over types and all matrix labels.

On $X\times Y$ with independent product coordinates, use the symmetric nonnegative kernel of [O, (3.28)]:
$$
 V_r((x,y),(x',y'))=W_r(x,y')W_r(x',y).
$$
Every row of $V_r$ integrates to 1 because both rectangular marginals equal 1. The rooted square in $V_r$ at $(x,y)$ is exactly $c_r(x,y)=C_r^X(x)\, C_r^Y(y)$: conditional on this root, the two rectangular factors use disjoint remaining random coordinates, with the root lying on opposite sides in the two factors. (The symbols $x,y$ now include types.) Therefore $\|c_r-1\|_\infty\to0$, and for the **fixed finite** $M$, $\|c_r^M-1\|_\infty\to0$ as well. For $h_r$ the nonnegative rooted $H$ density in $V_r$, bridge integration gives
$$
 t(B_M,V_r)=\int h_r(x)\,[T_{V_r}c_r^M](x)\,dx,\qquad
 |t(B_M,V_r)-t(H,V_r)|\le t(H,V_r)\|c_r^M-1\|_\infty.
$$
This inequality uses only nonnegativity and exact row sums, not any uniform sup-norm bound on $V_r$ or $h_r$.

By [O, (3.24)–(3.25), (3.28)] with the very same fixed parameters, $t(H,V_r)\to L<1$. Hence $t(B_M,V_r)\to L<1$. At some finite prime choose a strict witness and scale $V_r$ by its finite maximum. The result is a $[0,1]$ graphon of positive mean violating the ordinary Sidorenko inequality for $B_M$ by homogeneity. The standard sampling argument transfers a positive strict gap to some finite simple graph: for a fixed $d$-edge, $v$-vertex pattern, collision probability is at most $\binom{v}{2}/n$, whereas expected sampled edge density is $(1-1/n)p$. Jensen shows that for $n>(\binom{v}{2}+dp^d)/(p^d-t(B_M,W))$ some realization has too few homomorphisms. No uniform density or boundedness in $r$ is claimed. The proof of the external rank-layer lemma over matrix spaces is not repeated here.

## 6. Review hooks and priority limits

- [G: Grzesik, Lee, Lidický and Volec, CPC 31 (2022), p. 908](https://doi.org/10.1017/S0963548322000074): ordinary two-color converse question **not** requiring connectedness. We impose connectedness as a strengthening, not as an attribution to their conjecture.
- [KVW: Král’, Volec and Wei, *Common graphs with arbitrary chromatic number*](https://arxiv.org/abs/2206.05800): already use joining a core graph by a path to a dense bipartite padding graph and spectral estimates. Neither the general connected-padding idea nor the use of bridges to reduce correlations originates in the present note. Their Theorem 23 assumes a core of girth at least 50, whereas this core has girth four. It does not supply this strong-common/non-Sidorenko separation. [Ko and Lee](https://arxiv.org/abs/2207.09427) handle highly connected common graphs, without establishing this bipartite strong-common/non-Sidorenko separation.
- [Lee and Noel, *Disconnected Common Graphs via Supersaturation*, eq. (2)](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v33i2p1/pdf/): strongly common definition; [Král’–Noel–Norin–Volec–Wei](https://arxiv.org/abs/2006.09422) study color count and Sidorenko under different quantifiers.
- [O: OpenAI, *A counterexample to Sidorenko's conjecture*, September 2026, fixed PDF](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Sidorenkos-conjecture-September-23-2026/paper.pdf), Table 1, Lemma 3.1, equations (3.4), (3.6), (3.7), (3.20), (3.24)–(3.28). The square argument is an additional consequence of these inputs; the row/column regularity follows already before symmetrization.
- Two separate AI-assisted internal reviews checked (3)–(7), the sparse-color tangency, pointwise root types and normalization steps. Neither is external peer review or a formal verification. A bounded literature search did not locate the same separation; it is not a certificate of priority. No connectedness higher than one is asserted, and no status of $H$ itself as common/uncommon is determined.


### Checks included in this directory

From this directory run, with Python 3 and no third-party packages:

~~~sh
python3 -B -O verify.py
python3 -B -O reviews/controls_1.py
python3 -B -O reviews/controls_2.py
~~~

[Review 1](reviews/review_1.md) and [Review 2](reviews/review_2.md) document two independent internal readings, with their [first](reviews/controls_1.py) and [second](reviews/controls_2.py) exact control programs. The [main checker](verify.py) carries the complete labelled incidence table and checks its fingerprint, connectivity, arithmetic constants, and a finite grid of rooted identities. It has no fallback to external data. These checks do not enumerate the enormous graph, supply a numerical violating host, or prove the analytic or finite-field lemmas. All three scripts use explicit failure conditions that remain active with Python's optimization flag.
