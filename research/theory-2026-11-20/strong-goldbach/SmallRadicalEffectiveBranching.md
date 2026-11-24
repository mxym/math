# Genuine branching, not full path length, controls the moving-seed rank test

This is a refinement of the exact acyclic elimination in [the feedback-depth proof](SmallRadicalFeedbackDepthRank.md). Keep its true all-composite closed factor set \(C\), independent unit prime seeds \(P\), \(L=\log N\), either moving local hypothesis, and permitted exponent \(\theta\) (so \(b_{\rm rad}+c+\theta<1\) or \(c+\theta<1\), respectively). In particular each row has at least two prime factors with multiplicity. Fix any retained \(R\supseteq P\) with induced acyclic complement \(U=C\setminus R\), and let \(K=A_{RR}+A_{RU}(I-A_{UU})^{-1}A_{UR}\) be its first-return multiplicity matrix. Put \(D=\max_i\Omega(N-x_i)\le L/\log3\).

Define the following four integer parameters; empty maxima here are zero.
* \(h\) is the largest number of \(U\)-vertices along a path inside \(U\).
* \(\beta\) is the largest number of vertices with at least two outgoing **multiplicity-counted** arcs into \(U\) along a path inside \(U\). A vertex supporting two copies of the same arc counts.
* \(H\) is the largest number of vertices along a path wholly in \(U_\mathord{>}=\{u\in U:u>\sqrt N\}\).
* \(\tau\) is the largest number of vertices of \(U_\mathord{\le}=\{u\in U:u\le\sqrt N\}\) along a path inside \(U\).

Set
\[
 M=\min\{1+D^{h+1},\quad 1+D+D^{\beta+2}h,\quad
                        1+[D(H+1)]^{\tau+1}\},\qquad
 W=(|R|-|P|+1)\log M.
\]
For all sufficiently large \(N\), \(W\le L^\theta\) implies linear independence of the \(P\)-coordinate classes in \(\mathbb Q^C/\operatorname{row}_{\mathbb Q}(I-A)\). Equivalently, along any asymptotic family one could allow \(W\le L^{\theta+o(1)}\) by using the strict analytic margin. This is substantive when the deleted DAG has long paths but limited interior branching, or only a few visits to small-prime labels.

## 1. First-return bounds

The original depth bound gives \(\|K_i\|_1\le D^{h+1}\). Here are two independent stronger bounds, keeping multiplicities exactly.

**Bound by branching occurrences.** For a given retained start \(i\), direct returns contribute at most \(D\). There are at most \(D\) choices for a first \(U\)-child. For each such choice, unfold only arcs inside \(U\), counting copies as distinct. This is a finite rooted tree with depth (number of vertices on a path) at most \(h\), branching factor at most \(D\), and at most \(\beta\) true branch vertices along each path. Contracting unary vertices, or inducting on the maximal remaining \(\beta\), gives at most \(D^\beta\) leaves. The full tree has at most \(hD^\beta\) vertices: each level has at most the total number of leaves, since subtrees at a fixed level are disjoint. Each occurrence in this tree offers at most \(D\) arcs returning to \(R\); sum over the initial child choices to obtain \(\|K_i\|_1\le D+D^{\beta+2}h\). All multiplicity is accounted for by the unfolding and the last returning arc. If \(h=0\), only the direct term remains.

**Bound by visits to small labels.** Each vertex of the full graph has at most one outgoing arc to a label \(>\sqrt N\), including multiplicity: two such factors would multiply to more than \(N\), while the complement is \(N-x<N\). In particular, from a retained or small-\(U\) starting vertex, the possible succession through high \(U\)-vertices is a single chain of length at most \(H\), regardless of the labels of the starting vertex. Group into one macro step all paths from this start to the next point in \(R\cup U_\mathord{\le}\) whose interior is high \(U\). There are at most \(D(H+1)\) such choices counting multiplicities: at each of the at most \(H+1\) start/chain vertices there are at most \(D\) exits, and the internal high links have multiplicity one. A first return to \(R\) splits into these macro steps uniquely. No macro path can continue forever before reaching \(R\), since its expansion would be a directed walk in finite acyclic \(U\), where outdegree in the full closed graph is positive. Its internal low labels appear along the expanded \(U\)-path, hence number at most \(\tau\). Thus the unfolded macro tree has at most \([D(H+1)]^{\tau+1}\) leaves. This proves the third bound, also when \(H=0\) or \(\tau=0\). It does not claim that a vertex with many outgoing arcs must itself be a small label.

Since \(K\) is nonnegative, \(\| (I-K)_i\|_2\le1+\|K_i\|_1\le M\).

## 2. Determinant size and arithmetic

In the supported-dependence proof let \(t\) count the independent nonseed columns of \(I-K\); \(t\le |R|-|P|\). The signed-minor witness uses order \(t+1\), not the full retained dimension. Hadamard therefore bounds the size parameter by \(\log\mathcal B\le O(1)+(t+1)\log M\le O(1)+W\). The integer lift \((I_R,-B_{RU}B_{UU}^{-1})B=(I-K,0)\) from the preceding proof keeps every cofactor combination an integer combination of actual complementary rows. Their unit products are \(-1\) modulo \(\ell^{v_\ell(N)}\); after squaring, the supported seed relation gives a nonzero \(\Xi\) with \(v_\ell(\Xi)\ge v_\ell(N)\ge L^{1-o(1)}\). Insert the new size bound into Yu (1.9) with (1.10)–(1.11), as in that proof. For \(W\le L^{\theta+o(1)}\), the upper estimate is still \(L^{b_{\rm rad}+c+\theta+o(1)}\) or \(L^{c+\theta+o(1)}\), respectively. The same contradiction proves independence.

## 3. Example of a necessary condition in the genuine closure

If \(F\) is any feedback set with \(|F|\le s=|P|\), take \(R=P\cup F\). Independently eliminating outside \(F\) alone shows full nullity \(\nu\le |F|-1<s\) because each of the two or more original arcs out of each \(f\in F\) extends to a first return; closure and the DAG are essential. Thus independence is impossible and \(W>L^\theta\). In particular, because \(|R|-s+1\le s+1\), both
\[
 \log(1+D+D^{\beta+2}h)>\frac{L^\theta}{s+1},\qquad
 \log(1+[D(H+1)]^{\tau+1})>\frac{L^\theta}{s+1}
\]
are necessary. The first shows that a polynomial-in-\(L\) deletion depth by itself is not a way around the rank obstruction with small \(\beta\). The second yields the more physical high-chain condition
\[
 \log(H+1)>
 \frac{L^\theta/(s+1)-\log 2}{\tau+1}-\log D .
\]
For example, if every path in \(C\setminus(P\cup F)\) visits at most \(T\) labels \(\le\sqrt N\) for fixed \(T\), there must be a chain entirely above \(\sqrt N\) of length at least \(\exp(\Omega_T(L^\theta/s))\) for large \(N\), rather than merely a long arbitrary path. The chain is simple and follows the unique possible large-factor successor.

At a hypothetical Goldbach failure apply this to the closure of the selected genuine seeds. This remains a conditional necessary structure; it neither rules out such high chains nor makes any assertion about terminal SCCs or prime-pair existence. The arithmetical threshold \(\sqrt N\) is used only for the uniqueness of the above-threshold factor, not to assume every label has an above-threshold successor.
