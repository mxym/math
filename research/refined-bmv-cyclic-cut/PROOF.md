# A sharp cut criterion for two-letter trace words and the exponent threshold for the clustered BMV upper bound
Research draft, 2026-11-18. Independently rechecked by another AI; not externally peer reviewed. The trace-exponential lower bound is not addressed.

## 1. Single-word theorem

Let $X,Y$ be positive semidefinite complex matrices of the same arbitrary finite size. Consider the cyclic word
$$W=X^{a_1}Y^{b_1}\cdots X^{a_k}Y^{b_k},\qquad a_i,b_i>0,\quad \sum a_i=\sum b_i=1.$$
Nonnegative exponent lists are handled by deleting zero powers (convention $X^0=I$), merging adjacent runs of the same matrix, including cyclically, before applying the theorem. Unnormalized positive totals are handled by replacing the two base matrices by their total powers. Build a bipartite *cycle multigraph* with left vertices the X runs and right vertices the Y runs; each boundary between successive runs around the cyclic trace contributes one edge, so for $k=1$ the two vertices have two parallel edges. For left subset $I$ and right subset $J$ let $c(I,J)$ be the number, with multiplicities, of edges from $I$ to the complement of $J$, and put
$$d(I,J)=a(I^c)+b(J)+c(I,J)/2.$$

**Theorem 1.** The following are equivalent:
1. $|\operatorname{Tr}W|\le\operatorname{Tr}(XY)$ for all finite-dimensional $X,Y\ge0$.
2. Every cut satisfies $d(I,J)\ge1$.
3. There are edge masses $0\le s_e\le1/2$ with the sum incident to each left vertex $i$ equal to $a_i$ and the sum incident to each right vertex $j$ equal to $b_j$.

In the valid case the optimal constant is 1 (the identity matrices attain it). Otherwise no finite multiplicative constant works: even real positive definite matrices of size 3 give unbounded positive real trace ratios. In particular, this is a classification of exponent *patterns* in the all-dimensional trace inequality of Ando, Hiai and Okubo (their Eq. (1.6)), not a classification for a fixed nontrivial pair of matrices. It is not Drury's operator-norm inequality.

**Flow equivalence.** Form the network source→left with capacities $a_i$, left→right along each cyclic edge with capacity $1/2$, and right→sink with capacities $b_j$. A cut whose source side contains precisely the left vertices in $I$ and right vertices in $J$ has capacity $d(I,J)$. The total source/sink capacities both equal 1. A flow of value 1 saturates them all. Finite max-flow/min-cut proves 2 iff 3, also for real capacities.

**Sufficiency.** At each run, split its power into its two incident edge masses, in cyclic order. Regroup around the circle so a boundary of mass $s>0$ gives either $X^sY^s$ or $Y^sX^s$. Remove zero factors; cyclic rotation does not affect the trace. The masses sum to 1, counted over edges (by summing left margins). With $0<s\le1/2$, Araki's trace inequality gives
$$\|X^s Y^s\|_{1/s}^{1/s}
 =\operatorname{Tr}\big(Y^s X^{2s}Y^s\big)^{1/(2s)}\le\operatorname{Tr}\big(Y^{1/2}XY^{1/2}\big)=\operatorname{Tr}(XY).$$
Indeed apply Araki–Lieb–Thirring in its $r=1/(2s)\ge1$ form to $D=X^{2s}$ and $E=Y^{2s}$; the reverse product has the same singular values by adjunction. Noncommutative Hölder for the resulting product gives $|\operatorname{Tr} W|\le\prod_{e:s_e>0}(\operatorname{Tr}XY)^{s_e}=\operatorname{Tr}(XY)$. This also holds when $\operatorname{Tr}(XY)=0$.

**Provenance of the valid direction.** This direction also follows from the older Ando–Hiai–Okubo Theorem 2.1 (conditions (1.8)–(1.9)); it is not claimed as a new trace bound independent of their work. Indeed rotate at the beginning of a balanced edge factor, encode a forward factor as one run pair with exponents \((s,s)\), and a reverse factor as two run pairs \((0,s),(s,0)\). Grouping completed edge factors never changes the cumulative difference. After a left entry the left-minus-right prefix difference is either 0 or \(s\), and after a right entry the right-minus-left prefix difference is either 0 or \(s\). Thus both AHO inequalities hold because \(s\le1/2\); their theorem permits zeros. Our max-flow argument identifies which cyclic patterns admit this proof; the complementary test family proves necessity for the weaker cyclic trace comparison itself.

**Necessity and unboundedness.** The vanishing-overlap case of the rank-one projection walk is already due to Cha–Lee (Propositions 2–3). Allowing the formerly zero overlap to decay as $\sqrt t$ assigns a cost of $1/2$ to each crossing. For any violated cut let $d=d(I,J)<1$. In $\mathbb R^3$, for $0<t<1/4$, put
$$p=(1,0,0),\quad u=(0,-1,1)/\sqrt2,\quad
q_t=(\sqrt t,0,\sqrt{1-t}),\quad v_t=(\sqrt{1-t},-1,-\sqrt t)/\sqrt2.$$
The pairs $(p,u)$ and $(q_t,v_t)$ are orthonormal. Write $P_z=zz^T$ and set $X=P_p+tP_u$, $Y=P_{q_t}+tP_{v_t}$. The four cross inner products are positive:
$$p^Tq_t=\sqrt t,\quad p^Tv_t=u^Tq_t=\sqrt{1-t}/\sqrt2,\quad u^Tv_t=(1-\sqrt t)/2.$$
The last three are ≥1/4 for the stated t. Moreover
$$\operatorname{Tr}XY=t+t(1-t)+t^2(1-\sqrt t)^2/4\le 3t.$$
Each run has the two-term expansion $X^{a_i}=P_p+t^{a_i}P_u$ or $Y^{b_j}=P_{q_t}+t^{b_j}P_{v_t}$. Every term in the word trace is nonnegative: a cyclic trace of unit rank-one projections is the product of the successive real inner products, and all successive factors are cross-color. Select $p$ on left vertices $I$, $u$ on $I^c$, $v_t$ on right vertices $J$, and $q_t$ on $J^c$. The selected coefficient contributes $t^{a(I^c)+b(J)}$. Its $c(I,J)$ small overlaps contribute $(\sqrt t)^c$, and all remaining factors are bounded below by $1/4$. Therefore
$$\operatorname{Tr}W/\operatorname{Tr}XY\ge (4^{-2k}/3)\,t^{d-1}\longrightarrow+\infty.$$
For any prescribed target ratio choose finite t first; adding a sufficiently small positive multiple of $I$ to both matrices preserves the strict comparison by continuity of positive real powers. This supplies the same unbounded ratios with real positive definite matrices. No exponent-zero kernels are used.

**Four-factor corollary.** On the *open* square $0<a,b<1$ for $\operatorname{Tr}X^aY^bX^{1-a}Y^{1-b}$, the universal region is exactly $|a-\tfrac12|+|b-\tfrac12|\le\tfrac12$. Indeed the cycle is $K_{2,2}$; zero-crossing cuts are automatic, and a one-crossing cut is specified by one left vertex and one right complement vertex. The minimum among these cut capacities is $\min(a,1-a)+\min(b,1-b)+1/2$. Outside the diamond the ratio is unbounded. On the boundary of the square a zero power is removed and the trace equals $\operatorname{Tr}XY$ identically. The positive diamond is the known Ando–Hiai–Okubo Corollary 2.2(i); previously published counterexamples outside it are not ours. In particular, Carlen–Lieb (2022), after Example 4.2 in §4, explicitly ask about sharpness of the upper-quadrant condition $a+b\le3/2$; their example is $a=b=0.79$. Here every nondegenerate point outside the diamond fails.

## 2. Symmetrized words: the integer threshold

For positive integers $n,m$, write $H_{n,m}(A,B)$ for the average of the ordinary traces of all linear words with $n$ copies of $A$ and $m$ of $B$, normalized by $\binom{n+m}{n}$. The average is real by reversal/conjugation. If one multiplicity is zero there is just one word and equality is automatic; the reciprocal criterion concerns positive integers only.

**Theorem 2.** The clustered upper inequality $H_{n,m}(A,B)\le\operatorname{Tr}(A^nB^m)$ holds for every finite-dimensional positive definite pair iff $1/n+1/m\ge1/2$. In that range each individual word satisfies the upper bound on its absolute trace. Off that range the positive real average-to-cluster ratio is unbounded for real positive definite matrices of size 3. The least total word length admitting failure is nine, at $(4,5),(5,4)$. The balanced case $(4,4)$ is already in Ando–Hiai–Okubo (2000), and Cha–Lee already gave divergence for all $n,m\ge5$.

**Valid side.** Take any word and merge cyclic runs. Its left weights, normalized for $X=A^n$, are at least $1/n$; its right weights, for $Y=B^m$, at least $1/m$. Show every cut has capacity at least 1. With $c\ge2$ this is immediate. If $c=1$, $I^c,J$ must both be nonempty: all left vertices would emit two edges into each outside right vertex, while if $J$ were empty each selected left vertex would emit two edges. Thus $a(I^c)+b(J)\ge1/n+1/m\ge1/2$. If $c=0$, cuts with $I=\varnothing$ or $J$ all right vertices are automatic; otherwise pick a left vertex in $I$ and a right vertex outside $J$. For $k\ge2$ the two distinct neighbors of the first belong to $J$, and the two distinct neighbors of the second to $I^c$. Thus $a(I^c)+b(J)\ge 2/n+2/m\ge1$. For $k=1$ the nonvacuous zero-crossing case cannot occur. Apply Theorem 1 and average.

**Invalid side and credit.** Use the rank-one projection path and cyclic bridge word of Cha–Lee (Props. 1–5 and Cor. 2), but with different small spectral weights on the two sides. In their notation take $p=(1,0,0),\,u=(0,-1,1)/\sqrt2,\, q=(0,0,1),\,v=(1,-1,0)/\sqrt2$, $A=P_p+t^mP_u$, $B=P_q+t^nP_v$. Then the sole zero cross-overlap is $p^Tq$; $p^Tv=u^Tq=1/\sqrt2$, $u^Tv=1/2$. All cyclic word trace expansions are nonnegative. The threshold failure $2(n+m)<nm$ implies $n,m\ge3$. In $A^{n-2} B A B^{m-2} A B$ select $p,v,u,q,u,v$ at the six runs. This single term contributes $t^{2m+2n}/16$. Meanwhile $\operatorname{Tr}(A^n B^m)=t^{nm}+t^{2nm}/4$. Therefore
$$\frac{H_{n,m}(A,B)}{\operatorname{Tr}(A^n B^m)}
 \ \ge\ \frac{t^{2(n+m)-nm}}{16\binom{n+m}{n}(1+t^{nm}/4)}\ \longrightarrow\ +\infty.$$
Regularize for fixed t as above if positive definiteness is required. For $n+m\le8$, $1/n+1/m\ge4/(n+m)\ge1/2$; at total nine only $(4,5),(5,4)$ fail.

**Scope.** This classifies exactly the *upper* side of the refined BMV comparison (OQP 40). The upper side was already disproved in general. Nothing here establishes or refutes the separate open lower comparison $H_{n,m}\ge\operatorname{Tr}\exp(n\log A+m\log B)$, and nothing here is a new proof of Stahl's original BMV theorem.
