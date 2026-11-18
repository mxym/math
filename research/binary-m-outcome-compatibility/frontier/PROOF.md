# The universal visibility frontier and equality cases

Fix complex dimension $d\ge2$ and $m\ge2$ labels. A binary POVM has effects $(I\pm A)/2$ for a Hermitian contraction $A$; the other POVM has positive effects $B_1,\ldots,B_m$ summing to $I$. Zero effects are allowed. Give the binary POVM visibility $a$ and the other visibility $b$, both in $[0,1]$. The two noisy POVMs have effects $(I\pm aA)/2$ and $C_j=eI+bB_j$, where $e=(1-b)/m$. The noise is fixed and uniform over *outcome labels*, even originally zero labels. A joint POVM must have exactly these marginals.

For a fixed pair, write $h_{A,B}(b)$ for the largest compatible $a$ at fixed $b$, and write $s_{A,B}$ for its largest compatible common visibility $a=b$. These maxima exist: joint POVMs form a compact set and the marginal equations are closed. For fixed $b$, the feasible $a$ form an interval starting at zero by classical randomization on the binary side. For common visibility the same conclusion follows by convexly mixing a joint POVM with the joint uniform POVM.

**Theorem.** Define
$$
f_m(b)=(m-2)e+2\sqrt{e(e+b)},\qquad
s_* = \frac12\left(1+\frac1{1+\sqrt m}\right).
$$

1. Every pair is compatible at $(a,b)$ if and only if $a\le f_m(b)$. This is the pointwise consequence of the [earlier trace-norm inequality and witness](../PROOF.md).
2. The following are equivalent: (i) $s_{A,B}=s_*$; (ii) $h_{A,B}(b)=f_m(b)$ for some $0<b<1$; (iii) the same equality holds for every $0<b<1$; (iv) there is a nonzero common reducing subspace $K$ of $A$ and all the $B_j$ on which $A$ is a Hermitian involution $S$ and $B_j$ are pairwise orthogonal projections $P_j$ summing to $I_K$, with $P_j S P_j=0$ for every $j$. No condition on the complementary summand is imposed.
3. If $m=2,3$, every pair in part 2 contains a reducing qubit block on which $S$ swaps an orthonormal basis, two labels give its coordinate projections, and the other labels vanish. For each $m\ge4$ there is a worst-case pair already in dimension four having no proper nonzero common reducing subspace.

Part 2 classifies worst pairs at interior $b$, not at $b=0,1$. Part 3 asserts neither that every worst pair is itself a qubit pair nor that qubit blocks cease to exist in all worst pairs for $m\ge4$.

## 1. A support function with two independent visibilities

Let $T$ be Hermitian. Writing each joint effect as $(C_j\pm D_j)/2$ gives the requirements $-C_j\le D_j\le C_j$ and $\sum_j D_j=aA$. The support of the order interval $[-C,C]$ in direction $T$ is $\|C^{1/2}TC^{1/2}\|_1$: first restrict to the support of $C$, then conjugate by $C^{1/2}$. Indeed, $C\pm D\ge0$ annihilate $\ker C$ by positivity. Separation from the compact convex sum of these intervals gives
$$
(a,b)\text{ compatible for }(A,B)
\iff a\operatorname{Tr}(AT)\le L_b(T):=\sum_j\|C_j^{1/2}TC_j^{1/2}\|_1\quad\text{for every }T=T^*.
$$
The [pointwise bound](../PROOF.md) is $L_b(T)\ge f_m(b)\|T\|_1$; its strict scalar steps are recalled below. It suffices because $\operatorname{Tr}(AT)\le\|T\|_1$. The padded Hadamard/computational qubit pair from [Bluhm et al., §6.2](https://arxiv.org/pdf/2512.17706) gives equality: take $A=\sigma_x$, $B_1,B_2$ the coordinate projections, all other $B_j=0$ and $T=\sigma_x/2$. Each of the first two labels contributes $\sqrt{e(e+b)}$ and each padded label contributes $e$. Here $\operatorname{Tr}(AT)=\|T\|_1=1$. In higher dimension take this qubit as a direct summand and extend $T$ by zero. This proves part 1, including $b=0$ and $b=1$. Note
$$
f_m(b)=1-(\sqrt{e+b}-\sqrt e)^2,
$$
so $f_m$ decreases strictly from $1$ to $0$ and $0<f_m(b)<1$ in the interior. Its unique fixed point is $s_*$, by direct substitution; this is the common threshold already proved in the earlier note.

## 2. A saturated witness

There are two ways to reach the same interior contact $(a_0,b_0)$ with $a_0=f_m(b_0)>0$. If (i) holds, take $a_n=b_n\downarrow s_*$ from above, less than 1, and set $a_0=b_0=s_*$. If (ii) holds, fix $b_n=b_0$ and let $a_n\downarrow a_0$ strictly from above in $[0,1]$. In either case each pair of noisy measurements at $(a_n,b_n)$ is incompatible. Choose a separating Hermitian $T_n$ normalized by $\|T_n\|_1=1$ with $a_n\operatorname{Tr}(AT_n)>L_{b_n}(T_n)$. Finite-dimensional compactness gives a converging subsequence with nonzero limit $T$ of trace norm one. By continuity of square roots and norms,
$$
a_0\ \ge\ a_0\operatorname{Tr}(AT)\ \ge\ L_{b_0}(T)\ \ge\ f_m(b_0)=a_0.
$$
On $K=\operatorname{supp}|T|$, set $R=|T||_K>0$, $S=\operatorname{sgn}(T)|_K$. Then $S$ is a Hermitian involution commuting with $R$. Equality $\operatorname{Tr}(AT)=1$ forces $Av=\pm v$ for each nonzero eigenvector of $T$ with eigenvalue of sign $\pm$: the weighted average of the signed expectations saturates 1, and $I\mp A\ge0$. Thus $K$ reduces $A$ and $A|_K=S$.

We now justify the rigidity of the final inequality in the chain. Write $J:K\to\mathbb C^d$ for the inclusion. For label $j$ define $F_j=J^*B_jJ$, $X=R^{1/2}F_jR^{1/2}$, $Y=SXS$. With $e=(1-b_0)/m>0$, the trace norm for that label is the **unsquared** fidelity of $P=eR+b_0X$ and $Q=eR+b_0Y$. Indeed, $M=C_j^{1/2}JR^{1/2}$ and $N=MS$ satisfy $MN^*=C_j^{1/2}TC_j^{1/2}$, $M^*M=P$ and $N^*N=Q$. Their polar isometries preserve all nonzero singular values. No invariance under $B_j$ has yet been assumed.

Use $2F(P,Q)=\min_{H>0}\operatorname{Tr}(PH+QH^{-1})$. For positive definite $P,Q$ the minimum is attained at $P^{-1/2}(P^{1/2}QP^{1/2})^{1/2}P^{-1/2}$; see [the earlier proof](../PROOF.md) or [Watrous, Theorem 3.19](https://cs.uwaterloo.ca/~watrous/TQI/TQI.double.3.pdf). For each vector $u$ in an orthonormal eigenbasis of a minimizer, put
$$
r=\langle u,Ru\rangle>0,\quad x=\langle u,Xu\rangle/r,\quad y=\langle u,Yu\rangle/r.
$$
Both $x,y\in[0,1]$. Denote $p=\sqrt e>0$ and $q=\sqrt{e+b_0}>p$. The corresponding summand in half the trace is at least $r\sqrt{(e+b_0 x)(e+b_0 y)}$ by scalar AM–GM. Each square root dominates its chord because
$$
e+b_0x-[p+(q-p)x]^2=(q-p)^2x(1-x).
$$
Multiplying the two positive chords and dropping $(q-p)^2xy$ gives the final lower bound $r[e+p(q-p)(x+y)]$. Summed over $u$ and $j$ this is $f_m(b_0)\operatorname{Tr}R$: use $\operatorname{Tr}X=\operatorname{Tr}Y$ and $\sum_j X_j=R$. Every gap in the estimate is nonnegative. Equality therefore forces $(x,y)$ to be $(1,0)$, $(0,1)$ or $(0,0)$ for every $u$ at every label.

For fixed $j$, the vectors $w=R^{1/2}u$ form a basis of $K$, not necessarily orthonormal. Their normalized expectations for the positive contractions $F_j$ and $SF_jS$ are precisely $x$ and $y$, since $R$ commutes with $S$. Extreme expectations are eigenvalues on the same vectors: $F_jw=xw$ and $SF_jSw=yw$. The basis implies $F_j^2=F_j$ and $F_j(SF_jS)=0$, hence $F_j S F_j=0$. This projection also forces $B_j$ to preserve $K$: any eigenvector in $K$ of $F_j$ with eigenvalue $0$ or $1$ has the same extreme expectation for the *full* positive contraction $B_j$ and is its eigenvector. Self-adjointness gives reduction. Finally $\sum_j F_j=I_K$; positive projections summing to the identity are pairwise orthogonal (test on the range of each). This proves (i) or (ii) implies (iv).

## 3. The converse and the number of labels

Given (iv), take $T=S$ on $K$ and zero off it, so $\operatorname{Tr}(AT)=\|T\|_1=\dim K$. Write $P=P_j$ and $P'=SPS$ on $K$. The two projections are orthogonal, because $PSP=0$. In the fidelity expression of §2 the matrices $eI+bP$ and $eI+bP'$ therefore commute. The contribution is $e\dim K+2[\sqrt{e(e+b)}-e]\operatorname{rank}P$ by splitting along their ranges and orthogonal complement. At $e=0$ the formula follows directly or by continuity. Summing gives $L_b(T)=f_m(b)\dim K$. The same witness works at every $b$: if $a>f_m(b)$ it separates. This proves (iv) implies (iii) and (i); trivially (iii) implies (ii). The complement cannot spoil compatibility below the universal bound, and cannot hide a witness supported on $K$.

For $m=2$ or 3, let $K_i=P_iK$, $S_{ij}=P_iS|_{K_j}$. Then $S_{ii}=0$. For distinct $i,j,k$, the $(i,k)$ block of $S^2=I$ has at most one surviving term, so $S_{ij}S_{jk}=0$. Set $V_{ij}=\operatorname{ran}S_{ij}\subseteq K_i$. At fixed $i$ these ranges are orthogonal because $S_{ij}^*S_{ik}=0$ when $j\ne k$, and span $K_i$ since $\sum_{j\ne i}S_{ij}S_{ij}^*=I_{K_i}$. Each $S_{ij}S_{ij}^*$ is the projection onto $V_{ij}$: the other terms annihilate this range. Further, $S V_{ij}\subseteq V_{ji}$ by the vanishing block products, and the reverse containment after applying $S$ follows by interchanging $i,j$ and using $S^2=I$. For any unit vector $v$ in a nonzero $V_{ij}$, the plane spanned by $v,Sv$ reduces the entire pair and has the asserted operations. Such a vector exists because $K\ne0$ and $S$ is an involution. For $m=2$ the three-distinct-indices step is vacuous.

For $m=4$ take the four coordinate projectors on $\mathbb C^4$ and set
$$
S=\begin{pmatrix}0&U\\ U^*&0\end{pmatrix},\qquad
U=\frac15\begin{pmatrix}3&4\\ -4&3\end{pmatrix}.
$$
This is a Hermitian involution with zero diagonal, hence satisfies (iv) on the whole space. A projector commuting with every coordinate projector is diagonal; commuting with $S$ forces its diagonal entries to agree across each nonzero entry of $S$. The complete bipartite support is connected, so the only reducing projections are $0,I$. Adding zero labels gives the same conclusion for all $m>4$ (the noise still depends on the new $m$).
