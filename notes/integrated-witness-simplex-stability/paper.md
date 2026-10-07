# Integrated determinant witnesses and explicit simplex stability

mxym. 7 October 2026.

**Outcome.** For every fixed $d\ge3$, every convex body $K\subset\mathbb R^d$, and every maximum-volume inscribed simplex $S$, we prove $$E(K,S)\le G_d^*\left(a(K)-\frac1{d+1}\right)^{1/d}$$ with entirely explicit constants. This removes the quadratic concentration loss of the released modulus; in dimension three the power is $1/3$ instead of $1/51$. The proof uses integrated determinant witnesses, a conditioned random anchor simplex, and the released elementary geometric conversion. It uses no inverse stability theorem for the Minkowski problem. No novelty, priority, best-known-rate, or optimal-exponent claim is made. An independent analytic model audit of this replacement passed. Finite exact checks support the audit; no human peer review or proof-assistant formalization is claimed.

# Definitions and constants

For a full-dimensional compact convex body $Q\subset\mathbb R^n$, let $\Pi Q$ be its projection body, normalized by $h_{\Pi Q}(u)=|Q\mid u^\perp|_{n-1}$ for unit $u$, and let $R(Q)=|\Pi Q|/|Q|^{n-1}$. Entry005 defines the affine invariant $$a(K)=\left(\frac d{d+1}\right)^d\frac{R(\mathcal P K)}{R(K)}-1,
 \qquad e=a(K)-\frac1{d+1}\ge0,$$ where $\mathcal P K$ is a pyramid over $K$. For an inscribed simplex $S$ with centroid $z$, the prescribed-center excess is $$E(K,S)=\inf\{t\ge0:K\subset z+(1+t)(S-z)\}.$$ Fix an arbitrary maximum simplex $S$, and normalize it affinely to a regular simplex $\Delta$ of centroid zero and inradius one. Its vertex norms are $d$. The vertex-replacement determinant identity gives $|\alpha_i(x)|\le1$ for $x\in K$, and therefore $$B_2^d\subset\Delta\subset K\subset R_0B_2^d,\qquad R_0=d(d+1).
 \tag{1}$$ The resulting cone law $\nu$ is the pushforward of $h_K(u)dS_K(u)/(d|K|)$ by $u\mapsto u/h_K(u)$. It is centered, supported on $\partial K^\circ\subset B_2^d$, and satisfies $$\begin{aligned}
 A&=\mathbb E|\det(X_1,\ldots,X_d)|\le1,\\
 B&=\mathbb E|\det((X_1,1),\ldots,(X_{d+1},1))|,\\
 D&=B-A=(d+1)Ae\le(d+1)e.
\end{aligned}$$ These are the version-3 cone-law identities. With $$b=\frac1{4(dR_0)^d},
 \tag{2}$$ Cauchy's formula and the cube contained in the unit projected ball give $$\mathbb E(-u\cdot X)_+\ge2b\qquad (u\in S^{d-1}).
 \tag{3}$$ In detail the left side is $|K\mid u^\perp|/(d|K|)$, which is at least $(2/d)^{d-1}/[d(2R_0)^d]=2b$.

For this note define the explicit constants $$Q=(d+1)(d+2)8^d b^{-4d},\qquad M=b^{-1},
 \qquad C=4d^2R_0(M+1),
 \tag{4}$$ $$e_*=\frac1{(d+1)MQ(8MdC)^d},\qquad
 A_d^*=4MdC\,[MQ(d+1)]^{1/d},
 \tag{5}$$ $$G_d^*=\max\{A_d^*,(R_0-1)e_*^{-1/d}\}.
 \tag{6}$$ All these constants are explicit. In particular $b,Q,M,C,e_*$ are rational. They remain very poor numerically. No dimension-independent conclusion is claimed.

# Integrated sign witnesses

We prove the new probabilistic step for any centered probability law on $B_2^d$ satisfying (3); it need not be a cone law or have atoms. For an ordered base tuple $\mathbf x=(x_1,\ldots,x_d)$ put $$F_{\mathbf x}(y)=\det((x_1,1),\ldots,(x_d,1),(y,1)),$$ and let $P(\mathbf x)=\mathbb E(F_{\mathbf x}(X))_+$ and $N(\mathbf x)=\mathbb E(-F_{\mathbf x}(X))_+$. Centering gives the cancellation identity $$D=2\mathbb E_{\mathbf X}\min\{P(\mathbf X),N(\mathbf X)\}.
 \tag{7}$$ Indeed $\mathbb EF_{\mathbf x}(X)=\det(x_1,\ldots,x_d)$ up to an irrelevant orientation sign. Subtracting its absolute value from $\mathbb E|F_{\mathbf x}(X)|$ and then integrating proves (7), including singular base tuples.

Define a continuous, nonnegative two-sample witness $$\psi_{\mathbf x}(y,z)=
 \min\{(F_{\mathbf x}(y))_+,(-F_{\mathbf x}(z))_+\}
 +\min\{(-F_{\mathbf x}(y))_+,(F_{\mathbf x}(z))_+\}.
 \tag{8}$$ For independent $Y,Z$ of law $\nu$, each minimum has expectation at most $\min(P,N)$, since it is bounded by each of its two arguments. Therefore $$\mathbb E_{\mathbf X,Y,Z}\psi_{\mathbf X}(Y,Z)\le D.
 \tag{9}$$ This integrates witnesses over their actual sampled points. It never assigns positive individual mass to a selected support point.

**Lemma 1** (Linear assignment error). *There are $d+1$ affinely independent points $w_i\in\operatorname{supp}\nu$ and a measurable assignment $X\mapsto w_{I(X)}$ such that $$h:=\mathbb E\|X-w_{I(X)}\|\le QD.
 \tag{10}$$ If $QD\le b$, their simplex $T$ satisfies $bB_2^d\subset T\subset B_2^d$.*

*Proof.* Let $W=(W_0,\ldots,W_d)$ be independent samples, and put $$V(W)=|\det((W_0,1),\ldots,(W_d,1))|.$$ For the covariance matrix $\Sigma=\mathbb EXX^{\mathsf T}$, (3) and centering give $\mathbb E|u\cdot X|\ge4b$ and hence $u^{\mathsf T}\Sigma u\ge16b^2$. Expanding the two determinants and using independence yields the exact moment identity $$\mathbb EV^2=(d+1)!\det\Sigma\ge(d+1)!16^d b^{2d}\ge2b^{2d}.
 \tag{11}$$ For clarity the lifted moment matrix is $\operatorname{diag}(\Sigma,1)$, and the usual determinant expansion gives $(d+1)!$ times its determinant. Also $V\le2^d$, by subtracting one lifted point from the others and applying Hadamard's inequality to the $d$ difference columns. Thus the event $$\mathcal E=\{V\ge v_0\},\qquad v_0=b^d,$$ has probability at least $$q_0=\frac{b^{2d}}{4^d},
 \tag{12}$$ because $\mathbb EV^2\le b^{2d}+4^d\mathbb P(\mathcal E)$.

For each $i$, use the $d$ anchors except $w_i$ as base, and test $w_i$ and $x$ in (8). For each $i<j$, use $x$ and the $d-1$ anchors except $w_i,w_j$ as base, and test $w_i,w_j$. Let $H(W)$ be the integral in $x$ of the sum of all these $m=(d+1)(d+2)/2$ witnesses. Every summand has unconditional expectation at most $D$ by (9): the base and the two tested samples are independent with law $\nu$. Hence $\mathbb EH(W)\le mD$.

Restricting to $\mathcal E$ and averaging, choose anchors in $\mathcal E\cap(\operatorname{supp}\nu)^{d+1}$ with $$H(W)\le\frac{mD}{q_0}.
 \tag{13}$$ The inequality can be attained: $H$ is continuous by dominated convergence, and the indicated event in the compact support product is compact and has positive probability. Its minimum does not exceed its conditional average. This selection argument is valid for nonatomic laws.

Let $\alpha_i(x)$ be the barycentric coordinates relative to these anchors. The first kind of witness is exactly $V\min\{1,(-\alpha_i(x))_+\}$. The second is at least $V\min\{(\alpha_i(x))_+,(\alpha_j(x))_+\}$: its two determinants have opposite signs whenever both coefficients are positive, and magnitudes $V\alpha_j(x)$ and $V\alpha_i(x)$. Contributions from two negative coefficients can be discarded. Consequently $$\Phi:=\mathbb E\left[\sum_i\min\{1,(-\alpha_i(X))_+\}
   +\sum_{i<j}\min\{(\alpha_i(X))_+,(\alpha_j(X))_+\}\right]
 \le\frac{mD}{q_0v_0}.
 \tag{14}$$ Every replacement determinant is at most $2^d$, so $$|\alpha_i(x)|\le L_0:=2^d/v_0\ge1 \qquad (x\in B_2^d).$$ Assign $x$ to the index $r$ of its largest positive coefficient, resolving ties by the smallest index. Such a coefficient exists because their sum is one. Put $N_x=\sum_i(-\alpha_i(x))_+$ and $U_x=\sum_{i\ne r}(\alpha_i(x))_+$. Then $$N_x\le L_0\sum_i\min\{1,(-\alpha_i(x))_+\},\qquad
 U_x\le\sum_{i<j}\min\{(\alpha_i(x))_+,(\alpha_j(x))_+\}.$$ The second bound uses just the pairs containing $r$. Since the anchor diameter is at most two, $$\|x-w_r\|\le2\sum_{i\ne r}|\alpha_i(x)|=2(N_x+U_x).$$ Integrating and using (14) gives $$h\le2L_0\Phi\le\frac{2L_0m}{q_0v_0}D
 =(d+1)(d+2)8^d b^{-4d}D=QD.$$

Finally, for every unit $u$, the one-Lipschitz function $x\mapsto(u\cdot x)_+$ has expectation at least $2b$ by centering and (3). The assigned law has expectation at least $2b-h\ge b$. Some anchor therefore has $u\cdot w_i\ge b$. This holds in every direction, so $bB_2^d\subset T$. The other inclusion is automatic from the support condition. QED.

# Explicit geometric conversion

Now return to the cone law of the normalized body. If $e\le e_*$, then $QD\le Q(d+1)e\le b$. Let $P=T^\circ$. Each selected $w_i$ lies on $\partial K^\circ$, so $$K\subset P\subset MB_2^d.
 \tag{15}$$ The support function $h_P$ is $M$-Lipschitz, $h_P(w_i)=1$, and $h_K(x)=1$ on $\operatorname{supp}\nu$. Equation (10) gives $$0\le\int(h_P(x)-1)\,d\nu(x)\le Mh\le MQD=:z_0.
 \tag{16}$$ The left integral is $V(K[d-1],P)/|K|-1$. Minkowski's first inequality therefore gives $(|P|/|K|)^{1/d}\le1+z_0$. Here $z_0\le1$, so $$|P|-|K|\le(2R_0)^d d2^{d-1}z_0.
 \tag{17}$$

We recall the elementary cap argument to specify constants. Put $s=d_H(K,P)$. If $s>0$, choose a farthest $q\in P$ and the unit direction $u$ from its metric projection onto $K$, with $u\cdot q-h_K(u)=s$. We have $s\le M$. With $t=s/[2(M+1)]$, the ball $(1-t)q+tB_2^d$ lies in $P$ and its lowest $u$-coordinate exceeds $h_K(u)$ by at least $s/2$. It is disjoint from $K$. Its inscribed cube of side $2t/d$ gives $$|P|-|K|\ge[s/(d(M+1))]^d.$$ Combining with (17), including $s=0$, proves $$s\le C z_0^{1/d}\le C[MQ(d+1)e]^{1/d}.
 \tag{18}$$ Our gate $e_*$ makes $s\le1/(8Md)$.

It remains to keep the initially chosen maximum simplex. Since $h_P\ge1$ and $h_K\ge h_P-s$, we have $(1-s)P\subset K$. Maximality of $\Delta$ gives $|\Delta|/|P|\ge(1-s)^d\ge1-ds$. The nonnegative column-stochastic matrix of its vertex barycentric coordinates in $P$ has determinant magnitude at least $1-\delta$, where $\delta=ds\le1/8$. Hadamard's inequality forces every column to have an entry at least $1-2\delta$. The dominant rows are distinct: if two coincided, the permanent, interpreted as the probability of distinct independent row selections, would be at most $1-(1-2\delta)^2\le4\delta<1-\delta$, contradicting its domination of the determinant.

Match the vertices accordingly. Their distances are at most $2\delta\operatorname{diam}P\le4Md s$. Taking convex combinations and using $B_2^d\subset\Delta$ gives $$K\subset P\subset\Delta+4Md sB_2^d\subset(1+4Md s)\Delta.$$ Together with (18) this proves $E(K,\Delta)\le A_d^*e^{1/d}$ for $0\le e\le e_*$. This includes $e=0$: the assignment error and $z_0$ vanish, so $s=0$ and the same prescribed simplex has zero excess. For $e>e_*$, (1) gives $E(K,\Delta)\le R_0-1$, yielding (6). Undoing the affine map restores the centroid of the arbitrary initial $S$. We have proved:

**Theorem 2** (Explicit unconditional replacement). *For every fixed $d\ge3$, every convex body $K\subset\mathbb R^d$, and every maximum-volume inscribed simplex $S$, equations (2), (4)--(6) give $$E(K,S)\le G_d^*\left(a(K)-\frac1{d+1}\right)^{1/d}.$$ At the local threshold, $A_d^*e_*^{1/d}=1/2$.*

# Dependencies and the remaining geometric question

The new step is Lemma 1. It replaces shrinking-cell concentration by an integrated selection over conditioned random anchors. The cancellation identity, normalization, mixed-volume argument, cap estimate, and stochastic matrix conversion are standard or are already proved in the released supplement. No inverse-Minkowski result is used. The proof depends only on the direct arguments displayed here and the pinned cone-law definitions. No quantitative inverse-Minkowski theorem is imported.

The separate exact truncation calculation gives the ceiling $1/(d-1)$ for both the prescribed-maximum quantity and affine Banach--Mazur excess. It is not reproduced here. The remaining exponent loss is now solely the cap conversion from volume to distance: $1/d$ versus that ceiling. A valid comparison-simplex-specific inverse estimate might close it, but no such estimate is assumed or established by this note.

The exact checker supplements the proof by verifying affine determinant moments, cancellation and witness expectations, barycentric witness identities, and selection bounds for finite rational laws. Finite tests do not prove the general statement or cover nonatomic laws; those are handled analytically above. No novelty or best-known assertion is made.

## References

1. mxym, Random-determinant rigidity, sharp symmetric cone bounds, and spectral nonattainment, entry005 v3, commit 31e3d8a37e4a3051a7f5a2535be1c75642e15bcc. [Pinned source](https://github.com/mxym/math/blob/31e3d8a37e4a3051a7f5a2535be1c75642e15bcc/preprints/005-simplex-product-optimum/v3/paper.md).
2. mxym, Effective simplex rigidity for the projection cone invariant, Sections 2 and 4-6, commit 6785c1c830f8e19e2eb07b0bb89f4d475a8b154a. [Pinned source](https://github.com/mxym/math/blob/6785c1c830f8e19e2eb07b0bb89f4d475a8b154a/notes/quantitative-projection-simplex-stability/paper.md).
3. R. Schneider, Convex Bodies The Brunn Minkowski Theory, second expanded edition, Cambridge University Press, 2014. Classical cone-volume, Cauchy, support-function and mixed-volume identities.
