# Expected puncturing rank and the optimum

Let $q$ be a prime power, $d\ge2$, $L=(q^d-1)/(q-1)$, and $n=tL$ with $t\ge1$ an integer. Write $P$ for the one-dimensional subspaces of $\mathbb F_q^d$. An $[n,d]$ linear **randomization code** $C$ is the row space of a full-rank $d\times n$ generator matrix $G$. Define $S_t$ by choosing one nonzero representative of each point of $P$ and using it $t$ times as a column of $G$. This spans $\mathbb F_q^d$, so the stated dimension is attained.

The message $M$ is uniform on the cosets of $C$ in $\mathbb F_q^n$. The transmitted $X$, chosen uniformly in the indicated coset, is received noiselessly by Bob. Independently of $(M,X)$, retain each coordinate with probability $1-\varepsilon$ to obtain $R$; Eve observes $(R,X_R)$. Define $E_C(\varepsilon)=H_q(M\mid R,X_R)$ (base-$q$ Shannon entropy).

**Theorem.** For each $0<\varepsilon<1$, $S_t$ maximizes $E_C(\varepsilon)$ over all $[n,d]$ randomization codes, uniquely up to monomial equivalence (permutation and nonzero scalings of coordinates). Its dual $S_t^\perp$ has the same property over all $[n,n-d]$ randomization codes. The optima are simultaneous in $\varepsilon$. At $\varepsilon=0,1$ all codes of the same dimension tie.

### 1. Reduction to expected rank

For a set $R$, let $r_C(R)$ be the rank of the columns indexed by $R$, equivalently $\dim C|_R$. The unconditional $X$ is uniform over the whole ambient space, so $H_q(X_R\mid R)=\mathbb E|R|$. Given the message and a fixed $R$, the observation is uniform on a translate of the punctured space, since all fibers of a linear projection have the same size. Thus $H_q(X_R\mid R,M)=\mathbb E r_C(R)$ and
$$
E_C(\varepsilon)=n-d-n(1-\varepsilon)+\mathbb E r_C(R).
$$
In particular it suffices to compare expected ranks. This reduction is classical; see the [sources](REFERENCES.md).

### 2. Independent inclusion of projective directions

Let $m_e$ count the columns in direction $e\in P$, and $z$ the number of zero columns, so $\sum_e m_e=n-z$. Zero columns cannot increase rank. Direction $e$ survives with probability $1-\varepsilon^{m_e}$, independently over $P$ since the coordinate sets involved are disjoint. Put $\theta=-\ln\varepsilon$. For $x\in[0,\infty)^P$ form $T_x$ by independently including $e$ with probability $1-e^{-x_e}$. Write $r(A)$ for the dimension of the linear span of representatives of $A$. Then
$$
F(x)=\mathbb E r(T_x),\qquad \mathbb E r_C(R)=F(\theta m).
$$

### 3. Concavity, with a strictness estimate

The following is the Poisson rounding/discrete Hessian argument of [Dughmi, Roughgarden and Yan](https://arxiv.org/html/1103.0040v3), Lemma 4.2 (§4.3) and Claims 4.5–4.6, specialized to projective rank. We give details including the strict estimate used here.

Set $D_e f(A)=f(A\cup\{e\})-f(A)$. Increasing $x_e$ by $h\ge0$ is equivalent to independently adjoining $e$ with probability $1-e^{-h}$. Differentiation once and twice gives
$$
\partial_e F(x)=\mathbb E D_e r(T_x),\qquad
\partial_j\partial_e F(x)=\mathbb E D_jD_e r(T_x).
$$
These statements also hold on the boundary by continuity of the finite sum of exponentials; when $j=e$, $D_e^2=-D_e$.

For fixed $A$, quotient $\mathbb F_q^d$ by the span of $A$. Directions with zero image give zero rows and columns of $(-D_jD_e r(A))_{e,j}$. The others split into classes $B$ of parallel nonzero images. Two nonzero images cost one rather than two new dimensions exactly when they are parallel, including when the two indices coincide. Thus for any real $v$,
$$
-\sum_{e,j}v_e v_j D_jD_e r(A)=\sum_B\Big(\sum_{e\in B}v_e\Big)^2\ge0.
$$
At $A=\varnothing$, distinct original directions are nonparallel, so this quadratic form is $\lVert v\rVert_2^2$. Also $D_e r(A)\ge0$, with value $1$ at the empty set. Since $\Pr(T_x=\varnothing)=e^{-\sum_e x_e}>0$, we have at all finite nonnegative $x$
$$
-\nabla^2F(x)\succeq e^{-\sum_e x_e}I,\qquad
\partial_e F(x)\ge e^{-\sum_e x_e}>0 .
$$
Hence $F$ is strictly concave, including along boundary faces, and strictly increases in every coordinate. Concavity is in the *intensities*, not the raw Bernoulli inclusion probabilities.

### 4. Balance, zero columns and equality

The rank-preserving action of $\mathrm{GL}(d,q)$ on $P$ is transitive. Thus for $a=\sum_e x_e$ the group average of $x$ equals $u=(a/L)\mathbf 1$. Invariance gives $F(x)\le F(u)$ by Jensen, strictly unless $x=u$. More quantitatively, at $u$ the gradient is constant across coordinates. Its inner product with $x-u$ is zero, and the curvature bound on the segment from $u$ to $x$ gives
$$
F(u)-F(x)\ge \tfrac12 e^{-a}\lVert x-u\rVert_2^2.
$$
For $x=\theta m$ one has $a=\theta(n-z)$. Raising $u$ to $\theta t\mathbf 1$ strictly increases $F$ if $z>0$. Together these show that the unique maximizing histogram is $z=0$, $m_e=t$ for every $e$. If desired the difference in equivocation from the optimum is at least
$$
\theta z e^{-\theta n}
+\tfrac12\theta^2 e^{-\theta(n-z)}
\big\lVert m-((n-z)/L)\mathbf 1\big\rVert_2^2,
$$
where the first term follows by integrating the gradient while raising the constant vector. Uniform multiplicity is integral at the specified lengths. After permuting and rescaling coordinates, each matrix attaining it has the prescribed repeated representatives. Row-basis changes do not alter the code. Conversely these monomial operations preserve expected rank under i.i.d. coordinate retention.

### 5. The dual and endpoints

For each $R$, the orthogonal complement in $\mathbb F_q^R$ of $C^\perp|_R$ is the restriction of the words of $C$ supported on $R$: extend a vector by zero outside $R$ and apply $(C^\perp)^\perp=C$. Its dimension is $d-r_C(R^c)$, the kernel dimension of puncturing to $R^c$. Therefore
$$
r_{C^\perp}(R)=|R|-d+r_C(R^c),\qquad
E_{C^\perp}(\varepsilon)=\mathbb E r_C(R^c).
$$
Membership in $R^c$ has probability $\varepsilon$, independently across coordinates. The primal comparison at erasure rate $1-\varepsilon$ thus proves the dual comparison at $\varepsilon$. Every $[n,n-d]$ code is a dual, and monomial equivalence is preserved in both directions since the inverse transpose of a monomial matrix is monomial. The dual here is the **dual of the repeated simplex**, not the repeated Hamming code. At $t=1$ it is the usual Hamming code. With no erasures $M$ is known; with all symbols erased its entropy is unchanged, so uniqueness is restricted to the open interval.
