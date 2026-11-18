# Spectral ordering on the local-unitary graph-state hull

## Statement

Let $d\ge2$ and $n\ge1$. At site $i$ use the channel
$$
 D_{p_i}(X)=(1-p_i)X+\frac{p_i}{d}\operatorname{Tr}(X) I,
 \qquad 0\le p_i\le \frac{d^2}{d^2-1}.
$$
Write $D=\bigotimes_i D_{p_i}$. For an equal-sum pair of vectors, $x\prec y$ means that the sum of the $k$ largest entries of $x$ is at most the corresponding sum for $y$, for every $k$. For a density operator $M$, write $\lambda(M)$ for its eigenvalue vector.

**Graph-state theorem.** Let $\Gamma$ be any symmetric, zero-diagonal matrix over $\mathbb Z_d$. Set $F(x)=\sum_{i<j}\Gamma_{ij}x_ix_j$ and $\omega=e^{2\pi i/d}$. Form the unit vector
$$
 |G_\Gamma\rangle=d^{-n/2}\sum_{x\in\mathbb Z_d^n}\omega^{F(x)}|x\rangle.
$$
If $\rho$ belongs to the convex hull of all these states' projectors and their conjugates by products of single-site unitaries, then
$$
 \lambda(D(\rho))\prec \lambda(D(|0^n\rangle\langle0^n|)).
$$
On the right is the tensor product of the local lists $(1-p_i+p_i/d,p_i/d,\dots,p_i/d)$, to be sorted when taking sums. No assumption that the distinguished entry is *largest* is required.

### A compression lemma

Let $V$ take values in a finite product of finite abelian groups. Conditional on the value $u$ of a finite random variable $U$, suppose the coordinates of $V$ are independent. At each site fix one order of the letters in which **every positive-probability conditional law** of that coordinate is nonincreasing. For any function $t$ from latent labels to the product group,
$$
 \mathcal L(V+t(U))\prec\mathcal L(V).
$$

Indeed, for any set $A$ of size $k$, let $C_i A$ replace each fiber in coordinate $i$ by the initial segment of the same size in the fixed order. Fix $U=u$, write $s=t(u)$ and condition also on $V_{-i}$. The acceptable values of $V_i$ in the event $V+s\in A$ form a translation of the fiber over $V_{-i}+s_{-i}$. By conditional independence and the order assumption this fiber cannot carry more probability than the initial segment of that size for the unshifted $V_i$. Consequently
$$
 \Pr(V+s\in A\mid u)\le\Pr(V+s^{(i\to0)}\in C_i A\mid u),
$$
where $s^{(i\to0)}$ clears the $i$th shift. Apply the inequality successively for $i=1,\ldots,n$. The final set $C_n\cdots C_1 A$ is independent of $u$ and retains size $k$, so averaging gives $\Pr(V+t(U)\in A)\le\Pr(V\in C_n\cdots C_1 A)$. Maximizing over $A$ proves the lemma.

### Graph-label proof

Use $X^u|x\rangle=|x+u\rangle$ and $Z^v|x\rangle=\omega^{v\cdot x}|x\rangle$. By character orthogonality the states $Z^z|G_\Gamma\rangle$ form an orthonormal basis. After $X^u Z^v$, the phase on $|x\rangle$ is $F(x-u)+v\cdot(x-u)$, whose dependence on $x$ is exactly $F(x)+(v-\Gamma u)\cdot x$. Thus the Weyl error sends the state to the basis label $v-\Gamma u$, up to a scalar phase. Using $F$ rather than a half quadratic form avoids division by two, including at composite $d$.

The uniform twirl over $d^2$ Weyl symbols equals $X\mapsto\operatorname{Tr}(X)I/d$: averaging phases kills off-diagonal entries and averaging shifts replaces each diagonal entry by the common mean. At site $i$, $D_{p_i}$ is therefore the random Weyl channel with weight $1-p_i+p_i/d^2$ on $(0,0)$ and $p_i/d^2$ on every other symbol. All weights are nonnegative on exactly the stated physical range. Choose the pairs $(U_i,V_i)$ independently across sites. The output on the graph projector has spectrum $\mathcal L(V-\Gamma U)$.

Given $U=u$, the $V_i$ are independent. If $u_i\ne0$ the conditional law is uniform; otherwise the weight at zero is proportional to $1-p_i+p_i/d^2$ and each other weight to $p_i/d^2$. Choose zero first for $p_i\le1$ and last for $p_i>1$, breaking all remaining ties arbitrarily at that site. The same order works for every relevant $u$, including at the extreme physical parameters. Now $V$ itself has the product distribution specified on the right hand side. Apply the compression lemma with $t(u)=-\Gamma u$.

Local-unitary covariance of $D$ preserves this comparison throughout each orbit. The sum of the largest $k$ eigenvalues is convex (it is the maximum of $\operatorname{Tr}(PM)$ over rank-$k$ orthogonal projectors $P$); hence one and the same reference majorizes any convex mixture. The empty graph gives a product pure state, so the hull contains all separable inputs. At prime $d$ the stabilizer graph normal form includes all pure stabilizer inputs. This last inclusion is **not** asserted for every stabilizer convention at composite dimension.

## Correlated erased-site sets

Draw a subset $E\subseteq[n]$ with any law, then erase precisely those sites by independently replacing each with $I/d$. This gives the mixture of $\rho_{E^c}\otimes (I/d)^{\otimes E}$, with tensor factors placed at their original positions. The graph-state theorem's spectral comparison also holds for this different channel.

Indeed, condition on $E$ and on $U$. The $V_i$ are independent: uniform on $E$ and zero off $E$. The fixed order with zero first works at all sites. Apply the same lemma; $\mathcal L(V)$ is the spectrum obtained by erasing the same masks on $|0^n\rangle$. For fixed $E$ the shifted law also factors as uniform on $E$ times a possibly correlated law on $E^c$: the first factor is unaffected by any shift, including after averaging in $U$. In the common graph-label basis this also follows directly from [Alhejji–Knill, Prop. IV.5](https://arxiv.org/html/2307.06894v3). Local-unitary covariance and convexity handle the same hull. This identifies a subclass of [Song–Chen's compatible-marginal conjecture, Eq. (14)](https://arxiv.org/html/2603.25410v1) with $Q=I/d$; it is not the general conjecture.
