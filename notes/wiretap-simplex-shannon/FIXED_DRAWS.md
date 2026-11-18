# A second proof: condition on the number of draws with replacement

The argument here replaces Sections 2–4 of the [main proof](PROOF.md). It uses the fixed-draw concavity mechanism of [Shaddin Dughmi, EC 2011, Lemma 3.2 and §3.3](https://arxiv.org/html/1103.0041v2). Dughmi formulates the bounded lottery with a feasible allocation vector. The computation below states the special rank inequality on the full probability simplex directly; one need not assume that a vector of scaled projective multiplicities lies in the allocation polytope of that paper.

Fix $0<\varepsilon<1$, $\theta=-\ln\varepsilon$. Attach independent Poisson counts of mean $\theta$ to the $n$ coordinates and retain exactly those with nonzero counts. This is the required independent-erasure law. Given a total of $K=k$ arrivals, the index sequence is equivalent to $k$ independent uniform choices of physical coordinates **with replacement** by the Poisson splitting identity. Replacing a zero column by any nonzero vector weakly increases every sampled rank and strictly increases it when exactly one arrival occurs at that coordinate and none elsewhere, an event of positive probability. It preserves full generator rank. It therefore suffices to treat codes with no zero columns.

Let $p_e=m_e/n$ be the probability of drawing projective direction $e$. Let $H_k(p)$ be the expected rank of the span of $k$ independent draws from $p$. The claim is that each $H_k$ is concave on the probability simplex. The cases $H_0=0$ and $H_1=1$ are immediate. For $k\ge2$ take a vector $v$ with $\sum_e v_e=0$. The expectation defining $H_k$ is multilinear in the $k$ individual draw laws. Putting each law equal to $p$ and differentiating in direction $v$ gives
$$
D^2 H_k(p)[v,v]
=k(k-1)\,\mathbb E\!\sum_{i,j\in P}v_i v_j r(A\cup\{i,j\}),
$$
where $A$ is the support of $k-2$ independent draws. In the quotient by $\operatorname{span}(A)$, let $b_i$ be 1 if the image of $i$ is nonzero and 0 otherwise. Partition the nonzero images into parallel classes $B$. For any indices, including coinciding ones,
$$
r(A\cup\{i,j\})=r(A)+b_i+b_j-\sum_B\mathbf 1_{i\in B}\mathbf 1_{j\in B}.
$$
The constant and linear terms vanish in the double sum because $\sum_i v_i=0$. The second variation is thus $-k(k-1)\,\mathbb E\sum_B(\sum_{i\in B}v_i)^2\le0$. The polynomial identity remains valid at boundary points. By transitivity of $\mathrm{GL}(d,q)$, averaging the permuted draw laws shows that $H_k(p)\le H_k(\mathbf1/L)$ for *each* $k$.

For $k=2$, distinct directions always have rank two, so $H_2(p)=2-\sum_e p_e^2$. Its gap from the uniform value is exactly $\sum_e(p_e-1/L)^2$. Since $K$ is Poisson of mean $n\theta$, $\Pr(K=2)=e^{-n\theta}(n\theta)^2/2>0$. Averaging the inequalities for all $k$ proves optimality for the original channel with strict inequality for nonuniform $p$. Together with the zero-column argument, this gives precisely the equality criterion of the main theorem; its dual statement follows by the same puncturing identity.

**What was conditioned on?** $K$ is a Poisson arrival count and may exceed $n$. For $K=2$, for example, the two arrivals may hit the same coordinate. Conditioning on exactly two *distinct physical coordinates being revealed* is a different experiment (sampling without replacement). The comparison here does not imply the general coefficientwise criterion in HWSS Eq. (15).
