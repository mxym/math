# Averaging the coefficients moves the peak

Let $k_n$ maximize $\mathbb E\,i_k(T_n)$, with ties chosen arbitrarily. We show that for all sufficiently large $n$, with probability at least $1-e^{-c n}$,
$$
k_n-\max\mathcal M(T_n)>0.0004n .
$$
The first index is determined by the expected coefficients (the *annealed* peak); the second is measured on the tree actually sampled. The size after which this statement applies is not estimated.

The classical Bedrosian matrix-tree identity (Heilman, Lemma A.1) gives
$$
\mathbb E\, i_k(T_n)=\binom nk(1-k/n)^{k-1},\qquad 1\le k<n .
$$
Indeed, for a prescribed $k$-set delete its internal edges from $K_n$. On the subspace supported there with coordinate sum zero, the Laplacian has eigenvalue $n-k$ with multiplicity $k-1$. On the orthogonal complement perpendicular to the all-ones vector the eigenvalue is $n$ with multiplicity $n-k$. Apply the matrix-tree theorem, divide by $n^{n-2}$, and sum over the choices of the set.

Set $H(x)=-x\log x-(1-x)\log(1-x)$ and $g(x)=H(x)+x\log(1-x)$. Uniformly in $1\le k<n$, writing $x=k/n$ gives $n^{-1}\log\mathbb E\, i_k=g(x)+O((\log n)/n)$ by the usual binomial entropy bounds and $1-x\ge1/n$. At $k=n$ the coefficient vanishes for $n\ge2$; at $k=0$ it is 1. We have $g(0)=0$ by continuity, $g(x)\to-\infty$ at 1, and
$$
g'(x)=\log\frac{(1-x)^2}{x}-\frac{x}{1-x},
\qquad
g''(x)=-\frac2{1-x}-\frac1x-\frac1{(1-x)^2}<0 .
$$
The derivative takes both signs. Hence $g$ has a unique interior maximizer $x_*$ and $k_n/n\to x_*$ for any choice of maximizing indices. The annealed location itself is an elementary consequence of the known expectation.

To verify $x_*>0.3074$ without floating point, take $x=3074/10000$, $y=(1-x)^2/x$ and $w=(y-1)/(y+1)\in(0,1)$. The first three positive terms of $\log y=2\sum_{j\ge0}w^{2j+1}/(2j+1)$ exceed $x/(1-x)$ by the strictly positive rational in the [output](ANNEALED-CHECKS.txt). Thus $g'(x)>0$. In contrast, the [Kesten-root enclosure](PROOF.md) with grid $K=600$, depth 13, Poisson cutoff 10 and $M=10^{12}$ gives
$$
0.305300\le\mu\le0.306955 .
$$
Both inequalities are certified by [annealed.py](annealed.py). Therefore $x_*-\mu>0.000445$. For large $n$, choose $|k_n/n-x_*|<0.00002$, and apply the exponential mode bound with $\varepsilon=0.00002$. This yields the stated gap.
