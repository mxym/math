# Randić energy: a minimum-degree bound and a necessary leaf count

Let $R=D^{-1/2}AD^{-1/2}$ be the normalized adjacency matrix of a finite simple graph and $E=\operatorname{tr}|R|$ its Randić energy. If every degree is at least $d\ge2$, then

$$
\frac En\le \frac{1+(d-1)\sqrt{d-1}}{d^2-d+1}.
$$

For connected graphs of order $n\ge3$ with $\ell$ leaves we also obtain $E\le 2n/3+2\ell/9$. Together with the known sun spectra these bounds rule out leafless maximizers for $n\ge4$ and give a linear necessary leaf count. They **do not determine the maximizing connected graph** in the [Gutman–Furtula–Bozkurt conjecture](https://doi.org/10.1016/j.laa.2013.06.010).

## 1. The minimum-degree estimate

Put $a=\sqrt{d-1}/d$, $c=1+2a+3a^2$, $H=2a(1+a)^2$ and $p(x)=[a^2(1+2a)+cx^2-x^4]/H$. On $[0,1]$ we have

$$
H(p(x)-x)=(x-a)^2(1-x)(x+1+2a)\ge0.
$$

The eigenvalues of $R$ lie in $[-1,1]$ by similarity to the random-walk matrix. Write $b_i=(R^2)_{ii}=\sum_jR_{ij}^2$. Nonnegativity gives the fourth-moment inequality

$$
\operatorname{tr}R^4=\sum_{ij}((R^2)_{ij})^2
\ge \sum_i b_i^2+\sum_{i\ne j}\sum_k R_{ik}^2 R_{kj}^2
=2\sum_i b_i^2-\sum_{ij} R_{ij}^4.
$$

Here $b_i$ is the mean reciprocal degree of the neighbors of $i$, so $b_i\le1/d$. Every entry has $R_{ij}^2\le d^{-2}$. It follows that

$$
 c\operatorname{tr}R^2-\operatorname{tr}R^4
 \le \sum_i \big((c+d^{-2})b_i-2b_i^2\big)
 \le n\left(\frac cd-\frac{2d-1}{d^3}\right).
$$

For the second inequality, the summand is strictly increasing on $[0,1/d]$: $c+d^{-2}>4/d$ for $d\ge4$ since $c>1$; for $d=2$ its left side is $3$, and for $d=3$ it exceeds $1+2\sqrt2/3>4/3$.

To evaluate the resulting bound on $E/n$, consider a random variable $X$ supported on $1,a$ with mass $1/(d^2-d+1)$ at $1$. Substitution gives $\mathbb E X^2=1/d$, $\mathbb E X^4=(2d-1)/d^3$. The displayed trace inequality gives $E/n\le\operatorname{tr}p(|R|)/n\le\mathbb E p(X)=\mathbb EX$ since $p(1)=1$ and $p(a)=a$. This is the bound above.

Equality forces every $b_i=1/d$; hence every neighbor of every vertex has degree $d$, so the graph is $d$-regular. On regular graphs, $R=A/d$. By [van Dam–Haemers–Koolen](https://doi.org/10.1016/j.jctb.2014.02.007), the equality graphs are exactly disjoint unions of triangles and hexagons for $d=2$ and disjoint unions of incidence graphs of projective planes of order $d-1$ for $d\ge3$. The equality classification on regular graphs is theirs. No existence of such a plane for every $d$ is implied.

## 2. The bound with leaves

Suppose $G$ is connected and $n\ge3$. The majorant polynomial for $a=1/2$ remains valid when there are leaves. It gives $9E\le2n+11\operatorname{tr}R^2-4\operatorname{tr}R^4$. The fourth-moment inequality, which also does not require a minimum degree, gives

$$
9E\le2n+\sum_i(12b_i-8b_i^2)+4\sum_{ij}(R_{ij}^4-R_{ij}^2/4).
$$

Since $12b-8b^2\le 4+4(b-1/2)$, we bound first the excess of the $b_i$. Every leaf has $b_i\le1/2$: its only neighbor is not a leaf. A nonleaf of degree $r$ with $k$ leaf neighbors has $b_i\le1/2+k/(2r)\le1/2+k/4$. Hence $\sum_i(b_i-1/2)_+\le\ell/4$. A nonleaf-to-nonleaf edge contributes nonpositively to the last sum. On any oriented leaf edge, $R_{ij}^2\le1/2$, so $R_{ij}^4-R_{ij}^2/4\le1/8$. There are $2\ell$ such orientations. The last sum before the factor four is at most $\ell/4$. Combining the terms gives $9E\le6n+2\ell$.

## 3. Comparison with the sun and balanced double sun

For odd $n\ge3$, the sun is a subdivided star and has energy $(n-3)/\sqrt2+2$ by [Allem–Molina–Pastine, §2](https://arxiv.org/html/1811.08776v1). For even $n\ge6$, join the centers of two subdivided stars with $p,q\ge1$ branches, $|p-q|\le1$, $n=2+2(p+q)$. The branch differences on each side yield $n-6$ eigenvalues of absolute value $1/\sqrt2$: on the zero-sum tip and internal branch coordinates, only the matching edges of weight $1/\sqrt2$ act. In orthonormal constant-on-type coordinates the remaining six-dimensional block is a weighted path with successive edge weights

$$
1/\sqrt2,\quad\sqrt{p/[2(p+1)]},\quad1/\sqrt{(p+1)(q+1)},\quad
\sqrt{q/[2(q+1)]},\quad1/\sqrt2 .
$$

Its eigenvalues are $\pm1,\pm r,\pm s$, with $r,s>0$ by the nonsingular path determinant; the unit eigenvalues come from regularity of the random-walk row sums and bipartiteness. Put $u=1/(p+1),v=1/(q+1)$. The determinant (unique perfect matching) gives $rs=\sqrt{uv}/2$, while the trace of the square gives $r^2+s^2=1-(u+v)/2+uv$. Therefore

$$
(r+s)^2=1+uv-(\sqrt u-\sqrt v)^2/2>1:
$$

indeed $(\sqrt{p+1}-\sqrt{q+1})^2<2$ when $p,q$ differ by at most one. It follows that the balanced double sun has energy strictly greater than $(n-6)/\sqrt2+4$. At $n=4$ the path $P_4$ has eigenvalues $\pm1,\pm1/2$ and energy $3$.

A leafless graph has $E\le2n/3$ by §1. The sun and balanced double sun beat this for every $n\ge4$; at $n=3$ the triangle ties the sun. Combining their energies with §2 shows that **any** maximizing connected graph for $n\ge6$ must have at least $(9\sqrt2/4-3)(n-6)$ leaves. For odd $n$ one may replace $n-6$ with $n-3$. This necessary condition is not a sufficient one.

## Prior work and checks

The regular energy constant and its equality classification are due to van Dam–Haemers–Koolen, cited above. [Gu, Huang and Li, Theorem 5.3](https://cfc.nankai.edu.cn/_upload/article/files/a2/6c/13dd3d364f9ebbcd4a9072ff7912/c6c5c64a-f379-4364-9020-329b09e4d5f3.pdf) give the different finite-order bound $1+\sqrt{(n-1)(n/d-1)}$ at minimum degree $d$. The bounds are not uniformly ordered for all $n,d$. Allem–Molina–Pastine, Theorems 4.7–4.8, already compare bipartite graphs without suspended paths and some nonbipartite graphs with nullity to the sun benchmark. The qualitative need for a leaf can also be obtained by second-moment estimates; it is not presented as a new characterization. [Yin (2026)](https://www.mdpi.com/2227-7390/14/18/3338) treats Kragujevac-like trees. The minimum absolute eigenvalue studied by [Guo–Zhang](https://arxiv.org/abs/2509.06247) is not the mean absolute eigenvalue bounded here.

This AI-assisted research draft underwent independent internal AI review, not external peer review. No global priority or formal-verification claim is made. From this directory run, with Python 3.10 or later and no optimization:

    python3 check.py
    python3 independent.py

The computations check finite consequences, not the infinite theorems. Both implementations inspect all 27,474 connected labeled graphs of orders three through six. The independent implementation also checks the general-degree moment comparisons in real quadratic fields and 900 exact quotient-path characteristic polynomials.
