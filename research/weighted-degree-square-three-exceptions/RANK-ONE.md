# The BEKSZ degree-square inequality for product weights

Let $w_{ij}=x_i x_j$ for $i\ne j$, with $x_i\ge0$. There is no bound on the order or on the number of distinct degrees. The zero-total case is immediate, so normalize $\sum_i x_i=1$ by homogeneity. Write $Q=\sum_i x_i^2$, $S_j=\sum_i x_i^j$, and $g=\min_{s_i=\pm1}|\sum_i s_i x_i|$. Then $W=(1-Q)/2$, $d_i=x_i(1-x_i)$ and $C=(1-g^2)/4$. Substituting into $8WC\ge4W^2+\sum_i d_i^2$ gives the equivalent inequality
$$ (1-Q)g^2\le 2S_3-S_4-Q^2. $$

First, $g^2\le S_3$. Order the positive $x_i$ decreasingly and greedily choose each sign opposite the current residual, so its absolute value evolves as $r_0=0$, $r_i=|r_{i-1}-x_i|$. Let $k$ be the **last** index with $r_{k-1}\le x_k$ (index 1 qualifies). All later steps simply subtract. Writing $t=\sum_{j>k}x_j$ gives $0\le r_n=r_k-t\le x_k-t$, so $t\le x_k$. Since $t\le x_k\le1$,
$$ (x_k-t)^2\le x_k^2(1-t)\le\sum_{i\le k}x_i^3. $$
The first inequality is $t(2x_k-x_k^2-t)\ge0$; the second uses $x_i\ge x_k$ on a prefix of total mass $1-t$.

Second, let $X$ take value $x_i$ with probability $x_i$, and take an independent copy $Y$. Then $\mathbb E X=Q$, $\mathbb E X^2=S_3$ and $\mathbb E X^3=S_4$. We have
$$ 2\bigl(\operatorname{Var}(X)-\operatorname{Cov}(X,X^2)\bigr)
   =\mathbb E[(X-Y)^2(1-X-Y)]\ge0. $$
When $X=Y$ the integrand vanishes; otherwise the two draws came from distinct indices, so $X+Y\le1$. Rearranging gives $(1-Q)S_3\le2S_3-S_4-Q^2$. Combining the two bounds proves the result.
