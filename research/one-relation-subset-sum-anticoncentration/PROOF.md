# Proof

Let $p_j(i)=2^{-j}\binom ji$ be the mass of a fair binomial count, $c_j=\max_i p_j(i)$, and $R_j(d)$ its largest mass in any residue class modulo $d$. We use the following estimates from [the two-magnitude proof](../two-weight-subset-sum-anticoncentration/PROOF.md), for $j\ge1$:
$$
(j+1)c_j^2\le3/4,\qquad (j+1/2)c_j^2\le2/\pi<2/3,\qquad (j+2)c_j^2\le1.
$$
For $j\ge d\ge2$, $R_j(d)\le c_d$. For $j\ge2d$, $R_j(d)\le R_{2d}(d)=c_{2d}+2/4^d$ and $dR_j(d)^2\le1/2$. For $d\ge3$ we will need the stronger bound $dR_j(d)^2\le3/8$: at $d=3$ use $3(22/64)^2<3/8$. At $d\ge4$ the sharp binomial estimate gives $\sqrt d\,c_{2d}<1/\sqrt\pi<4/7$, whereas the decreasing sequence $2\sqrt d/4^d$ is at most $1/64$. The square of their sum is less than $3/8$.

## Two-coordinate line estimate

Let $X,Y$ be independent fair binomial counts of $n,m\ge1$ trials, respectively. Partition the integral count rectangle by cosets of $\mathbb Z(d,e)$ for integers $d,e$ with $de\ne0$. Write $K_2$ for the number of cosets meeting the rectangle, $\rho_2$ for the largest coset mass. We claim
$$
K_2\rho_2^2\le 8/9.
$$
These cosets consist of **integer multiples of the actual step**; they need not contain every integer point on the corresponding real line.

Reflecting a count in its midpoint or interchanging axes preserves the desired bound. Denote the step magnitudes by $b=|d|,\ a=|e|$, with $1\le a\le b$ after interchanging axes if necessary. If $n<b$ or $m<a$, each coset has at most one point of the box and the product bound is $(n+1)c_n^2(m+1)c_m^2\le9/16$. Otherwise, the points in any coset in the box form a consecutive interval of steps. Count its first point, the unique point without a predecessor in the box. This gives
$$
K_2=P+Q-ab,\qquad P=a(n+1),\quad Q=b(m+1).
$$
The two coordinates within a fixed coset have prescribed residues modulo $b,a$, respectively, and each coordinate value occurs at most once. Summing the binomial masses over each residue in turn gives
$$
\rho_2\le c_nR_m(a),\qquad \rho_2\le c_mR_n(b).
$$
For $a=1$ the residue constraint is vacuous, so $R_m(1)=1$. No coprimality was used.

1. **$a\ge2$.** Both $P\rho_2^2$ and $Q\rho_2^2$ are less than $1/2$: for example $P\rho_2^2\le (n+1)c_n^2\,a c_a^2<(3/4)(2/3)$. If $n\ge2b$, $Q\rho_2^2\le(3/4)(1/2)=3/8$; if $m\ge2a$, the same improvement holds for $P\rho_2^2$. Either gives $K_2\rho_2^2\le7/8$. In the remaining range $P,Q\le2ab$, whence $P+Q-ab\le(3/2)\max(P,Q)$ and the result is less than $3/4$.
2. **$a=b=1$.** Up to reflection the fibers are indexed by the sum of the counts; this is $\mathrm{Bin}(n+m,1/2)$. Its support and peak give $K_2\rho_2^2\le3/4$.
3. **$a=1<b$, except for the long step-2 range.** Here $K_2=n+bm+1$. For $b\le n<2b$, $K_2\le b(m+2)$ and $K_2\rho_2^2\le (m+2)c_m^2\,b c_b^2<2/3$. For $n\ge2b$ and $b\ge3$, split $K_2=(n+1/2)+(bm+1/2)$. The first term times $\rho_2^2$ is at most $2/\pi$, and the second is at most $(m+1/2)c_m^2\, bR_n(b)^2\le(2/\pi)(3/8)$. Their sum is $11/(4\pi)<8/9$.
4. **$a=1,\ b=2,\ n\ge4$.** Put $U=n+1/2,\ V=2m+1/2$. The preceding fiber bounds yield $\rho_2\le c_n$ and $\rho_2\le c_m/2$ because every positive-length fair binomial is uniform modulo 2. For a third bound use Cauchy–Schwarz on the fiber sum $\sum p_n(i)p_m(j)$. The sum of the squared first factors is at most $c_n/2$ because the indices are distinct and have the same parity. The sum of the squared second factors is at most $\sum_jp_m(j)^2=c_{2m}$ by Vandermonde's identity. Thus $\rho_2^2\le c_n c_{2m}/2<1/(3\sqrt{UV})$. If $U/V\ge3$, then $(U+V)\rho_2^2\le(4/3)Uc_n^2<8/9$. If $U/V\le1$, then $(U+V)\rho_2^2\le 2V c_m^2/4<(m+1/2)c_m^2<2/3$. For $1\le x=U/V\le3$, the third bound gives $(U+V)\rho_2^2\le(\sqrt x+1/\sqrt x)/3\le4/(3\sqrt3)<8/9$.

This proves the line estimate including nonprimitive steps. No optimality of $8/9$ is asserted.

## The one-relation theorem

For independent fair bits and real weights, changing a sign translates the law and zeros have no effect. Group the $s$ nonzero absolute types; their counts are independent binomials. If the types are rationally independent, their count tuple identifies the sum, so $K\rho^2=\prod_i(n_i+1)c_{n_i}^2\le1$. This also covers the empty product.

If the types have rational rank $s-1$, their integer relation lattice is $\mathbb Zh$ for a primitive vector $h$: clear denominators in a generator of the one-dimensional rational kernel and divide out its gcd. Any rational multiple of the resulting vector that has integer entries is an integer multiple, by Bézout's identity. Two tuples give the same weighted sum exactly when they differ by an element of this lattice. Inactive coordinates ($h_i=0$) therefore factor out, each contributing $(n_i+1)c_{n_i}^2\le3/4$. From now on $s$ counts only active coordinates, all $h_i\ne0$; there are at least two. Let $l_i=|h_i|$. If some multiplicity $n_i<l_i$, all intersections with this box are singletons, giving the product bound again.

Now $n_i\ge l_i$ throughout. Every nonempty intersection of a coset with the box has exactly one first point under steps by $h$. Subtracting the points with a predecessor gives
$$
V_0=\prod_i(n_i+1),\qquad f_i=\frac{l_i}{n_i+1},\qquad
K=V_0\left[1-\prod_i(1-f_i)\right].
$$
Order the coordinates so $f_1\ge f_2\ge\cdots$. Project any *one* full fiber into coordinates 1 and 2. It maps injectively into a single coset of $\mathbb Z(h_1,h_2)$, since the projection retains the integer parameter along $h$ and $(h_1,h_2)\ne0$. Its mass is therefore at most $\rho_2\prod_{i\ge3}c_{n_i}$. The two-coordinate count is
$$
K_2=(n_1+1)(n_2+1)\big[1-(1-f_1)(1-f_2)\big].
$$
Combining both counts and the line estimate yields
$$
K\rho^2\le\frac89\left(\frac34\right)^{s-2}
\frac{1-\prod_i(1-f_i)}{1-(1-f_1)(1-f_2)} .
$$
The ratio is the sum of all $u_i=f_i\prod_{j<i}(1-f_j)$ divided by $u_1+u_2$. These nonnegative numbers decrease with $i$, so this ratio is at most $s/2$. The maximum of $(s/2)(3/4)^{s-2}$ for integers $s\ge2$ is $9/8$, attained at $s=3,4$. This proves $K\rho^2\le1$, for all multiplicities including 1.

Finally, if the types are partitioned into disjoint blocks whose rational spans form a direct sum, equality of sums forces equality in each block separately. The block sums are independent, so both support sizes and largest probabilities multiply. The claimed direct-sum extension follows whenever the proved inequality holds on each block.
