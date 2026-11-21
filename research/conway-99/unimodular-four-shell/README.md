# A norm-four search in an even unimodular lattice

A Conway graph exists if and only if the following finite configuration exists. This uses the same target for all four remaining Seidel ranks and places the 99 points on the shortest shell in the rootless case.

* Take a positive definite even unimodular lattice $T'$ of rank 48. It may be required to be indecomposable with at most three antipodal root pairs.
* Let $K$ be the orthogonal sum of two binary lattices with bases $a_j,b_j$ and Gram matrix $\left(\begin{smallmatrix}2&1\\1&4\end{smallmatrix}\right)$. Set $e=b_1+b_2$ and $K_0=\{k\in K:(e,k)\equiv0\pmod3\}$. Embed $K_0$ isometrically in $T'$, extending the embedding to its real span.
* Among the squared-norm-four vectors of $T'$, retain those $z$ whose orthogonal projection on this four-dimensional span is $e/3$. Find 99 of them with mutual inner products 0 or 1.

An edge is a pair with inner product zero. The list of positive definite even unimodular lattices in fixed rank is finite up to isometry. For any given Gram matrix the embedding test and the subsequent search take place on finite shells. This criterion does not enumerate the lattices.

## A bound that also holds in the dual shifted coset

Use the [rank-44 determinant-49 lattice](../maximal-marked-lattice/README.md) $U$ with marks $v_i=3u_i$. For any $x\in v_0+3U^*$, put $g_i=(x,v_i)$ and $N=(x,x)$. Then $g_i\equiv k\pmod9$ with $k=1,4,$ or $7$. This follows since $v_i-v_j=3(u_i-u_j)$ and $u_i-u_j\in U$. The centering, second-moment and rounding arguments from the [primal marked-coset bound](../marked-coset-shells/README.md) give $7N\ge11k(9-k)$, including for nonintegral $N$.

In fact $N\ge22$. For $N<22$ only $k=1$ is possible. Write $g_i=1+9n_i$. Then
$$\sum n_i=-11,\qquad \sum n_i^2=(7N+11)/9,\qquad An=-4n-2\mathbf1.$$
The even integer $\sum n_i(n_i+1)$ is at most six. The total positive mass is at most three. An entry at most $-2$ would require neighbor sum at least six. If there is a positive entry of two, it uses the entire budget of six and there are thirteen negative units. Each of those needs neighbor sum two and must see the sole positive site. That site would see all thirteen negatives and have neighbor sum $-13$, although it needs $-10$. Otherwise there are at most three positive unit entries. Each of at least eleven negative units needs two positive neighbors. The positive pairs have at most $2\binom32=6$ common-neighbor incidences in total. This proves the bound.

At equality the point already belongs to the primal marked coset: an element of $U^*$ with even integral squared norm has isotropic class, which vanishes in the anisotropic discriminant plane. Since $x=v_0+3d$ and multiplication by three is invertible on the discriminant group, $d\in U$. The norm-22 points therefore give exactly the independent sets described in the primal result.

## Gluing and the index-three neighbor

Both $U$ and $K$ have discriminant group $(\mathbb Z/7)^2$. The form of $U$ is anisotropic by the determinant-49 reduction. For $K$, coordinates dual to the two $b_j$ give the finite quadratic form $(s^2+t^2)/7$, which is anisotropic since $-1$ is a nonsquare modulo seven. A nonsingular anisotropic quadratic plane over this field is unique up to isometry, and negating it preserves anisotropy. Choose an anti-isometry of the discriminant forms. The pairs in $U^*\oplus K^*$ whose classes correspond give an even integral lattice $T$ of index 49 over $U\oplus K$, hence unimodular. Its intersections with the individual real summands are exactly $U$ and $K$.

Every vector in $U^*\setminus\{0\}$ has squared norm at least two. Indeed $U^*\subseteq L^*$ and $\sqrt7 L^*$ has minimum at least fourteen. A root of $T$ cannot have two nonzero components. The roots in $K$ are precisely $\pm a_1,\pm a_2$. The roots in $U$ have integral evaluations $(u_i,r)$ by their [signed Fano support](../short-support-packing/README.md). [Dual minimum](https://github.com/YesterdaysLemon/conway-99-research/tree/main/attempts/wave71-modular-theta-extension)

Let $t=v_0+e$, of squared norm 36, and define
$$T_0=\{s\in T:(s,t)\equiv0\pmod3\},\qquad T'=T_0+\mathbb Z(t/3).$$
The vector $t$ pairs to one with $a_1$, so $[T:T_0]=3$ and $t/3\notin T$. Since $t\in T_0$, adjoining $t/3$ reverses the index. Its squared norm is four and it pairs integrally with $T_0$. Thus $T'$ is even unimodular. Of the roots originally in $T$, exactly the roots of $U$ survive. Each of the other two cosets of $T_0$ in $T'$ has, up to sign, the form $t/3+s$ with $s\in T_0$. Three times its projection to $U\otimes\mathbb R$ lies in $v_0+3U^*$. The preceding bound makes its squared norm strictly greater than eighteen, precluding a root in either coset. Thus $T'$ has precisely the roots of $U$, at most [three antipodal pairs](../four-root-exclusion/README.md). The same bound prevents pure $K$ vectors from these two new cosets, giving $T'\cap (K\otimes\mathbb R)=K_0$.

The vectors $z_i=(v_i+e)/3$ belong to $T'$: their differences from $t/3$ are $u_i-u_0\in U$, and $(v_0,u_i-u_0)$ is a multiple of three. Each has squared norm four and the indicated projection. Distinct marks have inner product $(-8+8)/9=0$ or $(1+8)/9=1$. They span a 45-dimensional real space because their differences span the original 44-space and their common projection is nonzero.

In any orthogonal decomposition of $T'$ a mark meeting two summands would split into two roots. Every root has zero projection on the four-space, whereas every mark has nonzero projection. Thus each mark lies in a single summand. The graph of nonzero inner products between the marks is connected, having degree 84 on 99 sites, so one summand contains their entire 45-dimensional span. A nonzero complementary even unimodular summand has dimension divisible by eight and cannot fit in the remaining three dimensions. This proves indecomposability.

## Recovering a graph and searching a specified lattice

Conversely, subtract $e/3$ from each of the 99 selected vectors and multiply by three. They now lie in dimension 44, have squared norm 28 and have mutual inner products $-8$ or 1. The [tight-frame equality argument](../maximal-marked-lattice/README.md) gives a strongly regular graph with parameters $(99,14,1,2)$.

In coordinates $(a_1,b_1,a_2,b_2)$ a basis of $K_0$ is
$$(3,0,0,0),\ (-4,1,0,0),\ (-1,0,1,0),\ (-4,0,0,1).$$
A smaller basis and the four required pairings make the search practical for an individual input lattice. Run `python3 verify.py` to check its Gram matrix, determinant and height vector. Enumerate embeddings using the basis in the checker. For each embedding, form the graph on the norm-four vectors with the prescribed four pairings, joining two vectors if their inner product is zero or one. A clique of size 99 would provide the construction. None is asserted here.

## Excluding every even 2-neighbor of an extremal rank-48 lattice as the target

For the specific $T'$ just constructed, **every even unimodular 2-neighbor has a vector of squared norm four in common with $T'$**. In particular none can have minimum six. This excludes a family of candidate target lattices independently of their automorphism groups.

Let $T''$ be such a neighbor, meaning $T'\cap T''$ has index two in both. The common sublattice is the kernel of a nonzero linear functional $f$ on $T'/2T'$. Its representing vector is isotropic for the quadratic form $h\mapsto(h,h)/2\bmod2$. Indeed choose $z\in T''\setminus T'$. The class of $2z$ in $T'/2T'$ is nonzero, pairs evenly with the common sublattice, and has squared norm divisible by eight.

If any marked $z_i$ has $f(z_i)=0$, it survives in the neighbor. Otherwise $f(z_i)=1$ for all $i$ and $f$ vanishes on all $u_i-u_j$. The lattice they generate has odd index in $U$: adjoining $3u_0$ has index three, and the maximal extension has index a power of seven. The index-49 gluing and the index-three neighbor construction also preserve the lattice after localization at two. Thus modulo two we can work in the orthogonal direct sum of $U$ and $K$ and the representing class has zero $U$-component. Since $3z_i=v_i+e$, the remaining class $h\in K/2K$ must have $(h,e)=1\bmod2$.

There are three more norm-four vectors in $K_0$, namely $b_1-a_1$, $a_2-a_1$ and $b_2-a_2$. If all three pair oddly with $h$, the only possibilities for $h$ in coordinates $(a_1,b_1,a_2,b_2)$ are $(1,0,0,1)$ and $(0,1,1,0)$. Both have squared norm two modulo four. This contradicts isotropy and proves the assertion.

For a nonconstant vector of mark values, at least eight marks survive. Indeed $\sum_{j\sim i}z_j+4z_i=6e=2(3e)$ with $3e\in T'$. Thus each vertex sees an even number $d$ of surviving marks. If there are $w>0$ such marks with $E$ internal edges, double counting common neighbors gives
$$w(w-1)-E=\sum\binom d2\ge\sum d/2=7w.$$
Consequently $w\ge8$. The three-vector obstruction also covers the constant case with no surviving marks. The existence criterion may impose this 2-neighbor exclusion in addition to indecomposability and the root bound.
