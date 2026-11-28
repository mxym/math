# Sharp absolute permanent–determinant tradeoff in every order

## Statement and scope

For an \(n\times n\) complex matrix \(A=(a_{ij})\), write \(N(A)=\prod_i\|A_{i,*}\|_2\) and put \(\rho_n=n!/n^{n/2}\).

**Theorem.** For every integer \(n\ge5\), every real \(c\ge0\), and every complex \(A\),
\[
 |\operatorname{per}A|+c|\det A|
 \ \le\ \max\{\rho_n,\,1+c\}\,N(A). \tag{1}
\]
The constant is sharp. If there is no zero row, the equality cases are exactly:
- \(c<\rho_n-1\): rank one with a common equimodular nonzero row vector;
- \(c=\rho_n-1\): that rank-one class and the complex monomial matrices;
- \(c>\rho_n-1\): complex monomial matrices.

A complex monomial matrix has exactly one nonzero entry in each row and column. Row scalings and row and column phases need not be real. The sharp formula in (1) is already known in orders three and four from the [previous repository manuscript](https://github.com/mxym/math/blob/main/manuscripts/complex-permanent-pencil/paper.md), Theorem 1 and Part Q. For order two the absolute-value formula follows from
\[
 |a_1b_2+a_2b_1|,\ |a_1b_2-a_2b_1|
 \le |a_1b_2|+|a_2b_1|\le\|a\|_2\|b\|_2
\]
and a monomial witness. Thus the sharp **value** holds in every order \(n\ge2\); the proof here covers the previously untreated orders \(n\ge5\).

For the complex-matrix row-Euclidean pencil norm
\[
 C_n(\lambda)=\sup_{N(A)=1}|\operatorname{per}A+\lambda\det A|
\]
this gives
\[
 C_n(t)=\max\{\rho_n,\,1+|t|\}\qquad (n\ge2,\ t\in\mathbb R).
\]
Indeed, choose an even or odd permutation matrix according to the sign of \(t\) for the second branch; the equimodular rank-one witness gives the first. Also \(C_n(\lambda)=\rho_n\) whenever \(|\lambda|\le\rho_n-1\). Outside that disk, (1) is still an upper bound but need not be attained by a common phase. No exact answer for arbitrary nonreal \(\lambda\) in orders \(n\ge4\), or maximality of this disk as a flat-value region, is claimed.

## 1. The determinant envelope

It is enough to consider matrices with all row lengths one. Set \(P=|\operatorname{per}A|\), \(D=|\det A|\), \(G=AA^*\), and
\[
 r^2=\frac{1}{n(n-1)}\sum_{i\ne j}|G_{ij}|^2,\qquad
 d_n(r)=(1-r)^{(n-1)/2}\sqrt{1+(n-1)r}.
\]
Here \(0\le r\le1\), by Cauchy–Schwarz. The determinant satisfies
\[
 D\le d_n(r). \tag{2}
\]
It is the sharp arithmetic mean–variance determinant envelope, a direct application of [Rodin's mean–variance AM–GM theorem](https://arxiv.org/abs/1409.0162). Here is a short proof for the exact parameter range needed. The nonnegative eigenvalues \(x_i\) of \(G\) have sum \(n\) and \(\sum_i x_i^2=n+n(n-1)r^2\). For \(0<r<1\), maximizing their product under these two constraints gives an interior point: \((1+(n-1)r,1-r,\ldots,1-r)\) is a positive feasible point, while a boundary point has product zero. The two constraint gradients are independent since the variance is nonzero. Stationarity for \(\sum_i\log x_i\) gives \(1/x_i=a+2b x_i\), so there are exactly two distinct values \(h>\ell>0\) and \(2b=-1/(h\ell)\). If two entries equal \(h\), the vector increasing one and decreasing the other is tangent to both constraints. In this direction the diagonal Hessian of the Lagrangian has strictly positive coefficient \(-1/h^2+1/(h\ell)\), contradicting the necessary second-order maximum condition on the smooth constraint manifold. Thus \(h\) occurs once. The two constraints then give \(h=1+(n-1)r,\ell=1-r\). Taking a square root of the product gives (2). For \(r=0\), \(G=I\); for \(r=1\) all row pairs are proportional by Cauchy–Schwarz, so \(G\) is singular. These endpoints also obey (2).

Two monotonicity observations control the entire correlation interval:
\[
 \frac{1-d_n(r)}{r^2}\text{ is nonincreasing on }(0,1],\qquad
 w_n(r):=\frac{d_n(r)}{1-r^2}\text{ is decreasing on }(0,1). \tag{3}
\]
Indeed,
\[
 -d_n'(r)=\frac{n(n-1)r}{2}\,
 \frac{(1-r)^{(n-3)/2}}{\sqrt{1+(n-1)r}}.
\]
Integrating with argument \(rs\) makes the first quotient an integral of a nonincreasing function of \(r\), with nonnegative weight \(n(n-1)s/2\) for \(0\le s\le1\). The log derivative of the second quotient is
\[
 \frac{w_n'(r)}{w_n(r)}
 =\frac{r}{1-r}\left[\frac{2}{1+r}
            -\frac{n(n-1)}{2(1+(n-1)r)}\right]<0\quad (n\ge5).
\]
The last sign follows by multiplying positive denominators: \(n(n-1)-4+(n-1)(n-4)r>0\).

## 2. Two different permanent envelopes

### 2.1. Pair averaging for every \(r\)

Put \(m=\lfloor n/2\rfloor\), \(a_n=n/(2(n-1))\), and \(B_n=1-a_n^{m/2}\).
For a pair \(u,v\) of unit rows,
\[
 \sum_{j<k}|u_j v_k+u_k v_j|^2
 =1+|\langle u,v\rangle|^2-2\sum_j |u_j v_j|^2
 \ \le\ 1+(1-2/n)|\langle u,v\rangle|^2. \tag{4}
\]
The identity is expansion, and the inequality is Cauchy–Schwarz on the \(n\) numbers \(u_j\overline{v_j}\).

We use the phase-sensitive permanent block inequality of [Roos, Theorem 1.3, (20)–(22)](https://arxiv.org/pdf/1906.06176), [journal version](https://doi.org/10.1080/03081087.2024.2436061). In its notation \(F(A,k)\) is the average over all row and column \(k\)-sets of \(|\operatorname{per}A[I,J]/k!|^2\). For a composition of \(n\) into parts \(w_i\), his theorem gives \(P\le n!\prod_i F(A,w_i)^{1/2}\). For \(m\) parts of size two and, when needed, one singleton, (4) yields
\[
 F(A,1)=1/n,\qquad
 F(A,2)\le\frac{1+(1-2/n)r^2}{4\binom n2}
         =\frac{a_n+(1-a_n)r^2}{n^2}.
\]
As \(m/2\ge1\), the graph of \(x\mapsto (a_n+(1-a_n)x)^{m/2}\) on \([0,1]\) lies below the chord through its endpoints. Therefore
\[
 P\le\rho_n\big(a_n+(1-a_n)r^2\big)^{m/2}
   \le \rho_n\big(1-B_n(1-r^2)\big). \tag{5}
\]
In particular, for a chosen splice \(t\in(0,1)\) the strict condition
\[
 B_n>(1-1/\rho_n)\,w_n(t) \tag{6}
\]
ensures \(P+(\rho_n-1)D<\rho_n\) for all \(t\le r<1\), by (2), (3), and (5).

### 2.2. A complementary-block bound

For any rectangular matrix \(V\) with \(j\) rows, write \(G_V=VV^*\). If \(f(z)=\prod_{i=1}^j\sum_k V_{ik}z_k\), the permanental Gram identity is
\[
 \operatorname{per}G_V=\sum_{|\alpha|=j}\alpha!\,|[z^\alpha]f(z)|^2. \tag{7}
\]
For completeness, expand the inner products on the left. Assign a column to each row. Upon summing over row permutations, the other copy of the product ranges over assignments with identical multiplicities \(\alpha\); each such assignment occurs exactly \(\prod_k\alpha_k!\) times. Collecting terms gives (7). In particular, the sum of squared permanents of the maximal square column minors is at most \(\operatorname{per}G_V\): those minors are precisely the coefficients with no repeated column.

For a principal \(j\times j\) Gram submatrix \(G_I\), \(j\ge2\), let \(r_I^2\) be its average squared off-diagonal modulus. Then
\[
 \operatorname{per}G_I\le 1+(j!-1)\,r_I^2. \tag{8}
\]
For a permutation moving \(k\ge2\) indices, each of its \(k\) off-diagonal factors has modulus in \([0,1]\). Their product is at most the arithmetic mean of their squared moduli: apply AM–GM to the squared moduli, using exponent \(k/2\ge1\). Every off-diagonal position has the same coefficient after summing these averages over all nonidentity permutations, by relabeling. The coefficients sum to \(j!-1\), giving (8).

Partition the rows into \(I\) of size \(m=\lfloor n/2\rfloor\) and \(I^c\) of size \(\ell=n-m\). The complementary-column Laplace expansion, Cauchy–Schwarz and (7) give \(P\le\sqrt{\operatorname{per}G_I\operatorname{per}G_{I^c}}\). Apply arithmetic–geometric mean, (8), and average the result over all \(I\). For each side, its average \(r_I^2\) or \(r_{I^c}^2\) is exactly \(r^2\), since every ordered pair of distinct row labels has the same sampling probability. Hence
\[
 P\le 1+K_n r^2,\qquad K_n=\frac{m!+\ell!-2}{2}. \tag{9}
\]
For a chosen splice \(t\), the strict condition
\[
 (\rho_n-1)(1-d_n(t))> K_n t^2 \tag{10}
\]
ensures \(P+(\rho_n-1)D<\rho_n\) for \(0<r\le t\), by (2), (3), and (9).

## 3. The splice in orders five through fifteen

Use \(t=2/5\) for \(n=5\), \(3/10\) for \(6\le n\le14\), and \(1/5\) for \(n=15\). The following are exact rational lower-bound checks for the left minus right sides of (10) and (6). To reproduce, for a positive rational \(q=p/s\) set
\[
 L(q)=\frac{\lfloor\sqrt{\lfloor10^{12}p/s\rfloor}\rfloor}{10^6},\qquad
 U(q)=L(q)+10^{-6}.
\]
Thus \(L(q)\le\sqrt q<U(q)\) even for a perfect rational square. In (10) take \(\rho_n\) from below by \(L((n!)^2/n^n)\) and \(d_n(t)\) from above by \(U(d_n(t)^2)\). In (6) take \(\rho_n\), \(a_n^{m/2}\), and \(d_n(t)\) from above by \(U\) of their rational squares. If \(X,Y\) are the resulting lower bounds for the margins of (10) and (6), respectively, the table lists their floors after multiplication by \(10^6\).

| \(n\) | \(t\) | \(\lfloor10^6 X\rfloor\) | \(\lfloor10^6Y\rfloor\) |
|---:|:---:|---:|---:|
|5|2/5|1028|5872|
|6|3/10|370843|36617|
|7|3/10|680135|37322|
|8|3/10|2305259|174631|
|9|3/10|3326800|223472|
|10|3/10|10942540|357031|
|11|3/10|11236434|411216|
|12|3/10|48222200|519283|
|13|3/10|7664057|564563|
|14|3/10|192523504|646288|
|15|1/5|260514206|461840|

All coefficients or radicands are nonnegative in the indicated comparisons, as checked by \(1<L(\rho_n^2)\) and \(U(d_n(t)^2)<1\). The exact companion [script](verify_factor_permanent_determinant_all_orders.py) uses fractions and integer square roots and also checks the simple rational comparisons below. Only the two monotone scalar inequalities are reduced to these endpoints; no discretization of matrices or correlation values is used.

## 4. A uniform argument for all \(n\ge16\)

Choose \(t=3/(4(n-1))\le1/20\). To check (6), first
\[
 d_n(t)^2 =\frac74\left(1-\frac{3}{4(n-1)}\right)^{n-1}
 <\frac74 e^{-3/4}<\frac{224}{269}<\left(\frac{11}{12}\right)^2.
\]
Here \(e^{3/4}>1+3/4+(3/4)^2/2+(3/4)^3/6=269/128\). With \(a_n\le8/15\) and \(m/2\ge4\), the requisite stronger comparison is
\[
 w_n(t)<\frac{11}{12}\frac{400}{399}
              <1-(8/15)^4\le B_n. \tag{11}
\]
This closes \(t\le r<1\).

For \(0\le r\le t\), a different Gram estimate replaces the large factorial in (9). Write \(E=|G-I|\) entrywise, and \(S=\|E\|_{\mathrm F}=\sqrt{n(n-1)}\,r\le (3/4)\sqrt{16/15}<4/5\). A permutation term of \(\operatorname{per}(I+E)\) is a product of the weights of vertex-disjoint directed simple cycles of length at least two, each weight the product of the edge entries of \(E\). For a given length \(k\), the sum of weights of these individual cycles is at most \(\operatorname{tr}(E^k)/k\), since tracing includes all their \(k\) rotations as well as possibly non-simple closed walks. Dropping the disjointness constraint bounds the resulting sum over sets of cycles by the product of \(1+\text{weight}\) over individual cycles, and thus by the exponential of their weight sum. The real symmetry of \(E\) gives \(\operatorname{tr}(E^k)\le\sum_i|\lambda_i(E)|^k\le S^k\) for \(k\ge2\). By (7) applied to the full matrix,
\[
 \begin{split}
 P^2\le\operatorname{per}G
 &\le\operatorname{per}(I+E)
 \le\exp\left(\sum_{k\ge2}\frac{S^k}{k}\right)
 \le\exp\left(\frac52 S^2\right),\\
 P&\le 1+\frac{25}{4}S^2.
 \end{split} \tag{12}
\]
The last estimate uses \(u=5S^2/4\le4/5\) and \(e^u-1\le u/(1-u)\le5u\), which follows from the power series for \(e^u\).

Meanwhile, for \(0\le r\le t\), Bernoulli's inequality gives \((1-r)^{(n-3)/2}\ge1-(n-3)r/2\ge5/8\), whereas \(\sqrt{1+(n-1)r}\le\sqrt{7/4}<4/3\). Integrating the derivative from (3) therefore gives
\[
 1-D\ge1-d_n(r)\ge\frac{15}{128}\,S^2. \tag{13}
\]
Finally, \(\rho_{16}-1>54\), and \(\rho_{n+1}/\rho_n=\sqrt{n+1}(1+1/n)^{-n/2}>1\) in this range, since \((1+1/n)^n<e<3\). As \(54\cdot15/128>25/4\), (12) and (13) close \(0<r\le t\) strictly. Together with (11), they cover the infinite tail without any dimension-dependent search.

## 5. Endpoints, equality and sharpness

We have proved \(P+(\rho_n-1)D<\rho_n\) at every \(0<r<1\). At \(r=1\), the rows are proportional and \(D=0\). The permanent becomes \(n!\) times the product of the entries of a common unit row vector, in modulus; arithmetic–geometric mean gives \(\rho_n\) with equality exactly for an equimodular vector. At \(r=0\), \(G=I\), \(D=1\), and (7) gives \(P\le1\). Equality forces \(\prod_i(\sum_j a_{ij}z_j)\) to be a nonzero multiple of \(z_1\cdots z_n\). Unique factorization over \(\mathbb C\) makes each row form a different coordinate multiple, precisely a monomial matrix. This proves the critical inequality and both equality classes.

For \(c<\rho_n-1\) subtract \((\rho_n-1-c)D\) from the critical bound, leaving equality only at the flat matrices. For \(c>\rho_n-1\) add \((c-\rho_n+1)D\) and use \(D\le1\), leaving equality only at monomial matrices. Positive real row normalization is reversible; if any row is zero both sides of (1) vanish. The two displayed equality families furnish the sharp constants.

## Dependencies and comparison

[Carlen–Lieb–Loss](https://arxiv.org/abs/math/0508096) establish the sharp pure permanent constant \(\rho_n\) and its rank-one equality; the permanent pair-averaging inequality used above is from [Roos](https://arxiv.org/abs/1906.06176), not new here. The mean–variance product envelope (2) is a special case of [Rodin](https://arxiv.org/abs/1409.0162) and is proved again above. The existing repository result uses the exact two-row mixed rectangular calculation to handle the equal complementary blocks of order four; it does not give (1) above order four. The present step uses the fixed Gram statistic \(r\) to combine the phase-sensitive many-pair bound with independent Gram bounds and the sharp determinant envelope, yielding a complete real-parameter result and sharp absolute-value tradeoff in all orders. This argument does not solve the nonreal-coefficient pencil generally or assert chronological priority for all ingredients.

Run the finite endpoint check with:
```sh
python3 verify_factor_permanent_determinant_all_orders.py
```
