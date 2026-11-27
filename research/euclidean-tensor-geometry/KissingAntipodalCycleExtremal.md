# How antipodal can a cycle in a kissing configuration be?

Let the points be unit vectors with every off-diagonal inner product at most $1/2$. The **strength** of a path or cycle of distinct vertices is the least of $-\langle x_i,x_{i+1}\rangle$ over its edges (including the closing edge for a cycle). No restriction on dimension is imposed unless specified.

* Among **at most 21 points**, the largest cycle strength is exactly $0.861833162550\ldots$. It occurs only on a rigid 15-cycle of rank six. It is attained even in **exactly 21 points in dimension six**.
* For **at most 132 points**, no cycle has strength as large as $0.862072537$. For **any finite number** the corresponding exclusion is $0.862073192$. The supremum over all finite cycles is greater than $0.862073128190$, by an explicit 4,099-point witness in unrestricted dimension. We do not identify this supremum exactly.
* For paths and cycles with the number of vertices tending to infinity the optimal strengths have the same limit, with error $O(n^{-2})$. Finite path certificates also give bounds on how many very negative products a kissing code can have.

These are restrictions on distance distributions. They do not lower the unrestricted upper bound on either the six- or seven-dimensional kissing number. The [sharp short-path theorem](KissingSharpAntipodalPath.md) at $0.862389331567\ldots$ remains stronger for the very shortest chains.

## 1. Circulant Gram matrices turn cycles into a moment problem

Let $a_n$ be the best strength of an $n$-cycle. Average its positive semidefinite Gram matrix over cyclic permutations. The common lag-one entry cannot increase past minus the original strength; all other off-diagonal entries remain at most $1/2$. Conversely a positive semidefinite circulant matrix with diagonal one is a real Gram matrix. By the discrete Fourier basis, its lag-$j$ entry has the form
\[
 c_j=\sum_{k=0}^{\lfloor n/2\rfloor}p_k\cos(2\pi kj/n),
 \qquad p_k\ge0,\quad\sum_k p_k=1 .
\]
Here a mass at an ordinary frequency stands for equally divided masses at that frequency and its negative; the constant and Nyquist modes need no doubling. Thus $a_n=\max(-c_1)$ with $c_j\le1/2$ for $n\nmid j$.

Put $U=.862073192$. The [data](kissing-antipodal-cycle-data.json) give 25 nonnegative rational coefficients $y_j$, largest lag 222, for which
\[
 P(\theta)= U+\cos\theta+\sum_jy_j\big(\cos(j\theta)-\tfrac12\big)>0
 \quad\text{on }[0,\pi].
\]
If no listed lag is divisible by $n$, integration over the cycle's frequencies gives $a_n<U$. The 49 exceptional lengths dividing a listed lag have their own rational duals, positive at every frequency of the corresponding grid, using only nonzero lags modulo $n$. This covers **all** lengths. A second set of finite-grid duals gives $a_n<.862072537$ for $3\le n\le132$ (using §2 for $n=15$). It gives $a_n<.861832$ for every $3\le n\le21$ except 15.

For the lower bound, the data give nonnegative weights of denominator $10^{13}$ on a 4,099-grid. Distribute the leftover mass uniformly over the full cyclic group: it contributes zero to each nonzero lag. All 2,049 nonzero lags up to sign satisfy the required inequalities and $-c_1>.862073128190$. A smaller independent witness on the 1,201-grid also has $-c_1>.8620731$. These are **not** asserted to be realizable in six dimensions.

The checker independently certifies continuous positivity without relying on a polynomial solver or a supplied subdivision tree. It encloses cosines on the $2^{18}$-grid using integer square roots and half angles. With $M=1+\sum j^2y_j$, the loss between a function and its chord on a mesh interval of width $h$ is at most $Mh^2/8$. Every mesh value stays strictly above that loss. The other cosine grids use a separately enclosed complex rotation, with a certified error bound for every successive step.

## 2. The exact small-code answer and its rigidity

Let $r_k=\cos(2\pi k/15)$. Use the three real Fourier planes at frequencies $5,6,7$, with respective squared radii
\[
 p_5=\tfrac13-t,\qquad p_6=\tfrac23,\qquad p_7=t,
 \qquad t=\frac{2(1-\cos(2\pi/5))}{3(\cos(2\pi/15)+1/2)}.
\]
Explicitly $x_i$ is the concatenation of $\sqrt{p_k}(\cos(2\pi ki/15),\sin(2\pi ki/15))$ for these three $k$. All weights are positive. The products at lags $2,5$ equal $1/2$: the first follows from the definition of $t$, and the second from $r_{25}=r_{35}=-1/2$ and $r_{30}=1$. The other lags are strictly below $1/2$. The strength is
\[
                    a_{15}=-(p_5r_5+p_6r_6+p_7r_7).
\]
For the upper bound set
\[
 y=(r_5-r_7)/(r_{14}-r_{10}),\qquad
 z=(r_5-r_6+y(r_{10}-r_{12}))/(r_{30}-r_{25}),\qquad
 C=-r_5-yr_{10}-zr_{25}.
\]
The function $C+r_k+yr_{2k}+zr_{5k}$ vanishes identically at $k=5,6,7$ and is positive at $k=0,\dots,4$. The checker certifies these latter inequalities and $y,z>0$ with rational intervals; the vanishing at the three supporting frequencies follows algebraically from the displayed formulas and $r_{25}=r_{35}$. Integration gives $-c_1\le C+(y+z)/2$, with equality for the displayed code.

**Rigidity is for the original cycle, not just its cyclic average.** At equality each individual lag-one entry equals $-a_{15}$ and every lag-two and lag-five entry equals $1/2$, since their means saturate bounds with positive coefficients. The averaged Gram matrix has Fourier support in $K=\{5,6,7,8,9,10\}$. The kernel of an average of positive semidefinite matrices is contained in the kernel of each summand. Consequently the original Gram matrix has both its row and column spaces in the complex span of the same six characters.

Write $\xi_k=e^{2\pi i k/15}$ and expand the original matrix in the basis $\xi_k^i\xi_l^j$, $k,l\in K$, with symmetric coefficients. For fixed $h=k+l\bmod15$ there are at most three unordered pairs $\{k,l\}$. Restricting to entries $(i,i+s)$ and taking frequency $h$ in $i$ yields, for $s=0,1,2$, sums of the coefficients times $1,(\xi_k+\xi_l)/2,(\xi_k^2+\xi_l^2)/2$ (absorb multiplicity two for $k\ne l$). Put $v=\xi_k+\xi_l$. The last expression is $(v^2-2\xi_h)/2$. Distinct unordered pairs at fixed product $\xi_h$ have distinct $v$, as they are the roots of $X^2-vX+\xi_h$. Thus each of these systems is Vandermonde and injective. The three known constant diagonals $s=0,1,2$ determine the entire matrix, which must equal that of the displayed cycle. Its rank is exactly six by positivity of the three weights and independence of the six characters.

The finite duals in §1 exclude all other cycle lengths through 21 even at $0.861832<a_{15}$. To attain the maximum on 21 points, add a regular unit hexagon in the frequency-five plane. Its six points have all mutual products at most $1/2$ and every cross-product with the original cycle has modulus at most $\sqrt{p_5}<1/2$. This shows why cardinality 21 and ambient dimension six alone cannot exclude a cycle at this threshold; it does **not** extend that code to a larger kissing configuration.

## 3. The common infinite-length limit

Let $A$ be the maximum of $-\widehat\mu(1)$ over even circle probability measures with real cosine moments $\widehat\mu(j)\le1/2$ for all $j\ge1$. Compactness gives a maximizer; the continuous dual gives $A<U$. Convolving an optimal $n$-cycle measure with the uniform law on $[-2/n,2/n]$ multiplies moment $j$ by $\operatorname{sinc}(2j/n)$, where $\operatorname{sinc}(x)=\sin x/x$. At nonzero multiples of $n$ the multiplier has modulus at most $1/2$. At other lags a positive multiplier cannot raise a moment beyond $1/2$; a negative one has modulus at most $1/\pi$. Hence
\[
                 a_n\operatorname{sinc}(2/n)\le A .
\]
Our finite witness and $\operatorname{sinc}(2/n)\ge1-2/(3n^2)$ give $A>.862073093984$.

Conversely put $d=\lfloor(n-1)/2\rfloor$. Take the normalized positive sine vector $w_i=\sqrt{2/(d+2)}\sin((i+1)\pi/(d+2))$ on $i=0,\ldots,d$. Convolve an optimizing measure with the nonnegative kernel $|\sum_jw_j e^{\mathrm i j\theta}|^2$ of mean one. Its multipliers $r_j=\sum_iw_iw_{i+j}$, using zero extension, are in $[0,1]$ and vanish past $d$. The path adjacency eigenvector identity gives $r_1=\cos(\pi/(d+2))$. Sample this convolved density on the $n$-grid with weight $1/n$. Its degree is at most $d$ and $2d<n$, so its mass and low moments are unchanged: each nonzero residue sees either a single Fourier coefficient or zero. The resulting feasible cycle gives $a_n\ge A\cos(\pi/(d+2))$.

Let $b_n$ denote optimal strength on an $n$-vertex path. A finite Toeplitz Gram matrix of an optimal circle measure gives $b_n\ge A$. For the converse take any such path, and now use the length-$n$ normalized sine vector $w_i$. The density $\|\sum_{j=0}^{n-1}w_j x_j e^{\mathrm i j\theta}\|^2$ has mean one. Its $j$th moment for $j\ge1$ is $\sum_iw_i w_{i+j}\langle x_i,x_{i+j}\rangle\le1/2$; at the first lag it is at most minus path strength times $\cos(\pi/(n+1))$. This gives $b_n\cos(\pi/(n+1))\le A$. The two estimates on each side prove $a_n=A+O(n^{-2})$ and $b_n=A+O(n^{-2})$. They do not assume monotonicity of $a_n$ or identify the supremum over finite $n$ with $A$.

## 4. Consequences for angular counts

A vertex with three neighbors of strength at least $s$ would have their sum project by at least $3s$ on its negative, whereas that sum has norm at most $\sqrt6$. Above $\sqrt{2/3}$ the degree is therefore at most two. Each cutoff in the following table is **above** $U$. Since cycles are then impossible, the graph is a union of paths.

| Join if $\langle x_i,x_j\rangle\le -s$ | .86213905 | .86209333 | .86208089 | .86207487 | .86207419 |
|---|---:|---:|---:|---:|---:|
| Maximum vertices per component (upper bound) | 10 | 15 | 20 | 30 | 40 |

For each column the data supply an entrywise nonnegative symmetric **integer** matrix $H$ on $n=L+1$ vertices. Positive definiteness is checked by fraction-free elimination. For the Gram matrix $G$ of a path of strength $a$,
\[
 0\le\operatorname{tr}(HG)
 \le \sum_i H_{ii}+\sum_{j\ge i+2}H_{ij}-2a\sum_iH_{i,i+1}.
\]
The upper bound on $a$ resulting from these exact integer sums is strictly below the column cutoff. Any longer path would contain a subpath on $n$ vertices. For every subset of $k$ points the number of pairs in this angular interval is therefore at most $k-\lceil k/L\rceil$. For example at $.86213905$ there are at most **18** such pairs on 21 vertices, **65** on 73 vertices and **114** on 127. The [earlier sharp theorem](KissingSharpAntipodalPath.md) gives a five-vertex bound at its stronger **strict** cutoff; it is not replaced by this table.

**Replay:** put [the Python verifier](verify-kissing-antipodal-cycles.py) and [the JSON data](kissing-antipodal-cycle-data.json) together and run `python3 verify-kissing-antipodal-cycles.py`. The proof uses integers and exact fractions only. The dual and primal coefficients and the path matrices may be found numerically; no numerical feasibility result is used as a proof. For context, [Krenedits–Révész](https://arxiv.org/abs/1504.03808) study the classical point-value problem with prescribed support; the present moment constraints are one-sided at every nonzero lag. [Musin](https://arxiv.org/abs/2309.13854v4) studies spherical distance distributions with multipoint SDP. The circulant and sine-kernel arguments use standard Fourier tools; the numerical constants, rigidity and finite certificates above are the specific claims.