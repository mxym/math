# Fifty-eight disjoint obtuse pairs at the seven-dimensional first excess

**Theorem.** Among any 127 unit vectors in $\mathbb R^7$ satisfying $x_i\cdot x_j\le1/2$ whenever $i\ne j$, there are **58 pairwise disjoint pairs** with inner product **strictly below $-1/2$**. Thus at most 11 vectors are left over. The old guarantee at 127 was 57. This is the first possible size above the 126 roots of $E_7$; the theorem neither proves that 127 points exist nor excludes them, and assumes no symmetry, root frame or exact antipodes.

The main small-code result is independent of the ambient dimension. For any $k$-point $60^\circ$ spherical code put
$$
 C(X)=\min_{p_i\ge0,\ \sum p_i=1}\sum_{i,j}p_i p_j f(x_i\cdot x_j),
 \qquad f(u)=u^4-u^2/4 .
$$
For **every** such seven-point code, $C(X)\le203/1000$; for **every** nine-point code, $C(X)\le1648/10000$. These are upper bounds, not claims about sharpness. The numerical solver in the supplied checker searches for separating inequalities; only exact integer tests can close a cell.

## 1. Which small graphs need certificates?

Join $i,j$ when $g_{ij}=x_i\cdot x_j<-1/2$. This graph is triangle-free since the squared norm of a sum of three pairwise strong vectors would be negative. On an independent set every off-diagonal cost is nonpositive, so an independent set of $a$ points gives $C(X)\le3/(4a)$. It suffices to handle independence number at most 3 at seven and at most 4 at nine.

The census adds one vertex at a time with independent neighborhood, rejects a large independent set, and merges isomorphic results. A degree bound equal to the independence bound is also valid because neighborhoods are independent. The canonical form refines a vertex partition by neighboring counts in each cell and branches over choices of the next distinguished vertex; twins inside the same cell are interchangeable. This gives 9 seven-vertex graphs, and 290 nine-vertex graphs before the next reduction. A subset perfect-matching recursion, pairing its least vertex with each available neighbor, identifies the 170 nine-vertex factor-critical graphs (deleting any single vertex leaves a perfect matching).

Here is why the other 120 nine-vertex graphs do not need Gram certificates. Take the maximum Tutte–Berge barrier $T$, breaking ties by largest $|T|$ as in the [earlier barrier proof, §1](https://github.com/mxym/math/blob/c36c642c5f6984e670f9ba2368f4bfafb5b966d7/research/euclidean-tensor-geometry/KissingOddComponentBarriers.md). The components off $T$ are odd and factor-critical, so in a triangle-free graph each has size one or odd size at least five. Writing $t=|T|$ and $o$ for their number gives $o\ge t+1$ and $o-t$ odd. A component of size five has two independent points; one of size seven has at least three (by $R(3,3)=6$). The sum of the component independence numbers cannot exceed four. If the original nine-vertex graph is not factor-critical, the only partitions left are $7+1$ after one deletion or $5+1+1$ after two. In different components all cross-costs are nonpositive; given local upper costs $c_j$, allocating mass in proportion to $1/c_j$ gives total cost at most $1/\sum_j(1/c_j)$. Using the new seven-point value and the [previous five-point bound $253/1000$](https://github.com/mxym/math/blob/c36c642c5f6984e670f9ba2368f4bfafb5b966d7/research/euclidean-tensor-geometry/KissingOddComponentBarriers.md), either partition gives a reciprocal strictly larger than $10000/1648$.

## 2. Exact continuous certificates on the remaining graphs

The [Gram-cell verifier](verify-kissing-nine-gram-cells.py) covers all 9 seven-vertex classes and all 170 factor-critical nine-vertex classes. A full replay visited 1,647 and 18,856 continuous cells respectively; the nine-point run closed 9,512 leaves by integer dual certificates and one by incompatible intervals. The largest nine-point tree had 545 nodes. Node counts are descriptive, not acceptance criteria. The edge and nonedge intervals are closed, $[-1,-1/2]$ and $[-1/2,1/2]$; using the closures can only enlarge the test domain. The diagonal is 1. Automorphisms reduce the domain: successively order each coordinate above the others in its orbit under the stabilizer of the preceding coordinates. Every assignment has a relabeling in the retained domain.

**Continuous interval propagation.** Store rational endpoint numerators over $K=4096$. Use the $2k$ formal vectors $x_i,-x_i$ so upper and lower constraints become lower bounds on signed inner products. If two successive lower numerators are $a,b$, and $a+b\ge0$, the upper bounds on their angles sum to at most $\pi$. Thus the outer lower numerator for the endpoints is
$$
 \left\lfloor\frac{ab-\left\lceil\sqrt{(K^2-a^2)(K^2-b^2)}\right\rceil}{K}\right\rfloor .
$$
The verifier checks the integer ceiling by squaring and propagates these inequalities through intermediate signed vertices. An incompatible interval is empty. A split covers both closed children, with a shared boundary. This does not discretize the possible Gram matrices.

**Quadratic upper witnesses.** On a scalar interval $[l,u]$ where $24t^2\ge1$ throughout, $f$ is convex and its secant is a linear upper bound; its slope is $(l+u)\{l^2+u^2-1/4\}$. Else use the larger endpoint value, also including zero if the interval crosses zero. These choices work since the nonzero interior stationary points of $f$ are minima. Denote the resulting affine majorants by $h_{ij}(g_{ij})$. For every integer mass vector $W\ge0$ totaling 600,
$$
 C(X)\le E_W(G)=
 \frac{(3/4)\sum_i W_i^2+2\sum_{i<j}W_iW_jh_{ij}(g_{ij})}{600^2}.
$$
Also $v^\mathsf TGv\ge0$ for every integer vector $v$, and every retained coordinate order gives a nonnegative difference $\Delta(G)$. Hence for nonnegative integer multipliers
$$
 C(X)\sum a_W\ \le\
 \sum a_W E_W(G)+\sum b_v v^\mathsf TGv+\sum d_\Delta\Delta(G).
$$
The right side is affine. Its exact maximum on the current box is obtained by taking the appropriate endpoints separately. If this maximum does not exceed the claimed target times $\sum a_W>0$, the full box passes. If $\sum a_W=0$, the corresponding strict negative upper bound instead proves infeasibility. Every multiplier, integer Gram direction and probability vector used in these decisions is checked or constructed with its required sign/normalization. The common denominator for the mass costs is $4K^4\cdot600^2$ when each variable is an endpoint numerator. The integer operations used for the scalar and propagation arrays fit signed 64-bit arithmetic; the final dual sums use arbitrary-precision integers.

SciPy's LP and spectral searches determine candidate data and split locations only; the LP status, primal value and numerical eigenvalues do not certify a bound. A failed solve, unclosed finest interval or exhausted budget is an error, not a successful leaf. This makes the proof independent of whether the numerical choices are exactly reproduced.

## 3. From the local capacity to 58 disjoint pairs

In dimension seven the constant spherical harmonic of $f$ is $1/84$ and its other nonzero harmonic coefficients are positive. A probability measure must therefore have total energy at least $1/84$. For the components outside a Tutte–Berge barrier the cross-costs are nonpositive. If $c_j$ are upper bounds for the individual optimized energies, this forces
$$
 \sum_j 1/c_j\le84.
$$
For the bigger components we use the uniform measure, with $U_q$ denoting an upper bound for the ordered sum including the diagonal divided by $q$. Averaging over $q$-subsets gives $U_k\le3/4+(k-1)(U_q-3/4)/(q-1)$ when $k\ge q$. In addition to the [fixed previous inputs](https://github.com/mxym/math/blob/c36c642c5f6984e670f9ba2368f4bfafb5b966d7/research/euclidean-tensor-geometry/verify-kissing-odd-component-barrier.js), the [new barrier replay](verify-kissing-127-reciprocal-barrier.js) contains 13 three-point energy charts:
$$
 q=21,27,29,35,37,43,45,57,59,73,79,83,87 .
$$
These use [Bachoc–Vallentin positive kernels](https://arxiv.org/abs/math/0608426) and the same direct-triple and outward Bernstein certificate as the previous proof. The replay checks all 13 exact rational bounds before rounding **up** to millionths.

Now suppose a 127-point configuration has matching number at most 57. The canonical barrier then has $o\ge t+13$, $o\equiv127-t\pmod2$. If $s$ components are singletons, their antipodes can be added after deleting $T$, so $s\le t+5$ by [Tomar's unrestricted bound 132](https://www.mefyi.com/papers/kissing-numbers-five-seven/). All other components have odd size at least five. Assign each size $k$ the strongest available lower bound on $10^6/c_k$ rounded **down**. The unbounded-part dynamic program over nonsingleton total size and component count, followed by $s$ singleton charges, gives minimum **84,004,920** over all admissible $t,o,s$. In particular it exceeds $84,000,000$, contradicting the previous inequality. The minimum occurs at $t=0,o=13,s=5$. This establishes 58 disjoint strict pairs, not 58 true antipodes.

**Replay.** Use a standard Node.js installation and Python with NumPy, SciPy and threadpoolctl:
~~~sh
python3 verify-kissing-nine-gram-cells.py census
python3 verify-kissing-nine-gram-cells.py 7
python3 verify-kissing-nine-gram-cells.py 9
node verify-kissing-127-reciprocal-barrier.js
~~~
Append a class index to the Python 7/9 commands to replay an individual case. The 170 nine-vertex classes can be run in parallel.
