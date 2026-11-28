# A coupled harmonic obstruction: 61 disjoint obtuse pairs at 130 points

**Theorem.** Every set of 130 unit vectors in $\mathbb R^7$, with scalar products at most $1/2$ between distinct vectors, contains **61 pairwise disjoint pairs** with scalar product **strictly below $-1/2$**. At most eight points are left unmatched. The previous guarantee at 130 was 60; neither exact antipodes nor any symmetry are assumed. This does not decide whether 130 points are attainable, or lower [Tomar's unrestricted kissing-number bound of 132](https://www.mefyi.com/papers/kissing-numbers-five-seven/).

The new step is a **joint** obstruction for the components of a graph, not a claim that one stronger scalar charge excludes every partition. With the local inputs below, nine partitions pass the scalar test. All nine violate a positive-semidefinite, component-labeled harmonic inequality. Five reusable lists of positive Gram factors suffice for those nine cases.

## 1. Local input and the seven-point extremal graph

For $f(t)=t^4-t^2/4$ let $C(X)=\min_{p\ge0,\sum p_i=1}\sum_{ij}p_ip_jf(x_i\cdot x_j)$. The strong graph joins pairs with product $<-1/2$. In **arbitrary dimension**, the supremum over seven-point $60^\circ$ codes lies in
\[
 [\,0.200850277798\ldots,\;0.2015\,].
\]
The left endpoint is the exact algebraic number in the [sharp transitive heptagon theorem](https://github.com/mxym/math/blob/4f75d746375dfefc460c3bc2b69f5065d8e6bb09/research/euclidean-tensor-geometry/KissingSharpHeptagonalCapacity.md). Moreover **every** unrestricted seven-point maximizer has strong graph exactly $C_7$. This is not an assertion that it is vertex-transitive. Existence of a maximizer follows from compactness of the $7\times7$ feasible Gram matrices and continuity of the minimum over a compact mass simplex.

Indeed, an independent four-set gives $C\le3/16$. Among the nine remaining triangle-free graph types in the [previous census](https://github.com/mxym/math/blob/1a6fdc1dc8d4a4a1df7aef313b34e9c21b472400/research/euclidean-tensor-geometry/KissingNinePointCapacityAnd127Matching.md), eight have $C\le0.20084$, strictly below the witness. The remaining representative (index four, cycle order $0,5,2,3,4,1,6$) has $C\le0.2015$. The [continuous Gram verifier](verify-kissing-seven-heptagon-boxes.py) gives both exclusions and independently replays the seven-vertex census. The $C_7$ tree used 10,175 boxes, including 5,088 integer dual leaves.

The verifier improves the earlier affine upper bound for weak Gram entries. For an endpoint numerator $z$ over $K=4096$ and candidate integer slope $S$, write $P(z)=4z^4-K^2z^2-Sz$. Divide the closed interval into four covering subintervals. On $[a,b]$ with $h=b-a$, its degree-four Bernstein coefficients, multiplied by twelve, are
\[
 12P(a),\quad12P(a)+3hP'(a),\quad
 12P(a)+6hP'(a)+h^2P''(a),\quad
 12P(b)-3hP'(b),\quad12P(b).
\]
Their largest value over all four intervals, divided by twelve and rounded up to an integer $B$, ensures $f(z/K)\le (Sz+B)/(4K^4)$ for every **real** $z$ in the box. Select the best midpoint bound among such lines, the exact convex secant where applicable, and the prior constant bound. All interval multiplications fit signed 64-bit arithmetic ($|a|,|b|,h\le4096$ on the edge or nonedge boxes); the final LP-dual certification remains arbitrary-precision integer arithmetic. Floating-point searches cannot accept a leaf.

For five and nine points use the [fixed bounds .252 and .163](https://github.com/mxym/math/blob/4f75d746375dfefc460c3bc2b69f5065d8e6bb09/research/euclidean-tensor-geometry/KissingRefinedOddCapacitiesAndMatching.md). For larger odd sizes use uniform weights. The [input checker](verify-kissing-component-harmonic-inputs.js) certifies 18 additional or improved three-point uniform-energy charts ($q=11,13,25,27,29,33,35,37,43,45,47,59,63,81,83,93,95,97$) using positive [Bachoc–Vallentin kernels](https://arxiv.org/abs/math/0608426) and exact outward Bernstein subdivision. It recomputes all the lower-rounded reciprocal charges $w_k$ in the [proof data](kissing-component-harmonic-data.json), from these charts and the explicitly pinned predecessors. Thus each component of size $k$ admits a probability measure with energy at most $c_k=10^6/w_k$. For $k\ge11$ this measure is explicitly uniform; for $k=5,7,9$ take an optimizing measure.

## 2. A component-measure certificate

Suppose the code is partitioned into disjoint groups such that **between different groups** every product belongs to $[-1/2,1/2]$. Let $\mu_i$ be the above probability measure on group $i$ of size $k_i$. For every degree $\ell\ge1$, the matrix
\[
 H^{(\ell)}_{ij}=\iint P_\ell(x\cdot y)\,d\mu_i(x)d\mu_j(y)
\]
is positive semidefinite by the spherical-harmonic addition formula, with $P_\ell$ the normalized Gegenbauer polynomial in dimension seven. Consequently a collection of PSD coefficient matrices $A^{(\ell)}$ gives
\[
 0\le\sum_{i,j}\iint F_{ij}(x\cdot y)\,d\mu_i d\mu_j,\qquad
 F_{ij}(t)=\sum_{\ell\ge1}A^{(\ell)}_{ij}P_\ell(t).
\]
The same conclusion holds after simultaneously multiplying each coefficient row and column for group $i$ by $s_i\ge0$. These are bounds on actual component measures, not additional moment assumptions.

For $i\ne j$, take an upper bound on $F_{ij}$ over $[-1/2,1/2]$. On group $i$ choose $\lambda_i\ge0$, let $b_i$ bound $F_{ii}-\lambda_i f$ on $[-1,1/2]$, and put $a_i=F_{ii}(1)-3\lambda_i/4$. If $d_i=\sum_x\mu_i(x)^2$, then
\[
 \iint F_{ii}\,d\mu_i d\mu_i
 \le\lambda_i c_{k_i}+(1-d_i)b_i+d_i a_i.
\]
Uniform weights give $d_i=1/k_i$. Otherwise $1/k_i\le d_i\le\min(1,(64c_{k_i}+1)/49)$: off the diagonal $f\ge-1/64$, so the energy is at least $(49d_i-1)/64$. Maximize the displayed affine expression at the two endpoints. On a singleton only $a_i$ matters.

For compactness the [data](kissing-component-harmonic-data.json) organize equally sized groups into types. In each degree the coefficient between labels is the inner product of two rational factor rows, plus, for labels of the same type occurring $r$ times, a nonnegative rational multiple of $\mathbf1_{i=j}-1/r$. This last matrix is an orthogonal projection. A type may select **any** stored factor row; even repeated choices preserve positivity. Integer rescalings $s_i$ are given for each shape. Summing the just-described upper bounds with the exact group multiplicities produces a strictly negative rational for every residual partition.

The [standard-library verifier](verify-kissing-component-measure.py) proves all scalar interval bounds by exact Bernstein conversion and dyadic de Casteljau subdivision. It keeps an upper bound for the largest coefficient of every live interval and a lower bound from sampled endpoints. The stopping tolerance only determines when to return the rigorous **upper** bound; acceptance always uses a strict rational sign. No numerical SDP solver or trusted floating-point objective is needed to replay.

## 3. Exhausting the partitions

Suppose the strong-graph matching number is at most 60. By the [canonical Tutte–Berge barrier lemma](https://github.com/mxym/math/blob/c36c642c5f6984e670f9ba2368f4bfafb5b966d7/research/euclidean-tensor-geometry/KissingOddComponentBarriers.md) there is a set of $t$ deleted vertices leaving only odd factor-critical components, with number $o\ge t+10$ and $o\equiv130-t\pmod2$. If $s$ components are singletons, adding their antipodes after the deletion gives $s\le t+2$. The other components have odd size at least five by triangle-freeness. Their intercomponent products satisfy the two-sided bound required above.

The elementary scalar obstruction is $\sum_i w_{k_i}\le84{,}000{,}000$: $f$ has dimension-seven constant harmonic coefficient $1/84$ and positive nonconstant coefficients, and the cross-component costs are nonpositive, so inverse-cost weighting gives this necessary inequality. The verifier enumerates every partition meeting this integer budget by dynamic programming and bounded backtracking, without rounding adverse to an actual code. Exactly **nine** possibilities remain; each has $(t,o,s)=(0,10,2)$. The least charge is **83,981,304**, so the scalar shortcut provably does not finish this particular input table. The joint certificates exclude all nine. This proves the theorem, not sharpness of 61 or the cardinality of a largest seven-dimensional kissing configuration.

**Replay:** with the manuscript, companion programs and data in one directory:
~~~sh
python3 verify-kissing-seven-heptagon-boxes.py census
python3 verify-kissing-seven-heptagon-boxes.py
node verify-kissing-component-harmonic-inputs.js
python3 verify-kissing-component-measure.py
~~~
Only the Gram-cell program needs NumPy, SciPy and threadpoolctl. An optional class number replays a single seven-vertex graph.
