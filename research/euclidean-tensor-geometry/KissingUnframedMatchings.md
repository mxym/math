# Unframed matchings in six- and seven-dimensional kissing codes

**Any** 73-point kissing configuration in $\mathbb R^6$ has **33 disjoint pairs** at angles strictly greater than $120^\circ$. Any 127-point configuration in $\mathbb R^7$ has **57**. No exact antipodes, prescribed roots, angles within a root system, lattice, or symmetry are assumed. Neither result asserts that these hypothetical configurations exist, or that any of the forced pairs are exact antipodes.

The table covers every size above the root examples through [Tomar's unrestricted upper bounds](https://www.mefyi.com/papers/kissing-numbers-five-seven/). Join two unit vectors if their scalar product is $<-1/2$. A **nonhalf component** below means a connected component in which no independent set contains at least half the vertices.

| Dimension | Number of points | Guaranteed size of matching | Some nonhalf component has at least |
|---:|---:|---:|---:|
| 6 | 73 | **33** | 12 vertices |
| 6 | 74 | 34 | 16 |
| 6 | 75 | 35 | 19 |
| 6 | 76 | **36** | 21 |
| 7 | 127 | **57** | 11 |
| 7 | 128 | 58 | 13 |
| 7 | 129 | 58 | 15 |
| 7 | 130 | 59 | 16 |
| 7 | 131 | 60 | 19 |
| 7 | 132 | **61** | 20 |

There are also matchings at stronger angles, **without** the exact-antipode assumption of the [21-point frontier theorem](KissingFrontierNegativeMatching.md). Each entry is a separate matching all of whose products are strictly less than $-a$. The matchings need not be nested.

| $a$ | .501 | .510 | .520 | .530 | .540 | .550 | .560 | .580 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 73 points in dimension six | 33 | 31 | 28 | 25 | 22 | 18 | 15 | 6 |
| 127 points in dimension seven | 55 | 49 | 42 | 35 | 26 | 17 | 7 | – |

## 1. A budget on the components of a cut

Use $f(t)=t^4-t^2/4$ and $F_{ij}=f(x_i\cdot x_j)$. In dimensions $n=6,7$ put $P=36,63$ respectively. The constant Gegenbauer coefficient is $3/[n(n+2)]-1/(4n)=3/(4P)$, and both nonconstant coefficients are nonnegative (the degree-two coefficient has the sign of $6/(n+4)-1/4$). Hence for every probability vector $w$, including ones supported on a proper subset,
\[
                        w^t Fw\ge\kappa=\frac3{4P}.
\]
This uses positive-definiteness of the spherical harmonics, not antipodal representatives.

For each component of size $k$ of the graph $G_a-T$, with edges $x_i\cdot x_j<-a$, we construct a probability measure of self-energy at most $C_k$ with squared Euclidean mass norm at most $4C_k/3$. Give the components masses $p_i=C_{k_i}^{-1}/Z$ where $Z=\sum_i1/C_{k_i}$. The total self-contribution is at most $1/Z$ and the combined squared mass norm is at most $4/(3Z)$.

Only edges of the true-negative graph $G_{1/2}$ can have positive cross-energy, and their cross-energy per unit ordered mass is at most $\delta=f(a)$. This true-negative graph is triangle-free: three such vectors would have a negative squared sum. The cross-edge ordered weight is at most $1/2$ by the weighted triangle-free bound (move mass between two nonadjacent vertices toward the one with larger weighted neighborhood until the support is a clique). It is also at most $d\sum_j w_j^2$, by $2w_iw_j\le w_i^2+w_j^2$, if the maximum degree is $d$.

We may use $d=22$ in six dimensions and $34$ in seven. Project the true-negative neighbors into the hyperplane perpendicular to the central vertex and normalize; their mutual products are at most $(1/2-st)/\sqrt{(1-s^2)(1-t^2)}\le1/3$ when $s,t\ge1/2$ are their heights with respect to the opposite center. The expression decreases in either variable. An exact antipode is the only neighbor if present, so the degenerate projection causes no problem. Apply [Tomar's dimension-five and dimension-six $1/3$-code bounds](https://www.mefyi.com/papers/kissing-numbers-five-seven/). Every cut therefore satisfies
\[
                 \kappa\le\frac1Z+\delta\min\left(\frac12,\frac{4d}{3Z}\right).
\tag{1}
\]
At $a=1/2$ the entire cross term vanishes. We use **lower** rounded reciprocals in the right side, which only weakens the test.

## 2. A small-component certificate

On any independent set of size $r$ in $G_{1/2}$ the uniform measure has both self-energy and $3/4$ times squared norm at most $3/(4r)$. Triangle-freeness suffices to obtain independent sets of sizes $1,1,2,2,3$ on $1,2,3,4,6$ points respectively; the last assertion is the elementary $R(3,3)=6$. We also prove the following **dimension-free** bounds:
\[
                              C_5\le .260,\qquad C_7\le .209 .
\]
These are bounds on the best measure, **not** necessarily on the uniform measure. If the independence number is at least $3$ or $4$, respectively, the independent-set bound suffices. Otherwise the five-point graph is a pentagon; on seven points there are just nine possible unlabelled triangle-free graphs of independence number at most three. The [small-component replay](verify-kissing-unframed-component-costs.js) generates these from all $2^{21}$ edge masks, up to permutations, rather than assuming a list.

For completeness, here is the full interval procedure for each graph. On each edge put $s=-x_i\cdot x_j\in[1/2,1]$. Nonedges have $f\le0$ and are charged **zero**. Treat the $s$'s as independent until a necessary geometric condition eliminates a box.

* For incident edges with lower endpoints $l_i$, indexed by a subset of size $b$, put $L=\sum l_i$. If $(b+1)\min l_i\ge L$, feasibility implies $2((b+1)\sum l_i^2-L^2)\le b+1$. Indeed apply Cauchy–Schwarz to a nonnegative weighted sum of neighbors, whose squared norm is at most $((\sum v_i)^2+\sum v_i^2)/2$, and choose $v_i=l_i-L/(b+1)$.
* Around any odd cycle, $\sum\arccos s_i\ge\pi$: alternate signs along the cycle and use the triangle inequality between a point and its antipode. Upper angle bins, obtained using $\pi>333/106$ and the degree-eight alternating cosine upper polynomial, give an outward test.
* On cycles of lengths $4,5,6,7$ the verifier respectively uses $\sum s_i\le 3,4.046,5.001,5.923$. For four, bound $\langle x_0+x_2,x_1+x_3\rangle$ by Cauchy–Schwarz. For five, use the cycle's least adjacency eigenvalue $-2\cos(\pi/5)$. For six and seven let $c_j$ be the mean lag-$j$ product. Fourier decomposition of each coordinate on the cycle makes $c_j$ the average of $T_j(t)$ for a probability distribution on $t=\cos(2\pi i/\ell)$; also $c_2\le1/2$. For six use $2/3+t+T_2(t)/3\ge0$ on that support. For seven let $u,v$ be its two smallest distinct elements. Then $(t-u)(t-v)\ge0$ there, so $-c_1\le(3/4+uv)/(-u-v)<5923/7000$. The program checks rational isolating brackets for $u,v$.

The verifier splits edge boxes at integer multiples of $1/1024$. It propagates upper endpoints outward using the necessary lower-endpoint tests and orders some equivalent edges using the stabilizer of previously fixed edge labels. This loses no orbit: successively move a largest remaining value within its current orbit to the designated position, then fix that label. On each surviving box use upper edge costs $f(-s)$ at its upper endpoints, rounded **up** in millionths, and diagonal $3/4$. The program searches for nonnegative **integer** vertex weights summing to $160$ and accepts a box only when their explicitly evaluated quadratic cost, after normalization, is at most the claimed $C_k$. A heuristic chooses weights and branch order only; failure to certify or a depth/cell limit does not count as acceptance. Since this cost has no negative entries, it also bounds $3/4$ times the squared mass norm. All inequalities controlling acceptance or rejection use exact integer comparisons.

## 3. Larger parts and exact barrier enumeration

For arbitrary $k$ points the uniform measure has $C_k\le U_k/k$, with $U_k$ an upper bound for the mean ordered energy including the diagonal. We use the [published $4$–$20$ table](KissingFrontierNegativeMatching.md) and [four larger published bounds](KissingHigherCardinalityEnergy.md). The [new energy and barrier replay](verify-kissing-unframed-matchings.js) checks two univariate Gegenbauer majorants and nine further rational [Bachoc–Vallentin](https://arxiv.org/abs/math/0608426) three-point charts throughout the Gram-feasible continuum. They use the direct triple inequality in the [energy derivation](KissingFrontierNegativeMatching.md#3-two-finite-geometric-estimates), with rational positive kernel factors and outward dyadic Bernstein subdivision, not sampled grid values. A bound at $s\le k$ gives $U_k\le3/4+(k-1)(U_s-3/4)/(s-1)$ by averaging over the $s$-subsets. Each of the uniform bounds actually selected is at least $3/4$, as the squared-norm requirement needs.

If $G_a$ has no matching of size $m$, Tutte–Berge gives a deletion set $T$ of size $t$ leaving at least $t+N-2m+2$ odd components. Choose $T$ of largest cardinality among the sets maximizing the deficiency (odd-component count minus deletion count). There is then **no three-vertex component**: it could only be a three-vertex path, and deleting its center creates two singleton components, leaves the deficiency unchanged, and enlarges $T$.

At $a=1/2$ we have one more restriction. If $s$ singleton components remain, add their negatives to the surviving code. These are new distinct points; each old singleton has all other retained products in $[-1/2,1/2]$. The enlarged code has $N-t+s$ points, so $s\le t+\tau-N$ for $\tau=76,132$. We **do not** apply this repair at larger thresholds.

In units of $10^{-6}$ let $w_k=\lfloor 10^6/C_k\rfloor$. The dynamic program minimizes $\sum w_{k_i}$ over component sizes summing to $N-t$ with the required odd count and allowed number of singletons. For nonsingletons, start $D(0,0)=0$; appending a part $k\ne1,3$ adds $w_k$ and changes the state by $(k,k\bmod2)$. Add the singleton costs separately. Test (1) for the resulting lower bound on $Z$. Every putative barrier in the tables violates (1), proving the matchings.

For the last column suppose every component larger than $K$ has an independent half. At $T=\varnothing$ and $a=1/2$ assign these components the stronger reciprocal bound $4\lceil k/2\rceil/3$, and minimize the total over all integer partitions of $N$. The minimum is strictly greater than $4P/3$ for $K$ one less than the tabulated number, again contradicting (1).

There is also a useful interpretation at first excess: all components with an independent half can be replaced *simultaneously* by the chosen independent vertices and their negatives, without decreasing the code size. Products between different original components have absolute value at most $1/2$. The resulting code retains at least one antipodal pair per two replaced vertices. The [unframed upper bounds of 26 and 53 exact pairs](KissingNineteenPointEnergy.md) thus imply that in the original 73- or 127-point configuration **at least 21 vertices** must lie in nonhalf components. When applying a bound to a larger resulting code one may take a first-excess subset preserving any forbidden number of pairs.

**Reproduce:** run `node verify-kissing-unframed-component-costs.js` and `node verify-kissing-unframed-matchings.js`. To recheck the inherited uniform constants as well, run the two predecessor scripts linked from their tables. The new matchings constrain the structure of a counterexample; neither the current unrestricted upper bounds nor the root-system lower constructions are changed.
