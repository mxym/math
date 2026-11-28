# Odd-component barriers for unrestricted seven-dimensional kissing codes

**Theorem.** In a 60-degree spherical code of the indicated size in real dimension seven, there are at least the following numbers of **disjoint** pairs at angles **strictly greater than 120 degrees**:

| Points | Earlier guarantee | New guarantee | Points left over, at most |
|---:|---:|---:|---:|
| 129 | 58 | **59** | 11 |
| 130 | 59 | **60** | 10 |
| 131 | 60 | **61** | 9 |
| 132 | 61 | **62** | 8 |

The [earlier unrestricted matching bound](KissingUnframedMatchings.md) still gives 57 and 58 pairs for 127 and 128 points. No root frame, symmetry, exact antipodes or harmonic vanishing is assumed. The theorem constrains a putative code; it does not improve the [unrestricted upper bound 132](https://www.mefyi.com/papers/kissing-numbers-five-seven/kissing-numbers-five-seven.pdf), assert the existence of any of these four sizes, or establish that the matching guarantees are sharp.

### 1. A canonical barrier contains only odd factor-critical components

Join two unit vectors if their inner product is strictly less than $-1/2$, obtaining the graph $G$. It is triangle-free by the squared norm of the sum of three vectors. Write $o(G-T)$ for the number of odd components after deleting a set $T$. Choose $T$ to maximize $o(G-T)-|T|$, and then to maximize $|T|$. The Tutte–Berge formula identifies the first maximum with $N-2\nu(G)$, where $\nu$ is the matching number.

There is no even component $C$: deleting any additional vertex of $C$ creates at least one odd component there, without decreasing the deficiency. Every remaining odd component is **factor-critical**, meaning that deleting any one of its vertices leaves a perfect matching. Otherwise take $x$ for which the even graph $C-x$ lacks a perfect matching. Tutte’s theorem supplies a set $S$ there with $o(C-x-S)\ge |S|+2$ (the deficiency has even parity). Adding $x$ and $S$ to $T$ replaces one odd component by at least $|S|+2$, again contradicting maximality of $|T|$. A triangle-free factor-critical component therefore has size one or odd size at least five.

Let $t=|T|$ and $s$ be the number of singleton components. Their negative vectors can all be added to the surviving code: all their products with other survivors have absolute value at most $1/2$, and no negative vector being added is already present. Hence $N-t+s\le132$ by Tomar’s bound. If a matching of size $m$ fails, the remaining $o$ odd components satisfy $o\ge t+N-2m+2$ and $o\equiv N-t\pmod 2$.

### 2. Sign-aware bounds for five and seven points

Use $f(u)=u^4-u^2/4$. Write $C_k$ for any valid upper bound on the minimum of $\sum p_i p_j f(x_i\cdot x_j)$ over probability weights on a $k$-point code. The previous small-component certificate charged **zero** for every nonedge. Keeping information on the signs gives the dimension-free bounds
$$
C_5\le 253/1000,\qquad C_7\le2063/10000.
$$
These bounds concern self-energy only. Because a nonedge of strictly negative energy can help, we **do not** infer that the same constants bound $3\sum p_i^2/4$ for the selected weights. No such assertion is needed at the strict $-1/2$ cutoff.

If the graph has an independent set of size three or four, respectively, uniform mass there suffices. The other cases are the five-cycle and nine isomorphism classes on seven vertices: the [small-component checker](verify-kissing-odd-component-capacities.js) generates the latter from all labelled edge masks. For five vertices, triangle-freeness and independence number at most two force every degree to be two (apply triangle-freeness also to the complement). The incident-edge inequalities, cycle inequalities and stabilizer ordering used by the checker are justified in the [previous small-component proof](KissingUnframedMatchings.md#2-a-small-component-certificate).

Here is the extra local constraint. For an edge $e$ write $s_e=-x_i\cdot x_j$. Moving along a path while reversing sign at each step gives
$$
 d(x_i,(-1)^m x_j)\le\sum_{e\text{ on the path}}\arccos s_e,
$$
where $m$ is its length. Thus an even path bounds the inner product below and an odd path bounds it above. Enumerate simple paths of each parity between the ends of every nonedge, retain the shortest upper angular length for each parity, and intersect the resulting bounds with $[-1/2,1/2]$. Missing paths need not contribute a bound. If the resulting interval $[L,U]$ is empty, reject the box. Otherwise the maximum of $f$ on that interval is at an endpoint or at zero; include zero only if it belongs to the interval.

In detail, the normalized upper angle bins are $j/1024$ in units of $\pi/3$. An upper cosine Taylor polynomial through degree eight is used at $(111/106)j/1024$, which is less than $(\pi/3)j/1024$ for $j>0$. The last bin is valid without a Taylor test since $s_e\ge1/2$. For a sum of bins $v$, use the outward angle $x=(22/21)v/1024$, replacing its cosine lower bound by $-1$ if $x\ge333/106$. Otherwise the degree-ten alternating cosine polynomial is a lower bound. All polynomial-to-grid bounds are evaluated with integer arithmetic and rounded outward. This applies on the entire continuous edge box, not just on its grid corners.

The checker uses nonnegative integer masses totaling 160, bounds all matrix entries from above, and closes a box only if its resulting quadratic cost, after normalization, is at most the target. Iterative weight changes and the choice of which edge to split only select witnesses and search order. Open cells and resource limits cause failure. Shared split endpoints are included in both children.

### 3. The seven-dimensional energy budget

In dimension seven the constant normalized Gegenbauer coefficient of $f$ is $1/84$ and its remaining coefficients are nonnegative. The addition formula yields weighted energy at least $1/84$ for **every** probability measure. Between distinct components of $G-T$ we have $|x\cdot y|\le1/2$, so cross-energies are nonpositive. Giving components masses proportional to $1/C_k$ therefore forces $\sum_C 1/C_{|C|}\le84$.

For larger odd components the uniform measure has energy at most $U_k/k$, where $U_k$ bounds the ordered sum of $f$, including the diagonal, divided by $k$. The [energy/barrier checker](verify-kissing-odd-component-barrier.js) gives 14 additional rational three-point certificates at sizes $23,25,31,35,37,39,41,43,45,57,65,71,75,77$. They use the positive [Bachoc–Vallentin kernels](https://arxiv.org/abs/math/0608426) in the [direct triple inequality](KissingFrontierNegativeMatching.md#3-two-finite-geometric-estimates); integer Gram factors guarantee positivity and outward tensor Bernstein subdivision checks the polynomial inequality throughout the Gram-feasible cube. The replay checks the exact rational upper values before rounding them **up** to millionths. Uniform bounds at $q\le k$ are transported by averaging over all $q$-subsets:
$$
U_k\le3/4+\frac{k-1}{q-1}(U_q-3/4).
$$
The certified constants and two univariate bounds inherited from the [fixed earlier verifier](https://github.com/mxym/math/blob/dd7318679685df9b81e045992225c4fe230d765b/research/euclidean-tensor-geometry/verify-kissing-unframed-matchings.js) are unchanged.

Finally set $w_k=\lfloor10^6/C_k\rfloor$, taking the strongest available lower bound on this reciprocal. For nonsingletons use $D(0,0)=0$, absent states infinite, and append a part of odd size $k\ge5$ to a state $(j-k,b-1)$ at cost $w_k$. For all admissible $t,o,s$ from §1 minimize $sw_1+D(N-t-s,o-s)$; take $m=N-70$. The four minima are **84,402,559; 84,294,408; 84,105,271; 84,006,059** in increasing order of $N$. Each is strictly greater than $84,000,000$. This violates the energy budget for every putative deficient barrier and proves all four rows.

**Replay (standard Node.js):**
```sh
node verify-kissing-odd-component-capacities.js
node verify-kissing-odd-component-barrier.js
```
The small-component replay can also be split with arguments `5` or `7 j` for an individual seven-vertex graph index $0\le j\le8$. The inherited inputs can be rechecked with the earlier linked replays.
