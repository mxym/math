# A near-perfect obtuse matching in the 21-point kissing residual

Suppose 73 kissing points in $\mathbb R^6$ have 26 antipodal pairs, or 127 kissing points in $\mathbb R^7$ have 53 antipodal pairs. Normalize to unit length. **Of the 21 unpaired points, 20 can be matched in ten disjoint pairs whose inner products are all strictly below $-0.540$.** Thus all but one point of the original code can be paired at angular separations greater than $\arccos(-0.540)$ (about $122.68^\circ$). Also, the graph joining residual points at inner product strictly below $-0.522$ is connected.

Here is the stronger matching profile. Each column gives a separate guarantee; the matchings need not be nested.

| Guaranteed number of disjoint residual pairs | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Every selected scalar product is less than | −.657 | −.652 | −.645 | −.638 | −.630 | −.619 | −.608 | −.595 | −.580 | −.540 |

The original axes can be arbitrary. The theorem concerns the first-excess [maximal-pair frontier](KissingNineteenPointEnergy.md), complementary to the [integer embedding](KissingFrontierDiscreteEmbedding.md). It neither assumes nor proves that the 21 residual points contain another exact antipodal pair. It does not settle either unrestricted kissing number.

## 1. An energy budget that holds for every choice of weights

Put $F_{ij}=f(y_i\cdot y_j)$ for the residual points, where $f(t)=t^4-t^2/4$. For **every** residual probability vector $w$,
\[
                    w^TFw\ \ge\ \kappa=3/40 .
\]
Indeed choose one representative per marked axis with unit weight and weight the residual points by $10w_j$. The total weight is $P=p+10$, where $(p,P)=(26,36)$ or $(53,63)$. The weighted quartic energy is at least $f_0P^2$, since the nonconstant spherical harmonic coefficients are nonnegative. Here $f_0=3/(4P)$. Every off-diagonal term involving an axis has $|t|\le1/2$ and hence $f(t)\le0$. Therefore $f_0P^2\le3p/4+100w^TFw$, giving the claim. In particular this applies to probability vectors supported on any subset, even after deleting arbitrary vertices.

We will construct distributions on disconnected parts that violate the budget. Let $G_a$ have the 21 residual vertices and an edge when $t<-a$, with $a\ge1/2$. Across different components of $G_a$ or of $G_a-T$ one has $f(t)\le \delta=f(a)$. Positive cross terms are possible only on edges of the **true-negative graph** $G_{1/2}$. This latter graph is triangle-free: three squared unit lengths and three scalar products strictly below $-1/2$ would give a negative squared norm for the sum.

## 2. Measures on a part and the cost of combining them

For a part of size $k$, we obtain two simultaneous upper bounds $(C,d)$: a probability distribution on the part has self-energy at most $C$, and the mass of its true-negative neighbors of **any external point** is at most $d$.

* If $k=1$, use $(3/4,1)$. For $k=3$, some two vertices are independent in $G_{1/2}$; giving them equal mass gives $(3/8,1)$.
* Otherwise write $b=\lfloor k/2\rfloor$. If the part has an independent set of size $b+1$ in $G_{1/2}$, its uniform measure gives $(3/(4(b+1)),1)$. If not, the uniform measure on the **whole** part gives $(U_k/k,b/k)$, where $U_k$ is a bound for the diagonal-included energy per point on arbitrary $k$ kissing points in dimension at most seven. The second coordinate follows because the true-negative neighbors of any external vertex form an independent set. For $k=2$, $U_2=3/2$ trivially.
* Improve the low-independence $k=5$ case to $(137/500,2/5)$. A triangle-free graph on five vertices with independence number at most two must be a 5-cycle: each degree is at most two, and degree at most one would force three of its nonneighbors to form a triangle. Section 3 proves the energy bound.

For a cut into parts with chosen type $(C_i,d_i)$, take part masses $p_i=C_i^{-1}/Z$, $Z=\sum C_i^{-1}$. The self-energy contribution is at most $1/Z$. For two different parts the probability of a true-negative edge is at most $\min(d_i,d_j)$. Thus the positive cross contribution is at most $\delta D$, where we may take
\[
             D=\min\left\{2\sum_{i<j}p_ip_j\min(d_i,d_j),\ \tfrac12\right\}.
\]
For the second bound, independently draw one vertex from each part. The resulting true-negative graph on parts is triangle-free, and its weighted ordered edge mass is at most $1/2$: move all weight on a nonadjacent pair to the endpoint with larger weighted neighbor sum, without decreasing edge mass, until the support is a clique. With exactly three parts one may further bound $D$ by $2\sum_{i<j}p_ip_j-\min_{i<j}2p_ip_j$, since at least one pair must be absent in each draw. All these upper bounds allow negative cross terms to be discarded. A necessary condition for **every** partition of the indicated kind is
\[
                         1/Z+\delta D\ \ge\ 3/40 .
\]

## 3. Two finite geometric estimates

**Pentagon.** Number the vertices of a true-negative 5-cycle in cycle order, and let $\beta_i$ be the spherical distance from one endpoint to the antipode of the next. Then $0\le\beta_i<\pi/3$, $\beta_i+\beta_{i+1}\ge\pi/3$ because the two outer vertices are distinct kissing points, and $\sum_i\beta_i\ge\pi$ because following an odd cycle with alternating sign connects a point to its antipode. Noncycle pairs contribute nonpositive $f$. The [replay](verify-kissing-frontier-negative-matching.js) proves $\sum_i f(-\cos\beta_i)\le1.539034<1.55$, so uniform self-energy is at most $(5(3/4)+2(1.55))/25=137/500$.

For details, take $M=256$ and $j_i=\lfloor3M\beta_i/\pi\rfloor$. Then $j_i+j_{i+1}\ge M-1$ and $\sum j_i\ge3M-4$. For a bin $j$ use $x=111j/(106M)\le\beta$ (since $\pi>333/106$), so $\cos\beta\le z=1-x^2/2+x^4/24$. As $\cos\beta\ge1/2$, $f(-\cos\beta)\le z^4-z^2/4$. Round each upper cost upward to a multiple of $10^{-6}$. A cyclic dynamic program fixes the largest bin first, adds the remaining four sequentially, and tracks the last bin and the accumulated bin sum capped at $3M-4$. The last–first constraint is tested at the end. This relaxes the continuous problem outward; the returned integer upper sum is 1,539,034.

**Uniform component energies.** The verifier embeds rational [Bachoc–Vallentin](https://arxiv.org/abs/math/0608426) three-point Gram factors for $4\le k\le20$ in dimension seven (and hence every lower dimension). The following are the rounded-up $U_k$ actually used, in units of $10^{-4}$:

| $k$ | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| $10^4U_k$ | 15002 | 15002 | 15003 | 15005 | 15032 | 15073 | 15121 | 15174 | 15231 |

| $k$ | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| $10^4U_k$ | 15293 | 15357 | 15423 | 15492 | 15528 | 15634 | 15709 | 15784 |

Here is the direct local test. With $h$ a nonnegative combination of positive-degree normalized Gegenbauer polynomials and $S$ a symmetric positive three-point kernel as in the [earlier energy derivation](KissingNineteenPointEnergy.md#the-energy-certificate), put $P(t)=f(t)+h(t)+3S(1,t,t)$. On the entire kissing triple Gram domain check
\[
          \tfrac13\{P(a)+P(b)+P(c)\}+(k-2)S(a,b,c)\le B'.
\]
Summing over distinct ordered triples and separating repeated indices in the positive kernel sums gives $E_k\le 3/4+h(1)+S(1,1,1)+(k-1)B'$ for the actual mean ordered energy. We round this rational upper bound upward to obtain the table. Equivalently, the auxiliary univariate polynomial in the split certificate cancels identically when one adds $3(k-2)$ times the triple slack to the three pair slacks. The replay uses exact polynomial arithmetic and outward-rounded tensor Bernstein subdivision. All 17 exact unrounded bounds were also independently reproduced from closed-form Gegenbauer expansions using reversed-coordinate subdivision.

## 4. From components to a matching

If $G_a$ has no matching of $m$ edges, the [Tutte–Berge formula](https://doi.org/10.1017/S0004972700042982) gives a set $T$ for which the number of odd components of $G_a-T$ minus $|T|$ is at least $23-2m$. Indeed the maximum matching then covers at most $2m-2$ of the 21 vertices. Enumerate all integer partitions of $21-|T|$ satisfying that odd-component inequality; $|T|>10$ cannot qualify. For each part allow both alternatives of Section 2, or its single stated type for size one or three. At each displayed rational threshold the upper bound $1/Z+f(a)D$ is **strictly below $3/40$ for every resulting profile**. For the ten-pair row this checks 19,960 profiles. The contradiction proves the matching. For connectivity, any disconnected graph admits a cut into parts of sizes $a',21-a'$ with $1\le a'\le10$ and no crossing edge. All 36 type profiles for those cuts fail the same necessary condition at $a=0.522$.

**Replay:** `node verify-kissing-frontier-negative-matching.js`. No optimizer or external package is needed.