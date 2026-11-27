# Seven-dimensional kissing codes with irreducible symmetry: the sharp bound is 126

**Theorem.** Let $C$ be a finite subset of the unit sphere in $\mathbb R^7$ with $\langle x,y\rangle\le 1/2$ for distinct points. If a finite group of orthogonal transformations preserving $C$ acts irreducibly on $\mathbb R^7$, then $|C|\le126$. The normalized $E_7$ roots attain 126, so this bound is sharp. No transitivity on the points, antipodality, prescribed root frame or prescribed group order is assumed. Equivalently, the full symmetry group of any seven-dimensional kissing code with more than 126 points must preserve a nonzero proper linear subspace. A nonspanning code already preserves its span; a spanning finite code has finite symmetry group.

This settles the optimum **within this symmetry class**, not the unrestricted seven-dimensional kissing number. It does not assert uniqueness of equality throughout the larger class. [Cohn–Jiao–Kumar–Torquato](https://msp.org/gt/2011/15-4/gt-v15-n4-p11-p.pdf) describe inequivalent 126-point kissing codes. The ingredients already established in the repository are the [primitive and order-divisible-by-nine cases](KissingSevenManyOrbits.md), including an upper bound for the imprimitive $\mathrm{PSL}_2(7)$ case, and the [finite-orbit reduction](KissingSevenTransitiveUniqueness.md). The new step is a proof for the affine group of order 56, including **two arbitrary free orbits**. We use the [unrestricted upper bound 132](https://www.mefyi.com/papers/kissing-numbers-five-seven/kissing-numbers-five-seven.pdf) and [Anstreicher's antipodal bound](https://optimization-online.org/wp-content/uploads/2001/01/248.pdf).

## 1. The one remaining subgroup

We may exclude $-I\in G$ and take the absolutely irreducible complexification imprimitive. It has seven line blocks. The action on these lines has a diagonal kernel $B$, either scalar or a binary sign code on real orthogonal coordinate lines: this is the equal-weight/conjugation argument in the finite-orbit reduction. A nontrivial scalar kernel contains $-I$. If $B=1$, the image is one of the [seven transitive permutation groups of degree seven](https://pari.math.u-bordeaux.fr/dochtml/html-stable/General_number_fields.html). For $C_7:H$ with $H\le C_6$, any character of the line stabilizer $H$ extends to the group via the quotient. The same holds for both $A_7$ and $S_7$ (stabilizers $A_6,S_6$). The induced line representation would be a twist of the reducible permutation representation. The remaining group $\mathrm{PSL}_2(7)$ already has the needed bound in the cited proof, without point transitivity.

Suppose $B$ is nonscalar. The permutation image contains a 7-cycle, lifted to an element of order seven since the kernel is a 2-group. In a real orthonormal line basis the signs around its cycle multiply to $+1$ and can be removed by basis sign changes. The sign kernel is an invariant submodule of the binary cyclic permutation module of length seven. The factorization
\[
 X^7-1=(X+1)(X^3+X+1)(X^3+X^2+1)\quad\text{over }\mathbb F_2
\]
has distinct factors. Thus $B$ contains a three-dimensional irreducible summand $E$ (the one-dimensional summand is the scalar code). The seven coordinate characters on $E$ are all nonzero and distinct: the 7-cycle permutes them transitively, and an invariant common character or all trivial characters cannot give a faithful three-dimensional sign module. We may retain just $H=E:C_7$. All such actions have the same coordinate model: label coordinates by the seven nonzero elements of $\mathbb F_2^3$, on which a Singer cycle acts regularly. The two possible cubic factors interchange by reversing the generator; more generally we are free to choose a generator of the same order-seven cyclic group.

Use field coordinates $\mathbb F_8=\mathbb F_2[z]/(z^3+z+1)$, label the indices $0,\ldots,6$ by the binary coefficient vectors of $1,z,\ldots,z^6$ (integers $A=(1,2,4,3,6,7,5)$), and put $w_{s,i}=(-1)^{s\cdot A_i}$, the binary dot product. The action consists of these eight diagonal sign changes and the cyclic rotations of the seven coordinates. Its two 8-point orbits are the opposite simplices with rows $\pm w_s/\sqrt7$.

Indeed, a stabilizer containing an element of order seven is either a Sylow 7-subgroup or the whole group: its intersection with $E$ is invariant under that irreducible multiplier. The Sylow group's fixed space is a line; its conjugates have exactly the simplex rows as unit vectors with their two orientations. If seven does not divide its order, a stabilizer lies inside $E$. Order eight fixes no point. Order four fixes a single coordinate line, producing just one 14-point orbit, the axes with both signs. The remaining possible orbit sizes are 28 and 56. Consequently in $127,\ldots,132$ the sole possible total is **128**, consisting of both 8-orbits and a remaining 112 points, partitioned as $28+28+28+28$, $28+28+56$, or $56+56$.

A 28-orbit cannot occur here. Its seed is fixed by a nonidentity sign change, so it is supported in a three-coordinate Fano line (the nonzero kernel of a binary linear functional, viewed as a set of coordinate labels). At least two coordinates are nonzero, or it would be on an axis. The restricted $E$ signs include the three flips of any two of these coordinates; each gives a distinct point from the seed. Thus every squared coordinate is at most $3/4$. The restrictions of $\pm w_s$ include **all** eight signs on this triple. Compatibility with the two simplices would imply $\|x\|_1\le\sqrt7/2$, whereas the minimum with squared norm one and entries squared at most $3/4$ is $(1+\sqrt3)/2>\sqrt7/2$. The minimum follows by concentrating squared mass into the largest coordinates, using concavity of square root. It remains to exclude two free orbits.

## 2. A positive-kernel certificate distinguishing the two orbits

Write $Y=Hx\cup Hy$ for the residual 112 points, $M=112$, and $v_s=w_s/\sqrt7$. Use normalized spherical Gegenbauer polynomials in dimension seven: $P_0=1,P_1=t$ and $(k+5)P_{k+1}=(2k+5)tP_k-kP_{k-1}$. Their kernels are positive semidefinite on the sphere by the addition formula ([Delsarte–Goethals–Seidel](https://doi.org/10.1007/BF03187604)). Let $f$ be the unique positive multiple of
\[
 (t-\tfrac12)(t+\tfrac{127}{200})^2(t+\tfrac1{10})^2(t+\tfrac{327}{100})
\]
whose $P_0$ coefficient is 1; write $f=\sum_{k=0}^6 a_kP_k$. Its coefficients are all positive and the multiple is greater than 22 (exact arithmetic below). In particular $f(t)\le0$ on $[-1,1/2]$.

Define $p_k(x)=\tfrac18\sum_s P_k(x\cdot v_s)$ and $c_k=\tfrac1{64}\sum_{s,r}P_k(v_s\cdot v_r)=(1+7P_k(1/7))/8$ for even $k$. Use $\beta_4=-1/4$, $\beta_6=1/12$, all other $\beta_k=0$. For $k>0$, positivity applied to the signed combination of the uniform measure on $Y$ minus $\beta_k$ times that on the eight simplex rows gives
\[
 \frac{1}{M^2}\sum_{u,v\in Y}P_k(u\cdot v)
 \ \ge\ 2\beta_k\frac1M\sum_{u\in Y}p_k(u)-\beta_k^2c_k .
\]
For odd $k$ the last term is zero and no value of $c_k$ is needed. Conversely, between the two free orbits all $f(u\cdot v)\le0$, while the within-orbit contribution per representative $u$ is exactly $\sum_{g\in H}f(u\cdot gu)$, including $f(1)$ once. Combining the inequalities proves $\sum_{u\in Y}D(u)\le0$, where
\[
 D(u)=M\!\left[1+\sum_{k=4,6}a_k(2\beta_k p_k(u)-\beta_k^2c_k)\right]
       -\sum_{g\in H} f(u\cdot gu).
\]
Thus it suffices to prove **a one-seed inequality** $D(u)>0$ for every free seed compatible with itself and the two simplices. We never discretize the unknown relative orientation of two seeds.

Put $q_s=(u\cdot v_s)^2$; write $\mathbb E$ for average over $s$. Then $0\le q_s\le1/4$ and $\mathbb E q_s=1/7$ by column orthogonality of the sign matrix. The constant $M(1-a_4c_4/16-a_6c_6/144)-f(1)>-94$. The polynomial
\[
 h(q)=-56a_4P_4(\sqrt q)+(56/3)a_6P_6(\sqrt q)
\]
has successive coefficients strictly greater than $-160,2911,-5580,419$. Cauchy gives $\mathbb E q^3\ge7(\mathbb E q^2)^2$; the tangent bound $t^2\ge 2(3/100)t-(3/100)^2$ then gives
$\mathbb E h(q)\ge -163+2911/7-5405\mathbb E q^2$. In particular it suffices to verify
\[
 \boxed{\quad 1112/7-5405\mathbb E q_s^2
        +\sum_{1\ne g\in H}[-f(u\cdot gu)]>0.\quad}
\]

## 3. Compact domains and exact finite replay

For any nonidentity $E$ sign flip, the squared mass on its four changed coordinates is at least $1/4$ (a free seed and its image are distinct). For each $i$, summing the three such inequalities whose changed coordinates omit $i$ counts each of the six other coordinates twice; hence $u_i^2\le5/8$. Consequently $\|u\|_1\ge\sqrt{5/8}+\sqrt{3/8}>\sqrt7/2$. The signs of $u$ (zeros assigned either sign) cannot therefore be any of the 16 words $\pm w_s$, by the two-simplex cap. These words are a length-seven perfect radius-one binary code: two differ in at least three positions, and $16(1+7)=128$. Any sign vector of a feasible seed differs in one position from one of them. By an $E$ sign change, possibly overall negation, and a rotation, we need only the orthant $u=(-b_0,b_1,\ldots,b_6)$ with all $b_i\ge0$. Overall negation need not preserve $C$: it does preserve all of the **one-seed** conditions and $D$. Frobenius doubling of the index modulo seven preserves this orthant, both simplices, and normalizes $H$. We can take the largest $b_i$ to have index $0,1$ or $3$, the representatives of its three index orbits.

The [integer box checker](verify-kissing-seven-irreducible.js) covers those three charts. Endpoints of $b_i$ intervals are in units of $1/S$. Contract by $\sum b_i^2=1$, the four-coordinate mass inequalities, the largest-coordinate inequality and the signed linear simplex bounds $|\sum_i w_{s,i}u_i|\le\sqrt7/2$, always rounding outward. The latter yield $a_s/R\le q_s\le b_s'/R$ by sign-aware squaring and clamping to $[0,1/4]$. On this interval $(Rq_s)^2\le(a_s+b_s')Rq_s-a_sb_s'$. To maximize the sum of the eight secants subject to $\sum Rq_s=8R/7$, start at the lower endpoints and assign remaining mass in decreasing order of slope. This gives an integer upper bound $U$ for $R^2\sum_s q_s^2$.

The self products $t_g=u\cdot gu$ are bounded by direct signed interval products; for diagonal sign changes both complementary squared masses are used. A lower endpoint above $1/2$ excludes the box. Otherwise intersect with $[-1,1/2]$. Only 31 nonidentity self products are needed (7 involutions and 24 inverse pairs). For a bin $[a,b]$ of width $1/B$, the checker rounds down the following lower bound for $256[-f(t)]$ throughout it:
\[
 256\cdot22(1/2-b)(a+13/4)\,
  \operatorname{dist}(-127/200,[a,b])^2
  \operatorname{dist}(-1/10,[a,b])^2 .
\]
Take the minimum for all bins touched, restoring multiplicities. Every term is nonnegative, so early exit at a sufficient partial sum is safe. If their integer sum is $J$, the displayed boxed inequality is certified by $1112\cdot8R^2\cdot256-7\cdot5405\cdot256\,U+7\cdot8R^2 J>0$. If a box is not certified, split its longest non-pivot interval at an integer midpoint, including that midpoint in both children. No unresolved box remains.

| grid $(S,R,B)$ | largest index 0 | largest index 1 | largest index 3 | max depths |
|---|---:|---:|---:|---|
| $(8192,7168,1024)$ | 4,353,683 | 676,215 | 632,867 | 36,35,33 |
| $(16384,10752,768)$, reversed tie order | 4,345,345 | 702,363 | 670,683 | 36,35,34 |

The bins are precomputed by exact arbitrary-precision integer division. Box calculations use exact-integer-sized operands below $2^{53}$; all nonintegral quotients before floor/ceiling are dyadic ($S$ is a power of two and $R$ a multiple of seven). An initial floating square root merely proposes an integer corrected by squared comparisons. For instance $U\le R^2/2$, and $J$ is at most 55 times the largest tabulated bin bound. The checker asserts the full cross products at these maxima are safe integers. Neither optimizer output nor a floating polynomial sign determines a leaf.

Run with Node.js and ordinary Python, from this directory:

~~~sh
python3 verify-kissing-seven-irreducible-coefficients.py
node verify-kissing-seven-irreducible.js
node verify-kissing-seven-irreducible.js --alternate
~~~

The [rational identity checker](verify-kissing-seven-irreducible-coefficients.py) reconstructs the polynomial and its Gegenbauer coefficients from its roots; it also checks the moment relaxation, sign code, normalizer and orbit arithmetic. The interval certificate now rules out the sole possible excess total, 128, proving the theorem. The residual case for an unrestricted improvement is a symmetry group with a proper invariant subspace, possibly the trivial group.
