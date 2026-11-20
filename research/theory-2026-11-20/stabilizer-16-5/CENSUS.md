# Orbit-mass certification of the dimension-ten source list

## 1. Fourier and slice reductions

Write $V_d=\mathbb F_2^d$. For $S\subset V_d$ of size $n$, put $w_S(u)=\sum_{x\in S}(-1)^{u\cdot x}$. Each nonzero $u$ has two affine fibers of sizes $(n\pm w_S(u))/2$. For a Sidon set, character orthogonality gives
$$\sum_u w_S(u)^2=2^d n,\qquad \sum_u w_S(u)^4=2^d(3n^2-2n).$$
For the fourth moment, the ordered zero-sum quadruples are the four-equal tuples and the permutations of two distinct equal pairs. Let $L=n\bmod2$, $Q=2^d$ and $H=(2k-n)^2$. If every hyperplane has at most $k\ge n/2$ points, summing $(w_S(u)^2-L)(w_S(u)^2-H)\le0$ over $u\ne0$ yields
$$Q(3n^2-2n)-n^4-(L+H)(Qn-n^2)+LH(Q-1)\le0.$$
Let $h(d,n)$ be the smallest such integer $k$ satisfying this numerical inequality. This floor is recomputed for every census stage.

For a split $S=(A,0)\cup(B,1)$ in $V_{d-1}\times\mathbb F_2$, both layers must be Sidon and their distinct pair-sum sets $\Delta A$ and $\Delta B$ must be disjoint. Conversely these three conditions suffice. For each nonzero $u\in V_{d-1}$ the two extended character values are $w_A(u)\pm w_B(u)$. If a largest hyperplane contains $m$ points, then $|w_A(u)|+|w_B(u)|\le 2m-n$. This holds for every choice of splitting hyperplane, not just a maximizing one.

## 2. Certified source classes

The files d7.txt through d10.txt contain candidate affine representatives as lists of binary-coordinate words written in decimal. The verifier checks rank, the Sidon property, and pairwise affine inequivalence. These lists are certified to be exhaustive by labeled incidence masses.

For each fixed size $n$ and dimension $d$, mark a hyperplane containing $a\ge h(d,n)$ points, and put $b=n-a$. If $G(S)$ is the affine stabilizer order, $N_a(S)$ the number of such hyperplanes and $L(A,b)$ the number of allowable $b$-point sets opposite the given anchor $A$ containing the specified origin, then
$$\sum_{[S]}\frac{N_a(S)}{G(S)}
 =\sum_{[A]:|A|=a}\frac{L(A,b)}{bG(A)}.$$
Indeed, count labeled pairs of a cap and a hyperplane and divide by the full affine-group order. At a fixed hyperplane, affine images of $A$ number $|\mathrm{AGL}(d-1,2)|/G(A)$. There are $2^{d-1}L(A,b)/b$ opposite sets, by marking a point and translating the opposite layer. The stabilizer of the marked hyperplane has order $2^{d-1}|\mathrm{AGL}(d-1,2)|$. The two sides therefore agree. Omitting a true class gives a strict deficit at some $a$, since it has at least one marked hyperplane. The same proof works if only **largest** hyperplanes are marked, provided both sides impose that invariant condition. Here a largest marked layer requires $|w_A(u)|+|w_B(u)|\le a-b$ for all nonzero $u$.

The initial dimension-seven count fixes the ordered standard affine frame. In dimension five the pair bound precludes ten points; in dimension six direct frame extension gives no spanning 10-set, hence none at all. Consequently all sets relevant to the dimension-seven stage span. The counts of frame extensions of sizes 10,11,12,13 are respectively 1400,10920,21840,0. Dividing the number of labeled sets with an ordered frame by the group order amounts to summing $8!$ times the number of unordered contained affine bases divided by the stabilizer order. Agreement certifies the base. At later stages the listed sizes exceed the maximum in the dimension below. Excluding one size excludes every larger size by taking subsets.

|Dimension|Sizes|Certified affine class counts, in order|
|---|---|---|
|7|10,11,12,13|2,1,1,0|
|8|14,15,16,17,18,19|5,5,3,1,1,0|
|9|20,21,22,23,24,25|1681,738,127,8,1,0|
|10|32,33,34,35|200,7,1,0|

Only size 32 in dimension ten uses maximal marks; its masses for $a=20,21,22,23,24$ are respectively $1/5,44,4933/5,163,0$. The other stages use all marks above their moment floors. For each right-side count anchor $A$, take zero in $B$ and use the Cayley graph on available points, adjacent when the sum is outside $\Delta A\cup\{0\}$. Cliques are enumerated with proper-color upper bounds. While selecting a new point, delete each prospective fourth point summing with it and two earlier points to zero. For maximal marks one may check only the lexicographically least translate of $B$ through zero, then credit $b$ translates, because a Sidon set of size greater than two has no nonzero translation fixing it: a period would occur as the sum of at least two distinct pairs.

For stabilizers, fix a source point and sum over images of that point. Recursively choose images of a spanning basis inside the target set. Compare membership on the whole enlarged span after adding each basis vector; at full rank this is precisely an isomorphism. Unary colors obtained by alternating weighted Walsh transforms on primal/dual coordinates are equivariant under linear changes after rooting, even when computed modulo $2^{64}$. They only prune exact tests. Equal fingerprints are **not** presumed to prove equivalence: the verifier searches all rooted isomorphisms for a colliding fingerprint. Counts of actual isomorphisms and search solutions have checked signed integer addition; incidence masses use exact rational arithmetic.



All sizes above dimension ten are unnecessary for this packet. The ordered-frame generation is in frame.py, affine group orders in group.cpp, and local counts in count.cpp/classify.py.
