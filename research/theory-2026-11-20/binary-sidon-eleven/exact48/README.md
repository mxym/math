# The maximum size of a Sidon set in the eleven-dimensional binary vector space

**Claim certified by the complete replay:** the maximum is **48**. A set in a binary vector space is Sidon if all sums of two distinct points, with order ignored, are distinct. This is a finite-computation proof. It is about the first dimension unresolved in Czerwinski and Pott's [Table 2](https://arxiv.org/html/2411.12911v3#S6.T2), which gives 48–58. The established construction of 48 points is not new. The earlier checkpoint in this repository proved an upper bound of 54. The nonexistence result here makes no symmetry assumption on a possible 49-set, uses no unpublished classification as a premise, and does not claim to determine larger dimensions.

## 1. Fourier and slice reductions

Write $V_d=\mathbb F_2^d$. For $S\subset V_d$ of size $n$, put $w_S(u)=\sum_{x\in S}(-1)^{u\cdot x}$. Each nonzero $u$ has two affine fibers of sizes $(n\pm w_S(u))/2$. For a Sidon set, character orthogonality gives
$$\sum_u w_S(u)^2=2^d n,\qquad \sum_u w_S(u)^4=2^d(3n^2-2n).$$
For the fourth moment, the ordered zero-sum quadruples are the four-equal tuples and the permutations of two distinct equal pairs. Let $L=n\bmod2$, $Q=2^d$ and $H=(2k-n)^2$. If every hyperplane has at most $k\ge n/2$ points, summing $(w_S(u)^2-L)(w_S(u)^2-H)\le0$ over $u\ne0$ yields
$$Q(3n^2-2n)-n^4-(L+H)(Qn-n^2)+LH(Q-1)\le0.$$
Let $h(d,n)$ be the smallest such integer $k$ satisfying this numerical inequality. In particular $h(11,49)=30$ and $h(10,31)=20$.

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

## 3. From a hypothetical 49-set to seven shapes

Let $m$ be its largest hyperplane size. The source census and moment bound give $30\le m\le34$. When $m=32,33,34$, run two complete opposite-layer searches at sizes $17,16,15$ respectively, for every one of the 200,7,1 anchor classes. None completes. The second algorithm distinguishes the least pair difference and is described below. As a control, a 32-point slice of the known 48-point construction gives 992 labeled admissible 16-point opposite layers through zero in the first search; the second returns an explicit 48-point witness which is checked from scratch. This leaves $m\in\{30,31\}$.

Choose a size-$m$ hyperplane and inside it a largest hyperplane intersection $C$ of size $a$. This splits the whole space into four parallel codimension-two affine cosets. Every union of two cosets in this quotient is a hyperplane, so any two layer sizes sum to at most $m$.

For $m=31$, the moment floor gives $a\ge20$. Since $|w_A|\le2m-49=13$ for the 31-set $A$, we have $a\le22$. For $m=30$, the stronger floor $a\ge20$ follows as follows. Suppose all internal affine hyperplanes had at most 19 points. Then $|w_A(u)|\le8$ at all nonzero characters. Put $g=\bigoplus A$ and $H=g^\perp$, so $|H|\ge512$. On $H$, an even number of points evaluate to one; therefore $w_A(u)\equiv30\equiv2\pmod4$ and $|w_A(u)|\le6$ away from zero. Character orthogonality on $H$ gives $\sum_{u\in H}w_A(u)^2=|H|\,\#\{(x,y)\in A^2:x+y\in H^\perp\}\ge512\cdot30$. Hence
$$\sum_{u\ne0}w_A(u)^4\le64(1024\cdot30-30^2)-28(512\cdot30-30^2)=1,503,600,$$
contradicting the exact fourth moment $1024(3\cdot30^2-2\cdot30)-30^4=1,893,360$. Thus $a\ge20$. The other side of a 30-set has 19 points; some sublayer has at least 10. Since any two cosets form a hyperplane, $a\le20$.

The complete shape list, with $C$ first, is
$$
(22,9,9,9),\ (21,10,10,8),\ (21,10,9,9),\ (20,11,11,7),\ (20,11,10,8),\ (20,11,9,9),\ (20,10,10,9).
$$
These are tested in the displayed order, first excluding all 31-hyperplanes with a 22-point internal slice, and then excluding those with a 21-point internal slice. Thus, in each surviving case, **every** 31-hyperplane has internal maximum at most the currently considered $a$. This explains the equal cutoff on both possible 31-hyperplanes in the rows with repeated big layers. For a pair $C,X$, $C\cup(X,1)$ is itself a hyperplane slice. If this slice has size 31 and $a$ is its internal maximum upper bound, its nontrivial coefficient limit is $2a-31$; if not, it is bounded by the global limit $2m-49$ with parity of $|C|+|X|$. For $m=30$ the internal maximum is 20, giving limit 10. The two respective bounds for the first and second added layers in the seven cases are
$$(13,13),(11,11),(11,12),(9,9),(9,12),(9,13),(10,10).$$
The check for a layer $X$ is exactly $|w_C(u)|+|w_X(u)|\le L$ for nonzero $u\in V_9$; the vertical character has known value $|C|-|X|$.

## 4. Quarter search and the quadratic filter

Fix any affine representative $C\subset V_9$ from the exhaustive census and write the other three layers as $U,V,W$. Because the quotient is $V_2$, four distinct points with zero sum come either from one layer, from two points in each of two layers, or from one in each of all four. Hence the necessary and sufficient conditions are:
1. All four sets are Sidon.
2. Their six pairs of distinct-pair-sum sets are disjoint.
3. $W\cap(C+U+V)=\varnothing$.

An affine change in $V_9$ taking $C$ to its representative extends to the whole space. Once $C$ is fixed, shear translations on two independent nonzero quotient directions move $U$ and $V$ independently by arbitrary amounts, and their sum translates $W$. We can therefore enumerate $U,V$ up to their own translations without choosing a coordinate origin for $W$. Given compatible $U,V$, test *all* subsets of the required size in the hole set $V_9\setminus(C+U+V)$ for the remaining conditions. The search does not quotient by any presumed automorphism of the hypothetical solution.

To enumerate a nontrivial layer up to translation, choose a fixed total order on permissible nonzero differences; its least occurring difference $d$ is obtained by exactly one unordered pair because the layer is Sidon. Translate this pair to $\{0,d\}$; all remaining differences must be later in the order. There are exactly two such translates, interchanged by adding $d$; the smaller of the two word lists is kept. A second solver uses ordinary numerical difference order rather than the first solver's degree order.

For the case $m=30$ there is an additional optional necessary condition on a proposed 30-set $A$. Its opposite layer $T$ has odd size 19. Translate $T$ independently so that its XOR is zero. For each linear functional let $k(u)$ be the number of its 19 points on the side with value one; $k(u)$ is even, $w_T(u)=19-2k(u)$. The function
$$q(u)=\binom{k(u)}2\bmod2=\sum_{x<y\in T}(u\cdot x)(u\cdot y)$$
is quadratic in the ten coordinates of $u$, with no constant term, and equals $k(u)/2\bmod2$. At $|w_A(u)|=10$, the condition $|w_A|+|w_T|\le11$ forces $w_T=-1$, hence $q(u)=1$. More generally take all even $k\in[0,19]$ for which $|19-2k|\le11-|w_A(u)|$. No choice rules $A$ out; a unique parity of $k/2$ imposes a linear constraint on the 55 squarefree monomials of degrees one and two. Inconsistent binary linear equations are an exact obstruction. Related support-parity and quadratic Walsh-congruence arguments for APN graphs appear in [Beierle, §3, especially (3.9)–(3.11)](https://arxiv.org/html/2609.35689v1#S3); the application here filters opposite layers of the 49-set. The first checker uses elementary elimination on the 55-column system. Consistency alone is never used to infer existence. The independent second checker omits this filter altogether and rules out completion by directly inspecting the larger family of pairs and their hole sets.

The first implementation uses proper greedy coloring, bit-sliced Walsh counts, a difference-to-layer inverted index and XOR-permuted bitmasks for holes. The second uses a different branching recurrence (remove $t-1$ stable sets, branch on the residual), signed integer character counts, direct pair-mask comparison and individual element tests of the hole set. They independently check the surviving fourth-subset problem. For all six 31-hyperplane cases, the verifier compares exact per-anchor numbers of candidate pairs, large hole sets and maximum hole sizes. For the 30-hyperplane case those counts are reported separately: the first algorithm imposes the quadratic filter and the second deliberately does not. In the (20,11,9,9) case one may generate the secondary nine-set listing separately for each of the few permissible eleven-sets, with its pair differences already forbidden; this keeps memory down without changing the pairs enumerated. A positive control at size 48 requires the solvers to recover full witnesses from just the 20-point first layer with remaining sizes 12,10,6. The recovered witnesses need not coincide; each is checked separately for all 1128 unordered distinct-pair sums.

## 5. Exact six-variable APN extremum

Let $F:V_6\to V_6$ be almost perfect nonlinear (APN): for every $h\ne0$ each equation $F(x+h)+F(x)=c$ has at most two solutions. Its graph $G=\{(x,F(x)):x\in V_6\}$ is a 64-point Sidon subset of $V_{12}$: distinct unordered graph pairs with the same sum would give at least four solutions to one derivative equation. Define its linearity to be the largest absolute Walsh coefficient of a nonzero component,
$$L(F)=\max_{a\in V_6,\,0\ne b\in V_6}\left|\sum_{x\in V_6}(-1)^{a\cdot x+b\cdot F(x)}\right|.$$
The larger character half of the graph has $(64+|W|)/2$ points and is an eleven-dimensional affine-space Sidon subset. Hence $L(F)\le32$ for **every** six-variable APN function, not only quadratic ones. Vectorial nonlinearity here has its standard component meaning, namely $32-L(F)/2$.

This upper bound is attained. Use $\mathbb F_{32}=\mathbb F_2[t]/(t^5+t^2+1)$, and on $\mathbb F_{32}\times\mathbb F_2$ take
$$F(x,y)=\bigl(x^3+y(x^{16}+x),\;y\operatorname{Tr}_{32/2}(x)\bigr).$$
This is the known Gold extension given by [Beierle and Carlet, immediately following Proposition 1](https://doi.org/10.1007/s10623-022-01111-6). The included `apn.py` constructs its full 64-value table, checks all 63 derivatives, all 2016 unordered graph pair sums and all 4032 correlations with nonzero output component. In particular $L(F)=32$. Thus the **maximum possible six-variable APN linearity is 32**, or equivalently the **minimum possible component nonlinearity is 16**. The example and graph-section identity are established prior tools; the sharp upper bound for unrestricted six-variable APN maps is the consequence here. [Beierle, September 2026, after Theorem 1.1](https://arxiv.org/html/2609.35689v1#S1) explicitly records the prior dimension-six general upper bound 52. The all-dimensions question about a uniform $C<1$ and questions on the existence of APN permutations are not resolved by this argument.

## 6. A historical dimension-twelve corollary

The [follow-up](../../binary-sidon-twelve/Overview.md) improves the upper bound below from 84 to 83 without symmetry assumptions.

The dimension-eleven maximum also gives $s(V_{12})\le84$ (not an exact determination in dimension twelve). If $|S|=85$, all hyperplanes have at most 48 points, so all nontrivial Walsh coefficients have modulus at most 11. Translate $S$ to XOR zero, possible because 85 is odd. Every character evaluates to one on an even number of points, so the allowed signed values are $-11,-7,-3,1,5,9$. On these six numbers
$$P(x)=-(x+11)(x+3)(x-1)(x-9)=-x^4-4x^3+98x^2+204x-297$$
has values $0,2048,0,0,2048,0$. Let $T$ be the number of ordered zero-sum triples in $S$. Character orthogonality gives $\sum w=4096\mathbf1_{0\in S}$ and $\sum w^3=4096T$, in addition to the two unconditional Sidon moments. With $n=85$, evaluating the sum over nontrivial characters gives
$$\sum_{u\ne0}P(w(u))=-1,249,280+4096(204\mathbf1_{0\in S}-4T)<0.$$
Indeed if zero is present then the patterns $(0,x,x)$ and their permutations give $T\ge3n-2$; otherwise the correction is also nonpositive. This contradicts the explicit evaluations. By heredity the bound holds for all set sizes. The same parity-check argument as below also gives maximum binary linear minimum distance 4 at [84,72], previously [listed as 4–5](https://www.codetables.de/BKLC/BKLC.php?q=2&n=84&k=72).

## 7. Reproducibility, coding interpretation, sources

From this directory run `./replay.sh` with a GCC- or Clang-compatible C++17 compiler and Python 3.10+ (standard library only). Default `JOBS=2`; adjust for available cores. Default compiler flags are `-O3 -march=native`; `CFLAGS=-O3` is also valid. Use `./replay.sh classification` or `./replay.sh endpoint` to replay the two stages separately. The `endpoint1` and `endpoint2` arguments run individual quarter checkers. For an unconditional replay do not skip the classification. Files d7.txt–d10.txt and known48.txt are input data, not external oracle results. Integer $x$ represents its binary digits; addition is bitwise XOR.

The 47-coordinate, eleven-check-bit lower construction is due to [C.-L. Chen, IEEE Transactions on Information Theory 37 (1991), 1429–1432](https://doi.org/10.1109/18.133262). The known witness can be obtained from the [Grassl binary [47,36,5] generator matrix](https://www.codetables.de/BKLC/BKLC.php?q=2&n=47&k=36) by adjoining the zero vector to its parity-check columns. The verifier checks the stored witness directly. Conversely a binary $[48,37,\ge5]$ code would give 49 Sidon points in eleven dimensions by the same parity-check construction. Thus the open [Grassl [48,37] distance interval 4–5](https://www.codetables.de/BKLC/BKLC.php?q=2&n=48&k=37) becomes exactly 4. Its lower bound is elementary: choose 48 distinct vectors in the affine coset with first coordinate one in $V_{11}$, including $e_0$ and $e_0+e_j$ for $1\le j\le10$. These parity-check columns span and no one, two, or three sum to zero. More generally, taking any 48 columns shows that the maximum possible length of a binary linear code with at most eleven parity checks and minimum distance at least five is exactly **47**. These assertions concern binary **linear** codes.

- I. Czerwinski and A. Pott, [Sidon sets, sum-free sets and linear codes](https://www.aimsciences.org/article/doi/10.3934/amc.2023054); and [On large Sidon sets](https://doi.org/10.1016/j.jcta.2025.106129), [author preprint Table 2](https://arxiv.org/html/2411.12911v3). The latter lists exact maxima through dimension ten and interval 48–58 in dimension eleven.
- D. Thornburgh, [A new upper bound for Sidon sets in binary dimension 4k+3](https://arxiv.org/abs/2609.27731), September 2026. Its general theorem specializes to 61 in dimension eleven.
- I. Bouyukliev and Z. Varbanov, [Some results for linear binary codes with minimum distance 5 and 6](https://www.moi.math.bas.bg/moiuser/~iliya/pdf_site/getPDFbvar.pdf), IEEE Transactions on Information Theory 51 (2005), Tables III–IV, gives relevant historical code counts. The incidence certificates above do not depend on these tables, nor do we identify all distance-six codes with even codes. For an example of a later corrected historical census see [Optimal Linear Codes and Their Hulls](https://doi.org/10.3390/math13152491).

[Download the complete proof and exact replay](Sidon11_exact48_v1.zip), SHA-256 `32941239672411e70a1eeca8fe0d5876cc9c97c736a2d6655346063e8fe04f59`. Extract and run `sha256sum -c SHA256SUMS && JOBS=4 ./replay.sh` from the extracted directory. [Replay summary](CHECKS.md); the per-anchor ledger and source files are in the ZIP. Both independent terminal search implementations have exhausted all seven quarter shapes; the second makes no use of the optional quadratic filter. The six-variable APN witness can be checked separately with [apn.py](apn.py).
