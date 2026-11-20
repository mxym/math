# The optimum distance of a binary 16-qubit, 5-logical-qubit stabilizer code is four

There is no binary stabilizer code with parameters `[[16,5,d]]` for any $d\ge5$. A known `[[16,5,4]]` code attains the bound. This is **only a theorem about stabilizer codes**. No assertion about nonadditive codes at Hilbert-space dimension 32 is needed.

[Grassl’s qubit entry](https://www.codetables.de/QECC.php?q=4&n=16&k=5) lists distance 4–5 and gives the lower-bound stabilizer used in the replay. In October 2026, [C.-Y. Lai, §VII-D](https://arxiv.org/html/2610.37894v1#S7.SS4), reported 27 surviving enumerators and explicitly left nonexistence unresolved. The proof below does not assume that list is exhaustive and uses no externally obtained solver verdict. Nor does it use the exclusion of the neighboring `[[17,6,5]]` parameter.

## 1. Stabilizer and shadow identities

Use phase-free single-qubit labels $0,X,Z,Y$, identified with $\mathbb F_2^2$. Their symplectic pairing is one exactly for distinct nonzero labels; add over coordinates. A putative code determines an isotropic subspace $S$ of $\mathbb F_2^{32}$ of dimension 11, order $R=2048$. Distance at least five means $S^\perp\setminus S$ has no vectors of weights one through four.

Write $A_j,B_j$ for the ordinary weight counts of $S,S^\perp$. For $K_j(i)=[y^j](1+3y)^{16-i}(1-y)^i$, character orthogonality gives
$$
 R B_j=\sum_i K_j(i)A_i.
$$
The sign $(-1)^{\mathrm{wt}(s)}$ is a character on $S$: the polar form of weight parity is the symplectic form, which vanishes on $S$. Extend this character to the ambient vector space. Then
$$
 R H_j=\sum_i(-1)^i K_j(i)A_i
$$
counts, after division by $R$, the vectors of weight $j$ in a coset of $S^\perp$. Thus $H_j\ge0$. In the even-stabilizer case take this coset to be $S^\perp$ itself; the identity still holds. Both character identities hold for any coordinate-type cell instead of a Hamming weight. Since $S\subset S^\perp$, all cells have $B\ge A$ and cells of weights 1–4 have $B=A$.

## 2. The degenerate branch is impossible

If any nonzero element of $S$ has weight $w\le4$, relabel coordinates and apply local Pauli-label permutations so this element is $Z$ on the first $w$ coordinates. A cell $(a,b,j)$ counts labels $X,Y$ on those positions, labels $Z$ there, and nonidentity labels outside. The cell count of $S$ is zero for odd $a$ by isotropy. Addition of the reference exchanges $b$ and $w-a-b$, so the remaining cell counts are variables identified across these two indices.

For a fixed source label in a cell, sum its characters over each target cell, using an ordinary quaternary Krawtchouk coefficient on the last $16-w$ positions. On the first $w$ positions the single-coordinate generating factors are $1+z+2u,1+z-2u,1-z$ for source $I,Z,X/Y$, respectively. Here powers of $u,z$ count target transverse and $Z$ entries. This produces the full integer matrix $K$ on the nonnegative reduced source variables. Let $L$ expand these reduced variables to all cells. Then $K-RL$ is nonnegative as a linear expression on every feasible distribution, and its entries on weights 1–4 vanish. The signed-source transform similarly gives inequalities $R H\ge0$; apply the sign *before* combining the paired source cells. The identity-cell count is one and the sum of expanded counts is 2048.

For each $w=1,2,3,4$, `cert1.json through cert4.json` gives an exact combination of these equations and inequalities with identically zero left side and strictly positive right side. The right sides are respectively $124928,794624,47104,1118208$. Negative multipliers occur only on equalities. The standard-library checker `verify.py` reconstructs every entry using literal enumeration of all at most $4^4$ local target Pauli words, not the generating function used to discover these certificates. Every cancellation is checked with integers. Thus a putative code must be pure: $S^\perp$ has no nonzero vector of weight at most four.

## 3. Single-coordinate syndromes and the geometric obstruction

Choose a basis of $S$. The syndrome of an error lists its eleven symplectic products with this basis. Let $C\subset\mathbb F_2^{11}$ be the syndromes of the 48 nonidentity one-coordinate errors. Purity makes them distinct and nonzero. Four distinct such errors cannot sum to the zero Pauli word: a coordinate containing one or two of them gives a nonidentity result, and four is not a multiple of three. Thus any sum of four distinct elements of $C$ vanishing would give a nonzero word of weight at most four in $S^\perp$. Hence $C$ is Sidon (its unordered distinct pairs have distinct sums). On each coordinate the three syndromes sum to zero: $C$ has 16 unordered triples with common sum zero.

If some affine hyperplane contains at least 32 points of any 48-point Sidon set in $\mathbb F_2^{11}$, **no vector is the sum of more than eleven unordered triples of distinct points** of that set. Here is our finite proof, certified by two independent searches. Choose a largest affine hyperplane and normalize its two sides to $A,B\subset\mathbb F_2^{10}$. The required size $m=|A|$ is 32, 33 or 34: there are exactly 200, 7 and 1 affine classes of Sidon sets of those sizes in dimension ten, and none of size 35. These statements are reverified from lower dimensions; see `CENSUS.md`. The Sidon condition on the union is precisely that both layers are Sidon and their internal difference sets are disjoint. By a shear/translation one can translate either layer independently without departing from affine equivalence. Normalize the opposite side to contain zero. For each character $v\ne0$, the two parallel signed imbalances of the whole cap have values $W_A(v)\pm W_B(v)$, where $W_X$ is the sum of the characters over $X$. Maximality of the chosen layer is precisely $|W_A(v)|+|W_B(v)|\le 2m-48$ for all nonzero $v$.

The first search fixes zero in $B$ and grows a clique on the allowable nonzero differences, also rejecting all four-point collisions among the selected points. A greedy proper coloring bounds each remaining clique. The second orders differences, selects the least difference of $B$ in this order, and translates its endpoints to $0,d$. It forbids smaller differences anywhere, then grows the other points by independent ordered branching and four-point tests. Every translation orbit has a representative in either search. The two searches compare the *actual lists* of opposite sets, canonicalized under translation. Only two 32-point sources admit any: 62 and 124 respective translation classes. None of the other 206 sources admit one. Directly checking all 48 points and all $\binom{48}{3}=17296$ triples of every completion gives maximum multiplicity eleven. Multiplicity is affine-invariant (the sum of three translated points is translated by the same vector). This contradicts the required sixteen triples at zero. The class assertion used here concerns only sets with a hyperplane of size at least 32; the full classification of 48-sets is not assumed.

Consequently every hyperplane intersects $C$ in at most 31 points. For the character specified by a nonzero stabilizer of weight $i$, the syndrome sign sum is $48-4i$: each position with identity contributes three and every other position contributes minus one. The corresponding affine side sizes are $24\pm(48-4i)/2$, hence both even. Since they are at most 31, they are at most 30. It follows that every nonzero stabilizer has weight in **9 through 15**.

## 4. Final contradiction and attainment

With support only at 0 and 9–15, take the following weighted sum of normalization, distance identities and shadow inequalities. Use coefficients $-215040,108$ on $A_0=1,\sum A_i=2048$; coefficients $29,15,3,1$ on $R(B_j-A_j)=0, j=1,2,3,4$; coefficients $48,4,4$ on $R H_j, j=0,1,2$. The coefficient of each allowed $A_i$ is zero. Thus
$$
             0=6144+2048(48H_0+4H_1+4H_2)>0.
$$
`cert0.json` and `verify.py` check the eight cancellations explicitly. This excludes the pure branch, and therefore all putative codes of distance at least five.

The direct checker `lower.py` verifies the eleven independent commuting rows in `known16.txt` (sixteen X bits then sixteen Z bits, in displayed qubit order). Their group has size 2048. Exhaustive enumeration of errors through weight four gives no undetectable nonstabilizer error through weight three, and 239 of weight four. This establishes the lower bound independently of the table’s label.

## Replay

`./replay.sh` requires Python 3.10+ and a C++17 compiler. No external LP package or live data is needed. It checks the five certificates and a distance-four witness, certifies the dimension-ten source census by incidence masses, and repeats both independent high-slice searches. `./replay.sh endpoint` skips **only** the dimension-seven through dimension-ten census, useful if that exact census has already been replayed. `JOBS=2` is the default. `CFLAGS=-O3` can replace the default `-O3 -march=native`.

The standard stabilizer formalism and shadow terminology are also described in [Calderbank, Rains, Shor, Sloane](https://arxiv.org/abs/quant-ph/9608006) and [Lai’s accompanying repository](https://github.com/cylai-nycu/quantum-code-lp). Integer certificates, not earlier numerical statuses, are used here.

[Download the full proof and replay bundle](stabilizer16_5_exact4_v1.zip), SHA-256 `1b3c6efdf393041a245ac3f0e3b253a5fb9d5ac08ef78515edbd68f8a8dc6fdc`. The bundle contains both high-slice search implementations and the entire lower-dimensional classification input and replay. The previously independent [dimension-eleven Sidon result](../binary-sidon-eleven/exact48/README.md) explains the shared source census.
