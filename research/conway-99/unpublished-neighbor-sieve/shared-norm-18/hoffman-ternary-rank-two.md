# The two remaining color decks for a two-dimensional ternary Hoffman kernel

Let C, D and K be the Hoffman coclique, its point–block incidence matrix and its ternary kernel. A separate result [gives dim K≤2](hoffman-ternary-rank-three.md), rules out weight eighteen, and shows that a pure weight-fifteen word forces dim K=1. This note assumes dim K=2. Thus nonzero words have weight twelve with sign split (6,6), or weight fifteen with sign split (6,9) up to negation. No short-shell or seven-rank hypothesis is used.

**Theorem.** With a basis of K, give each point of C its column color in F₃². Up to change of basis, the 22 colors must consist of two copies of every color, plus one zero and three copies of a single color v. If v=0 there are six global zero columns and all four projective words have weight twelve. If v≠0 there are three global zero columns, one projective weight-twelve word and three mixed weight-fifteen words. These necessary cases are not asserted to be realized as designs or graphs.

## Finding the six candidate decks

There are four projective directions and four projective nonzero functionals. Let L count the projective weight-twelve words and z the number of zero columns. Since a nonzero column contributes to the weight of exactly three of the four projective words, `12L+15(4−L)=3(22−z)`, so z=2+L. The multiplicity m_v of a nonzero projective direction v is `22−z−w`, where w is the weight of the unique projective word annihilating v.

Choose projective representatives with first nonzero coordinate one, and let M_fv be the lifted pairing of representatives, with entries 0,+1,−1. The same signed-orthogonality argument as for dimension three gives MMᵀ=3I. The signed multiplicity deviation d_v equals `∑_(f mixed) ε_f M_fv` for signs ε_f=±1, since absolute lifted word sums are zero at weight twelve and three at mixed weight fifteen. The two sign multiplicities in a direction are (m_v+d_v)/2 and (m_v−d_v)/2. These exact choices give six orbits on the nine colors under GL(2,3). In lexicographic color order (00,01,02,10,11,12,20,21,22), the orbit representatives are:
```
0: 2 1 4 2 2 2 3 3 3
1: 3 1 3 1 3 2 3 2 4
2: 3 2 2 2 2 2 2 2 5
3: 4 1 2 1 2 3 2 3 4
4: 5 1 1 2 2 2 3 3 3
5: 6 2 2 2 2 2 2 2 2
```

## Four exact integer pair contradictions

Use one variable x_B per **multiset** B of four colors summing to zero in F₃² that fits the corresponding available color multiplicities. An actual block count x_B is a nonnegative integer. For each pair multiset P, the sum over B of its number of P-subpairs times x_B must equal twice the number of literal pairs with these colors, since each literal pair of C points belongs to two blocks. The latter number is either m_i m_j for i≠j or choose(m_i,2), using literal color multiplicities m_i (not projective multiplicities). No triple constraint or graph adjacency enters the following four contradictions.

Rational row reduction of the explicit pair equations expresses the following individual block counts as an integral linear combination of the free block counts plus the indicated noninteger constant:
```
deck   four-color multiset   constant
0      00 00 01 02           −11/3
1      00 01 11 21           −11/3
3      00 00 00 00            11/3
4      00 01 11 21             8/3
```
Thus none is an actual integer design. The [standard-library checker](hoffman_ternary_rank_two.py) regenerates the 48 GL(2,3) basis permutations and all multiplicities, tests the exact row reduction over fractions, and verifies the four claimed contradictions. For the last two decks, it also computes small integer controls in the stronger color-aggregate model using the triple bound (each literal triple in at most one block): there are 25 in deck 2 and 15 in deck 5. These are only feasible aggregated block-count profiles. They neither assign literal blocks nor specify any outside adjacency.

## Genuine local constraints inside the two remaining decks

In the v=0 deck, write Z for the six global zero points and D_i for the four nonzero points on a projective direction, with two of either sign. Then `Z∪D_i` is the zero set of a weight-twelve word and contains exactly seven blocks. Let a be the number of all-zero blocks in Z, and let c_i indicate whether the whole four-point D_i is a block. The only possible remaining blocks in `Z∪D_i` are two Z points and an opposite pair in D_i. Counting pairs in Z gives
```
Σ_i c_i=2a−2,   a∈{1,2,3}.
```
In fact any two all-zero blocks have disjoint two-point complements in Z, by the no-repeated-triple rule. Globally the numbers of blocks meeting Z in exactly one or in no point are respectively 24+8a and 23−3a. At an individual q∈Z, let a_q count the all-zero blocks through q and r_i(q) the two-zero blocks through q using direction i. A one-zero block through q uses a nonzero affine line triple in F₃² off the origin. For the two opposite affine lines defined by a functional whose kernel is direction i, the two counts both equal
```
r_i(q)+a_q−2.
```
Indeed each nonzero color is counted four times around q. Subtracting the conditions for each opposite color pair shows that the four deviations between opposite affine-line counts vanish by invertibility of the signed matrix M. The total one-zero count is 4+2a_q from the literal pair incidence at q over the five other zero points. For a fixed nonzero direction i, each constituent color occurs in all opposite affine-line pairs except that indexed by i; the stated formula follows.

In the v≠0 deck, the global zero set Z has size three. The weight-twelve word has zero set Z plus the high-direction cell of size seven (five with one sign, two with the other). Its seven zero-sum blocks use at least two blocks through each of its ten zero sites. To see the last assertion in any balanced word, for a zero site the number of blocks of type (one positive, one negative, two zeros) plus three times its number of positive triple blocks is 12 by positive point pairs; its opposite version is the same. Counting the zero point pairs gives 18 instead of 12, so the number of all-zero blocks through the site is two plus its positive-triple count. Each of the other three projective words has one all-zero block Q in its seven-point zero set. It either uses its nonzero direction cell of four balanced points or uses two global zeros and an opposite pair in that cell. At least one Q uses two global zeros. If not, all six block occurrences of pairs from Z are in the weight-twelve zero set. These six two-zero blocks plus the one remaining zero block would supply at most 6+3=9 memberships at its five majority-sign high-cell points, but they require at least ten. More generally if m of the three Q use two global zeros and h₀ high-zero-set blocks use no global zeros, then the same incidence count gives 2m−h₀≥1.

Neither of these graph-local deductions excludes its remaining deck. Run `python3 hoffman_ternary_rank_two.py` for the exact combinatorial reduction.
