# The ternary rank of a Hoffman point–block design is at least twenty

Suppose a strongly regular graph with parameters (99,14,1,2) has a Hoffman coclique C of size 22. Every outside vertex has four neighbors in C by the Hoffman equality condition. They give a 2-(22,4,2) design of 77 distinct four-blocks, because each pair of C points is nonadjacent and has two common neighbors. **Moreover, every triple of C points lies in at most one block:** two distinct outside vertices have at most two common neighbors. Write D for the 22×77 point–block incidence matrix.

**Theorem.** The ternary kernel K=ker(Dᵀ mod 3) has dimension at most two. Equivalently D has rank at least twenty over F₃. This assertion is conditional only on the actual Hoffman coclique. There are no assumptions about the seven-rank or the short lattice shells. It is not a nonexistence proof for the graph.

## Word types and the pure case

For z∈K lift the entries to 0,+1,−1. Write p,q for the two sign counts, w=p+q, s=p−q. All block sums are 0 or ±3. The sum of the block sums is 14s, hence 3 divides s. The identity DDᵀ=12I+2J gives 12w+2s² as the sum of the squares of block sums; thus 3 divides w. A point with nonzero value must have a further nonzero point on each of its 14 blocks, and every other point occurs with it in two blocks. Thus a nonzero word has w≥8.

The +3 blocks have exactly three positive sites, and a positive site belongs to 4+2s/3 such blocks by the corresponding entry of DDᵀz. Similarly a negative site is in 4−2s/3 negative-sum blocks. On summing these incidences and comparing their difference with 14s, one obtains (w−15)s=0. Consequently w=12,15 or 18, since w=9,21 cannot be balanced. At w=15, if both signs are present the two incidences are nonnegative, so |s|≤6 and the sign counts are 6,9.

Weight eighteen is impossible. It would have p=q=9, so there are 12 pure triple blocks of each sign. Of the block types remaining, write n22 for blocks with two of each sign and n11 for blocks with one of each. Same-sign point pairs give n22+3·12=2·choose(9,2)=72; opposite sign pairs give n11+4n22=2·9²=162. Together n22=36 and n11=18. These four disjoint block types already require 12+12+36+18=78 blocks, but there are only 77.

A pure weight-fifteen word, if present, makes dim K=1. On the complement R of its fifteen positive sites, the seven blocks wholly inside R form a 2-(7,4,2) design: every original block has zero or three of the positive sites, and exactly 70 have three. The 7×7 incidence matrix on R has Gram 2I+2J, nonsingular over F₃, so every kernel word vanishes on R. The three translates of an independent kernel word by multiples of the pure word would then have total weight 30 (each of 15 positions is nonzero in exactly two translates); each nonzero translate has weight at least 12, contradiction. This is the same pure case as in [the ternary-kernel theorem](hoffman-ternary-rank.md). The graph switching consequence there is not needed here.

Thus if the claimed dimension bound fails, choose any three-dimensional subspace of K. Its nonzero words have weight 12 balanced (6,6), or weight 15 mixed (6,9). Below the word properties refer only to this subspace.

## Five signed decks, up to change of basis

With a basis of the three-space, the 22 coordinates are columns in F₃³; let z₀ be the number of zero columns. For each of the 13 projective points v let m_v count the nonzero columns of direction v. A projective linear functional f gives a projective word; call its projective zero line high if the word has weight 12 (ten zero coordinates), low otherwise (seven zeros).

Each nonzero column contributes to the weight of exactly nine of the 13 projective words. The number L of high lines therefore satisfies 12L+15(13−L)=9(22−z₀), or L=3z₀−1. Hence 1≤z₀≤4. A high projective line contains 10−z₀ of the nonzero columns, and a low line 7−z₀. Summing over the four lines through v counts all other directions once and v four times. If h_v of those four lines are high, this gives
```
m_v = 2 − z₀ + h_v.
```

To recover all orientations, choose the first-nonzero-coordinate-one representative of each direction, for both points and functionals. Let M_fv be the lift of f(v) to 0,+1,−1. Then MMᵀ=9I: for unequal projective functionals their values are uniform in F₃² on all 27 vectors, and the signed product has sum zero; summing over 13 chosen representatives halves the sum over the 26 nonzero vectors since the product is even. For f equal to itself, there are nine nonzero projective evaluations. If d_v is the excess of columns in direction v over columns in direction −v, the lifted coordinate sums of the words are Md. They vanish for high lines and are independently chosen among ±3 on low lines. Thus for any choice ε_f=±1 on the low lines,
```
d_v = (1/3) · sum_(f low) ε_f M_fv .
```
All possible decks therefore come from high-line subsets, the above signs, and the test that d_v is integral with |d_v|≤m_v and d_v≡m_v mod 2. The signed multiplicities are (m_v±d_v)/2. This is an exhaustive reduction, not a sampling of coefficients.

The [standard-library checker](hoffman_ternary_rank_three.py) generates exactly all invertible 3×3 matrices over F₃ by determinant and uses their 5,616 projective permutations to identify high-line subsets up to change of basis. It expands the signs as above, and checks coverage of every resulting oriented deck under all 11,232 invertible linear changes of basis. This gives exactly one, three, one and zero disjoint deck orbits for z₀=1,2,3,4 respectively. A basis change and a reordering of the literal points preserve zero-sum block membership; this is not a graph symmetry assumption. In particular the 1,3,1 deck count is obtained before imposing any pair or triple constraints on actual blocks.

## Literal design obstruction in the five decks

On each representative label the 22 literal positions by lexicographic column order, retaining repeated columns as **distinct positions**. Candidate blocks are exactly the four-subsets whose columns sum to zero in F₃³. Give each candidate a nonnegative integer variable x_B, with 0/1 in a true design; the triple bound already supplies x_B≤1. Every literal point pair occurs in exactly two chosen blocks, and every literal point triple in at most one.

The [integer coefficient file](hoffman_ternary_rank_three.json) supplies sparse row combinations verified directly by the checker. Signed coefficients on pair equations are allowed, whereas all triple coefficients are nonnegative. If c_B is the sum of the six used pair coefficients and four triple coefficients for candidate B, and R=2·(sum pair coefficients)+(sum triple coefficients), then
```
sum_B c_B x_B ≤ R.
```
In the three direct exclusions all c_B≥0 and R<0. In two further decks, choose the indicated point pair and use one independent inequality per candidate block through it. These inequalities have all c_B≥0 and the target coefficient at least 1,000,000. The right side is strictly less than 1,000,000, so that block cannot be chosen. With no block through the pair, its pair equation fails. The complete replay data are:
```
zero columns   candidate blocks   certificate
1              273                pair (8,15): all 6 caps ≤900193/1000000
2              279                all coefficients nonnegative, R=−999804
2              279                pair (2,16): all 5 caps ≤900206/1000000
2              279                all coefficients nonnegative, R=−999826
3              285                all coefficients nonnegative, R=−999824
```
Pair positions are zero-based in the exact representative ordering. The checker constructs its pair rows and triples from the candidate blocks and verifies every inequality coefficient by coefficient over the integers. There is no solver dependency or floating-point step in the certificate replay. Run `python3 hoffman_ternary_rank_three.py` with the JSON beside it. Existing kernels of dimensions zero, one or two are not ruled out.
