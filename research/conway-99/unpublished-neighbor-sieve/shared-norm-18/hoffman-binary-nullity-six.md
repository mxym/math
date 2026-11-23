# A Hoffman coclique has binary design nullity at most six

Let C be an independent 22-set in a putative SRG(99,14,1,2), and let D be its 22-by-77 incidence matrix against the exterior. Then

$$\dim_{\mathbb F_2}\ker D^t\le6,\qquad \operatorname{rank}_{\mathbb F_2}D\ge16.$$

This applies at every surviving Seidel rank, for every such C. It does not assert that C exists on every face, or exclude a graph or a Seidel rank.

## The putative extreme code

Every exterior point has four C-neighbors (Hoffman equality); the neighborhoods are distinct 4-sets, called blocks. Each point is on 14 blocks, every pair on exactly two, and no two blocks share three points. Let K be the binary kernel. It contains the all-ones word; each block meets every kernel word evenly. For word weight w the number of blocks fully contained in the word is w(w−8)/4, from the first two design moments. Thus any nonconstant nonzero word has even weight 8, 10, 12 or 14, using complements. In particular **no block lies within a weight-eight word**.

For completeness we recall the nullity-seven starting point. Write B_i for the number of weight-i words of the dual code. The binary MacWilliams transform at length 22 gives
$$2^{\dim K}(B_4+7B_2+28)=17920:$$
the polynomial K_4(w)+7K_2(w)+28 in the binary Krawtchouk polynomials is 8960 at w=0,22 and zero at the other four weights. The 77 genuine blocks are distinct dual tetrads, so dim K≤7. At equality p=B_2≤5, B_4=112−7p. A dual pair joins equal generator-column signatures. Each such pair has exactly two disjoint mate pairs: these complete its actual blocks, are themselves dual pairs, and cannot meet each other because the blocks would share three points. The mate graph on the p pairs is simple 2-regular. A signature class of size ≥4 gives too many pairs, and a triple class would have three internal pairs all requiring both of the at most two remaining pairs as mates, impossible. Hence if p>0 there are p≥3 disjoint doublets. Swapping coordinates inside these doublets preserves dual tetrads. An orbit with at least one singly used doublet is a Boolean cube, in which genuine blocks are independent (adjacent subsets would share three sites). The doublets give 24p singly used endpoint incidences in genuine blocks since each endpoint is on 14 blocks, two with its twin. Thus at least 6p actual blocks are in these cubes, requiring at least 6p nonblocks. But only 35−7p dual tetrads are nonblocks, impossible for p≥3. Consequently at dimension seven all 22 signatures are distinct.

Choose the constant word as first basis vector. The remaining data are 22 distinct sites S in the affine space F₂⁶; all graph blocks are affine planes (their four signatures sum to zero). Each nontrivial character has sum ±2 or ±6 on S, by the four possible weights. There are exactly 21 nontrivial characters of absolute sum 6, by Parseval: 22²+36h+4(63−h)=64·22. The smaller side of each of these cuts is a weight-eight word.

## Four possible eight-point halves

Fix such a cut. In affine coordinates write S=(A,0)∪(B,1) with A,B subsets of F₂⁵ of sizes 8,14. For nontrivial χ on the five-space both W_A(χ)+W_B(χ) and W_A(χ)−W_B(χ) must belong to {−6,−2,2,6}, where W sums the character on a set. In particular A is not in a proper affine hyperplane (|W_A|=8 would be impossible). Its affine dependence space, the binary kernel of the matrix with columns (1,a), has dimension two, even weights and no word of weight two. If u,v are generators then the union of their supports has size (|u|+|v|+|u+v|)/2≤8. Therefore the sorted nonzero weights are exactly one of
$$(4,4,4),\quad (4,4,6),\quad (4,4,8),\quad (4,6,6).$$
These weights determine all three nonzero coordinate-column multiplicities of a two-row generator, plus the number of zero columns. Thus they determine the dependence space up to coordinate permutation, and A up to affine equivalence (any matching of the columns preserving all dependencies induces a linear isomorphism of their spans, preserving first coordinate). The checker explicitly supplies and verifies one A per row.

In those representatives, for the fifth coordinate W_A is ±6 or ±4; this forces the two sections of B, of sizes n and 14−n, to have n=7 or n=6, respectively, after a possible interchange. Translating B arbitrarily while leaving A fixed is an affine shear of the six-space. Thus its first section in F₂⁴ may be replaced by its smallest 16-bit mask under translations of F₂⁴. The other section is **unrestricted**. For every such pair the checker tests all remaining Walsh sums by the preceding exact two-sign rule, with no assumptions on the graph's symmetry.

## Two local pair counts finish the screen

Every pair of points in S has exactly two actual block completions, which give two different unordered pairs with the same nonzero difference. Thus a difference occurs either zero times or at least three times among the 231 pairs. For every surviving S list all affine planes contained in it, dropping any plane contained in one of the 21 eight-point cuts. We deliberately impose only necessary conditions. If a pair has fewer than two remaining options, reject. For every pair with exactly two options, **both** planes are mandatory. If their union as a set of distinct planes has more than 77 elements, reject. These two tests reject every remaining S:

| Dependence weights | Walsh completions | After difference count | Pair deficient | 78 mandatory | 84 mandatory |
|:--|--:|--:|--:|--:|--:|
| 4,4,4 | 73,328 | 120 | 96 | 24 | 0 |
| 4,4,6 | 93,360 | 156 | 84 | 72 | 0 |
| 4,4,8 | 57,960 | 576 | 552 | 0 | 24 |
| 4,6,6 | 58,872 | 48 | 0 | 48 | 0 |

Run `python3 hoffman_binary_nullity_six.py` (Python 3.10+ and NumPy). The integer checker regenerates all rows from the four explicit eight-sets; no external graphs, solver, floating tests, cover search, or precomputed representatives for the 14-sets are used. This excludes dimension seven.

