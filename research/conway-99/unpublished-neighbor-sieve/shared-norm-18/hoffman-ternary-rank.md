# Ternary kernel of the point--block design of a Hoffman coclique

Let C be a 22-coclique. Its 77 outside vertices give 77 four-element blocks on C; any pair of points lies in two blocks. The blocks are distinct since distinct vertices cannot have four common neighbors. In fact the following holds in any simple 2-(22,4,2) design; it does not use the modular shell hypotheses. Write D for its 22-by-77 incidence matrix and K for the kernel of D-transpose over F3.

**Theorem.** The only possible nonzero weights in K are 12, 15 and 18. Weight 12 or 18 is balanced: its standard lift to 0,+1,−1 has equally many signs. Weight 15 has 9 of one sign and 6 of the other, or is a constant-sign word. At most one constant-positive weight-15 word exists. Moreover dim K ≤ 3, i.e. D has ternary rank at least 19. In the constant-sign case dim K=1 exactly.

Let the standard lift z have p positive and q negative sites, w=p+q and s=p−q. We have DDᵀ=12I+2J, and each point occurs in 14 blocks. The sum of the block sums implies 3 divides 14s, hence s. Each block sum is 0,+3 or −3, and its square is a multiple of nine. Thus 9 divides zᵀ DDᵀ z=12w+2s², giving 3|w (in fact the kernel is self-orthogonal by polarization). A nonzero site must have at least one further nonzero site on all 14 blocks through it, each pair occurring twice, so w≥8.

Let b+ and b− be the numbers of blocks of sums +3 and −3. A +3 block consists of three positive sites and one zero; similarly for −3. Every positive site belongs to 4+2s/3 positive-sum blocks and none of negative sum, by the corresponding entry of DDᵀ z. Similarly each negative is in 4−2s/3 negative-sum blocks. Comparing 3(b+−b−)=14s with the two expressions obtained by summing over sites gives (w−15)s=0. This excludes weight 9 and 21, since these are odd and could not be balanced, as well as all other weights except 12,15,18. At weight 15 when both signs occur, their nonnegative triple incidences give |s|≤6, hence |s|=3. Distinct all-positive weight-15 words have nonzero difference of weight at most 14 and hence exactly 12; their seven-element zero sets meet once. Their sum would then have forbidden weight 21. Thus the number f of positive constant-sign words is 0 or 1. An all-positive word has a 7-site complement meeting every block in 1 or 4 (or equivalently the 15-set meets each in 3 or 0). The seven four-blocks within its complement are the complementary Fano blocks there. They are mutually nonadjacent graph vertices since their point sets pairwise meet twice. Replacing the seven complement points of C by these seven outside vertices gives the familiar 15-overlap switch of cocliques.

If the positive weight-15 word exists, the seven block columns on its zero set form a 7-by-7 complementary Fano design. Its Gram 2I+2J is nonsingular over F3 (eigenvalues 2 and 16). Therefore every ternary kernel vector vanishes on these seven coordinates. For any word independent from the pure word, its three translates by multiples of the pure word would all have weight at least 12, but their weights sum to 30 (two contributions per remaining coordinate). Hence dim K=1. The Fano 15-overlap switch itself is already described in [the coclique shell argument](../../marked-coset-shells/README.md); the ternary rank statement is separate.

For the remaining dimension bound, use any basis of K of dimension k, so its 22 coordinates are columns of a generator in F3^k. Let z0 be the number of zero columns. Group the nonzero columns by projective direction into multiplicities (a,b) at two opposite vectors. For a uniform linear functional x, let L(x) be the number of coordinates where the word has value +1. For every nonzero x apart from the 2f exceptional constant-sign words, L=6 or 9. At x=0, L=0. At the two exceptions it is 0 or 15. Therefore
```
E[(L−6)(L−9)] = 54(1+2f)/3^k .
```
A nonzero column has probability 1/3 of value +1. Two columns in distinct directions have joint probability 1/9; two equal columns have probability 1/3 and two opposite columns have joint probability zero. Substitution and rearrangement give
```
z0(z0+1)/2 + sum(a²+b²−ab) = 10 + 243(1+2f)/3^k.      (*)
```
The left side is at least 11, half the total number of coordinates. Indeed a²+b²−ab ≥(a+b)/2 with equality only at (0,0) or (1,1), and z0(z0+1)/2≥z0/2 with equality only at z0=0. If f=1, a linear functional is +1 on 15 columns and −1 on none, so each of those 15 occurs in an unpaired direction and contributes at least 1 per coordinate rather than 1/2. Thus the left side is at least 19; for k≥5 the right side is at most 13. If f=0, (*) gives k≤5. At k=5 equality forces eleven distinct projective column pairs, each taken once in each orientation.

In that exceptional case select one generator column from each pair. This is an [11,5] ternary linear code with all nonzero weights 6 or 9. The total number of words is 243 and the total weight 11·162, so the counts are 132 and 110. Its dual has no nonzero word of weight below 5, as follows directly by expanding
```
((1+2X)^11 + 132(1+2X)^5(1−X)^6 + 110(1+2X)^2(1−X)^9)/243 .
```
This is the elementary ternary MacWilliams transform, or the character sum over the code for the dual weight enumerator. Consequently any four distinct original columns summing to zero must consist of two whole opposite pairs: otherwise after cancelling complete pairs and collecting signs there would be a nonzero relation on at most four of the eleven selected directions. Every block has zero column sum, so every block through any point would also contain its opposite mate. That pair would occur 14 times instead of two. Hence k≤4.

## Excluding dimension four when there is no pure word

Suppose k=4 and f=0 in (*). The half-coordinate lower bound 11 has excess exactly 2. The zero columns consume z0²/2 of this excess. Each used nonzero projective direction can only have unordered multiplicities (1,0),(1,1),(2,1),(2,2), with excess respectively 1/2,0,3/2,2. All other directions have multiplicities (0,0). The [standard-library verifier](hoffman_ternary_rank.py) enumerates the six multiplicity distributions by these equalities and the total 22.

To screen them, write n=22−z0 and let P be the number of unordered pairs of nonzero columns in the same projective direction, summing binom(a+b,2). For a uniformly random functional, its weight V has E[V]=2n/3 and E[V²]=(4n²+2n+4P)/9 by the single/pair probabilities. Together with A12+A15+A18=80, these determine the weight counts. The total Z of zero-sum four-subsets of columns is the average over all 81 functionals of the coefficient of x⁴ in
```
(1+x)^(22−V) (1+ωx)^p (1+ω²x)^q,  ω³=1, ω≠1.
```
Indeed averaging the character of any nonzero sum gives zero. One can use real parts; they agree for (p,q) and (q,p). There are H unordered pairs of opposite columns (including pairs of zero columns), obtained by summing h=ab over nonzero directions and h=binom(z0,2) for the zero group. A zero-sum four-subset containing one such pair consists entirely of two such pairs. Their number T is the sum of h_i h_j over distinct groups plus binom(z0,4) and the within-group counts binom(a,2)binom(b,2). At most H of these T four-subsets can be actual blocks since every one consumes at least two opposite pairs and each pair occurs just twice. Therefore the 77-block design needs Z−T+H≥77. In the ordering (z0, #10, #11, #21, #22), the six capacities are:
```
(0,0, 9,0,1):55    (0,1, 9,1,0):68    (0,4,9,0,0):80
(1,0, 9,1,0):70    (1,3, 9,0,0):82    (2,0,10,0,0):71.
```

Both survivors consist of nine fully paired directions plus four unpaired single columns, or one zero and three unpaired single columns. The sum of the unpaired columns is zero since all kernel words have coordinate sum divisible by three. In the three-single case they can be normalized by an invertible basis change to e1,e2,−e1−e2. In the four-single case they span exactly three dimensions. Indeed in a two-space four points in distinct projective directions would use all four directions e1,e2,e1+e2,e1−e2; no choice of signs makes their sum zero (the first-coordinate sum forces the three corresponding signs equal, contradicting the second-coordinate sum). Their sum-zero relation precludes four dimensions. Thus, after reordering, use e1,e2,e3,−e1−e2−e3. These are basis normalizations on a putative ternary code, not graph automorphisms.

There are 40 nonzero projective directions in F3⁴. From the directions not used by the singles, take every 9-subset of paired directions. As K is self-orthogonal, the sum of vvᵀ over the 9 paired directions equals the sum over the singles modulo three. The verifier obtains precisely all such subsets by dividing the available list in two and matching subset sizes and the ten independent Gram entries; this is an exhaustive factorization of the subset test, not random sampling. It checks the two permitted positive counts on every nonzero functional and constructs all zero-sum four-subsets by matching pair sums with their negatives, storing each sorted four-subset once. Irrespective of possible adjacency, every point pair must be in at least two of those four-subsets.
```
z0   normalized Gram candidates   min #possible blocks of any pair
0             486                  0 in 162 cases; 1 in 324
1             648                  1 in all 648
```
This exhausts both shapes. Thus rank D modulo three is at least 19. Run `python3 hoffman_ternary_rank.py`; the full finite part takes about two seconds and uses only integer arithmetic and fractions.

**Collision consequence.** In the two-type problem suppose t is an eligible norm-18 signed field perpendicular to C with kappa=3 positive and three negative sites on C. Let z=t|C, viewed as a field extended by zero to the full graph. Put w_t=3t−(3I−A)z, zero on C. On its 77-point complement w_t reduces modulo three to Dᵀz. Thus w_t=w_u implies z_t−z_u belongs to K. If the two six-site C supports intersect then their union has at most 11 sites, so the difference vanishes modulo three; since the entries are signed units, this implies z_t=z_u. Equality w_t=w_u then gives t=u. Accordingly each w has at most three preimages (their six-site C supports are disjoint). A repeated residual yields a ternary weight-12 word with exactly six of each sign. No conclusion of nonexistence follows from this alone.
