# Size 68 over F_17³: degree-eight moments vanish

Assume the size-68 reductions: [moments through seven and no full planes](FugledeF17Size68MomentSeven.md), [uniform-pencil cap eleven](FugledeF17Size68PencilCapEleven.md), [the exclusion of low-degree members](FugledeF17Size68LowDegree.md), and [four-blocking under a nonzero degree-eight form](FugledeF17Size68DegreeEightGeometry.md). In particular line cap is four, and projections modulo 17 are the actual least residues. This note excludes all genuine octic profiles, not the size-68 cardinality.

## Sharper plane cap and the incidence of small secants

Every plane slice of a member determines only directions in the opposite uniform-normal pencil. Since that pencil has at most eleven sites, the integer planar search [verify-fuglede-f17-size68-plane-cap.js](verify-fuglede-f17-size68-plane-cap.js) applies: a cap-four set determining at most eleven directions cannot have thirteen sites (1,090 direction masks, 8,944,556 visits, zero final cases). Thus both members have plane cap 12.

That verifier also finds no six-site cap-four planar set with at most five directions (21 masks, 204 visits). In particular, a projective line with four or five uniform normals for one member has a polar normal whose opposite plane slices each have at most five sites. The cap-five occupancy catalogue in the degree-eight geometric note shows that this polar normal is either uniform, or is a genuine octic of the form 4±(t−h)^8 and weight 8/17. If the line has four or five uniform sites and the pole is nonuniform, it is a tight center with, respectively, fourteen or thirteen positive neighbors.

For the notation of the lower-degree proof, W=570 is the total nonuniform profile weight, and C=26 is the total weight on every tight pencil. Every tight pencil has at least eight positives: fewer than seven is impossible by the uniform-pencil cap, and a pencil with exactly seven positives would have degrees at most five by the Radon degree bound. The exhaustive quintic tight-pencil calculation in the low-degree note excludes it, independently of the maximum degree of the member outside that pencil.

A positive profile of degree at most eight has at least nine positive occupancies (root count); the cap is 12 and the mass is 68. The extremal concentrated occupancy has 12^5,5,1^3 and square sum 748. Thus each weight (sum of occupancy squares minus 272) / 34 is at most 14. For a profile of degree at most seven there are at least ten positive occupancies, so the extreme vector is instead 12^5,4,1^4 of square sum 740; such weights are integers, so are at most 13. These extreme vectors maximize cumulative partial sums of the sorted occupancy list subject to the cap, mass and lower bound on positive entries.

## One member with octics cannot face one without them

If B has a genuine octic, its degree-eight moment form vanishes precisely at the uniform and lower-degree normals, and is nonzero. A tight pencil seeing an octic thus has at least ten positive profiles by the homogeneous Radon relation; one not seeing an octic is an entire rational line factor of the form, so there are at most eight such tight exceptions. Relative to positive degree count ten, their deficits are at most two. Writing N for B's number of nonuniform normals, the weighted row count gives
```
26 N ≥ 10·570 − 16 M
```
where M is an upper bound on the opposite weights. If the opposite member has no octic, M≤13, giving |U_B|≤95. Its opposite uniform support has size at most 131, from weighted incidence and the universal tight positive count at least eight: 26·|V_opposite|≥8·570, so |V_opposite|≥176.

The degree-eight geometric proof gives four-blocking for U_B. Write U=|U_B| and n_L=|L∩U_B|. Projective incidence gives
```
Σ_L (n_L−5)(n_L−8) = U²−217U+12280.
```
A nonfactor line has at most eight zeros and gives a positive term only when n_L=4, yielding 4. Each of at most eight factors with n_L>8 contributes at most 18 because n_L≤11. The right side decreases for U≤95 and is 690 at U=95. Therefore the number of four-secants is at least ceil((690−144)/4)=137. Since the opposite has no octics, their distinct poles all lie in its uniform set, which has size at most 131. Contradiction.

## Both members with octics: exact line-count and weight comparison

With both members octic, the preceding weighted bound with M=14 implies |U|≤96 for both. Let U denote the first size, V the opposite, and h9,h10,h11 count projective lines containing 9,10,11 points of the first uniform set. Their sum is at most eight because all such lines are factors of its degree-eight form. All remaining lines meet the uniform set in 4..8 points. Write a and b for the counts of four- and five-secants. The first two incidence moments are exact:
```
Σ_L n_L=18U,   Σ_L n_L(n_L−1)=U(U−1).
```
After removing the h lines put
```
K = 307−h9−h10−h11,
T = 18U−9h9−10h10−11h11,
Q = U(U−1)−12·18U+42·307−6h9−12h10−20h11 .
```
Here Q is the sum of (n_L−6)(n_L−7) over the remaining lines. Their counts n8,n7,n6 at sizes 8, 7, 6 are therefore uniquely specified by
```
n8 = Q/2−3a−b,
n7 = T−6K−Q+8a+3b,
n6 = K−a−b−n8−n7.
```
All five counts are nonnegative integers.

A tight center with fewer than ten positive neighbors must have eight or nine; its polar line has ten or nine uniform points respectively. The total unweighted deficit relative to ten is therefore at most h9+2h10, and its total weighted deficit at most 14(h9+2h10). For positive excess, at most V of the a+b small-secant poles are uniform in the opposite member. Every other such pole is a tight center of weight 8/17, with excess at least three, and excess four if it came from a four-secant. Thus a necessary inequality is
```
17[26(307−U)−5700] + 238(h9+2h10)
  ≥ 8 [3 max(0,a+b−V) + max(0,a−V)] .
```

The integer verifier [verify-fuglede-f17-size68-octic-line-count.js](verify-fuglede-f17-size68-octic-line-count.js) enumerates all h counts, tests every U from 0 through 96 and all possible a. Nonnegativity of n8,n7,n6 gives an interval of admissible b; testing only its least integer is sufficient because the right-hand side of the inequality is nondecreasing in b. For any retained counts, the required V is monotone and the verifier finds its minimum by binary search. Across all U≤96, the only U that admits any counterpart V≤96 is 87, and it requires V≥96. The reverse inequality at U=96 is impossible. There is therefore no mutually compatible pair. This rules out the last octic case and proves mixed moment vanishing through degree eight.
