# Rank 40 excludes the last two-type shell pattern

If the graph Seidel matrix has rank 40 modulo seven, it cannot have only neutral norms 18 and 24 among the twelve selected unit types. Combined with the earlier two-type screening, rank 40 therefore needs at least three of those types. This does not exclude rank 40 itself or the last two-type face at rank 42.

## Per-extension inputs

Suppose the two-type face holds. For a maximal isotropic seven-subgroup H write W(a,t) for its usual folded count, and M_H=W(2,22) for its number of eligible Hoffman cocliques. We suppress H in the W notation. The [short-shell identities](higher-moments.md#if-only-norm-18-and-norm-24-occur), after [the Fano endpoint exclusion](two-type-no-fano.md) gives W(0,14)=0, are
```
6 W(0,18) = 93 + 2 W(1,23) + 5 M_H,
6 (W(0,24)−W(3,35)) = 45 + 13 W(1,23) + 34 M_H.
```
Eliminating W(1,23) yields the exact equality
```
4 (W(0,24)−W(3,35)) = 26 W(0,18) + M_H − 373.           (1)
```
These are necessary identities for each actual H, not an assertion about a single averaged formal control. The [marked Hoffman-coclique reductions](two-type-true-hoffman.md) show M_H=1 for every H on this face (the earlier scalar bounds left the values one and three; the charge-(2,34) two-hit argument rules out the latter).

We also use the [projective class balance](two-type-residue-balance.md). In each of the shells (0,18), (0,24), (3,35), the sum of the populations in opposite classes is equal over the four opposite pairs inside each residual anisotropic plane. For the neutral shells, populations of the individual opposite classes also agree by negation, so each individual count is W(0,t). For positive charge three the count in an opposite *pair* is 2W(3,35); equality of the two members separately is not required.

## A finite incidence congruence

In rank 40 the original seven-discriminant space with its raw norm is a nonsplit nondegenerate four-dimensional quadratic space over F7. It may be written
```
V=F7^4,     Q(x)=x1²+x2²+x3²+3x4².
```
The associated dot product has the same diagonal coefficients. Its nonsquare determinant gives the required minus type in dimension four. The raw value of the seven-class of a charge-a, norm-t marking is t−11a²/9 modulo seven: equivalently use seven times the squared norm of its graph vector, on which the denominator nine is a seven-adic unit. Thus Q has value 4 at (0,18), and 3 at both (0,24) and (3,35).

There are 50 maximal subgroups H, the isotropic lines of V. Eligible original classes are those in H-perp; dropping H gives the residual anisotropic plane H-perp/H. Fix a nonzero q in {4,3}. There are 350 vectors of Q-value q in V and hence 175 opposite pairs. For each H and one residual pair {beta,−beta} of value q, the original classes over beta form a line x+H of seven vectors. Pairing each with its negative gives seven distinct opposite pairs in V. The four residual opposite pairs give four such seven-subsets. The [standard-library verifier](rank40_two_type_tangent_deck.py) constructs the sets directly; it checks all these sizes.

For an array of counts X on the 175 pairs, suppose those four line sums in each H have a common integer value L_H. Then
```
sum_{H} L_H = 0 modulo seven.                              (2)
```
This is a finite linear identity, not a uniformity assumption about different H. To check it, set up four rows per H on 175 variables X and 50 variables L. A row has ones in the seven relevant X columns and minus one at H. Exact Gaussian elimination modulo seven has 124 pivots amongst the X columns and one further pivot. The last reduced row is precisely 175 zeros followed by 50 ones, for each of q=4 and q=3. The verifier uses integer residues only, no external algebra package or graph search. Normalizing each isotropic generator by making the first nonzero coordinate one lists every H once; choosing the lexicographically smaller of x and −x labels an opposite pair, not a group symmetry of the graph.

Apply (2) to actual graph counts on the original classes. In either neutral shell let X_{[x]} denote the number in the *single* class x, which is the same for −x. Then the line sum is W(0,t). In positive charge three take X_{[x]} to be the *sum* of the counts in x and −x; its line sum is 2W(3,35). The original graph markings used in these definitions do not depend on H, since passing to H only tests orthogonality and changes their residual class. Consequently each of
```
sum_H W(0,18),      sum_H W(0,24),      sum_H 2W(3,35)
```
vanishes modulo seven. In particular the entire left-hand side of (1) vanishes after summation, with no need to reduce a half-integer. The right-hand side modulo seven is 50(1−373)≡6, a contradiction.

Even before using the M_H=1 theorem the same argument forces ∑ M_H≡2 mod7, hence the number of M_H=3 extensions would have to be 4 modulo seven. It is the additional graph-level exclusion of M_H=3, not the scalar congruence alone, that closes the two-type case at rank 40.
