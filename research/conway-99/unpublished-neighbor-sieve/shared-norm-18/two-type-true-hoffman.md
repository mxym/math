# Marking an actual Hoffman coclique leaves four two-type tuples and a unique coclique in every extension

Fix a maximal determinant-49 extension in the remaining two-type case (only neutral unit norms 18 and 24 among the twelve selected types), at rank 40 or 42. Write M for its number of eligible 22-cocliques, S for its eligible unit charge-one norm-23 labels, n for its size of each signed norm-18 residue class, and W234 for the usual raw folded population. Then only the following necessary tuples remain:
```
(M,S,n,W234) = (1,2,50,129), (1,5,51,102), (1,8,52,75),
                (1,11,53,48).
```
These are arithmetic/geometric restrictions, not a proof that any listed population is realized.

## A universal marked identity on this face

By [the preceding short-count theorem](two-type-short-counts.md) and [the Fano endpoint exclusion](two-type-no-fano.md), M is 1 or 3 and W014=0. Choose **any actual eligible** 22-coclique C; set c=−1_C. For charge a≥0, cost t and integer δ write K(a,t,δ) for eligible fields b with b·c=δ in this fixed extension. Divide counts by eight when the seven-residual quadratic value is nonzero and by one otherwise, exactly as for W. Thus Σ_δ K(a,t,δ)=W(a,t), on the same normalization **separately for every** marked C. Counts at charge zero include both orientations. The following quantity is nonnegative:
```
V_C = K(4,46,2) +2K(2,22,8) +2K(2,34,8) +3K(2,34,1)
      +8K(1,23,11) +2K(1,29,11) +3[K(1,23,4)−77].
```
The last bracket is nonnegative without any assumption on field symmetry. The 99 distinct ordinary d_i=(3I−A)e_i have charge one, cost 23 and zero seven-class since 3u_i belongs to the original lattice. Their inner products with c equal 7c_i+4, so exactly the 77 indices outside C give δ=4 at this isotropic quadratic value (no division by eight).

The new identity is
```
3V_C = 1173−320M−62S.
```
It excludes (M,S)=(1,14) and (3,6), giving V_C=−5 and −53 respectively.

## Exact derivation and scope of the mark

For any field b the corrected vector is b°=b+(a/9)1, of squared norm t−11a²/9. For c, c°²=154/9 and 9 b°·c°=9δ−22a. The original seven-class of c is in H, hence orthogonal to every eligible graph field at seven. Therefore δ≡4a (mod 7), and Cauchy gives (9δ−22a)²≤154(9t−11a²). The finite enumeration ranges over all |δ|≤√(22t), already valid by uncentered Cauchy.

Adding jc and folding by v=floor((a+2j+4)/9) sends the data to
```
a'=a+2j−9v,
t'=t+22j²+2jδ−22(a+2j)v+99v²,
δ'=δ+22j−22v.
```
These bijections, and negation (a,t,δ)→(−a,t,−δ), preserve the normalized populations: c changes the original seven-class by an element of H, so the residual class in H-perpendicular/H is unchanged. A finite range of actual bijections suffices. The enumerator merges signatures only when a signed translate coincides. Each candidate and its checked translates must obey parity, t≥11|a|, the neutral/affine minima, and the absent raw types (0,16),(0,20),(0,26),(1,21),(1,25),(2,26),(2,28),(2,30),(3,37). In particular raw norm26 and raw (1,25) vanish because their nonunit sources (1,21) and (0,16) vanish. The (1,27) shell is **not** discarded: every one of its fields is an N18 translate at one of its nine negative sites, so W127=9W018. Every N18 has δ=0: a potential ±7 gives charge two, norm26 upon a signed coclique shift and a lift of larger magnitude gives cost below 22. It follows that its (1,27) translates have δ=−3 or 4, by d_i·c=7c_i+4. These are precisely the additional low-angle restrictions. The fixed marking forces K(2,22,22)=1 (C itself), K(2,22,15)=0 (the difference would be Fano), and W014=0. There is no fixing of the overlap-one/overlap-eight counts or of the other short populations in this linear identity.

The universal omission of charge ±2 and cost 24 can also be checked directly: the exceptional entry is −2 or +1 in charge +2 orientation. A −2 translates to charge three and cost 27, impossible. If the exceptional entry is a +1 at p, then p has eight negative neighbors. The 23 negative sites have internal degree one if adjacent to p, and zero otherwise. The eight negative neighbors of p thus occupy four pairs in the neighborhood matching. The 15 other negative sites each share two neighbors with p, necessarily among its six zero neighbors. Three pairs among those six are adjacent and already share p, leaving only 12 allowed pairs. Each allowed pair can be used at most once, a contradiction.

Use the four [even unimodular rank-48 gluings](higher-moments.md) for this same H. In the graph-coordinate realization a projected lattice vector has graph part b°/√7. For actual c take graph axis 9√7 c° and add an auxiliary axis 3h, so the total squared length is 9702+9hᵗBh, B the upstream auxiliary Gram matrix. Against an auxiliary numerator w at scale s=1 or 3 the full inner product is 9δ−22a+(3/s)w·h. Averaging over the residual anti-isometries gives exactly K above because c has zero terminal residual class; there is no averaging over the location or structure of C. The rank-48 harmonic shell identities are those of [the single-site computation](site-degree-ten.md), now with this actual axis. For degrees d=2,4,6,8 use the monic zonal harmonic with coefficient recurrence c_(l+1)/c_l=−(d−2l)(d−2l−1)/(2(l+1)(48+2d−2l−4)). If f,g,h₃ are its norm-2,4,6 shell sums, at d=2 one has g+48f=h₃+195804f=0, and for d=4,6,8 respectively h₃=151740f+192g, −99180f−552g, 50220f+432g.

The [native exact verifier](two_type_true_hoffman.py) generates all graph-chart types needed for each of the four gluings, reverses the four inherited raw/unit substitutions, and imposes the actual-axis rows at the indicated three harmonic shells. The result has 191 signed positive-charge/neutral angle slots, identified into 116 variables. The coefficient matrix with constants has rank 105 and includes
```
3K446,2+6K222,8+6K234,8+9K234,1+24K123,11+6K129,11+9K123,4
 +320W222+62W123 = 8004.
```
Subtract the ordinary-mark lower constant 9·77 and substitute W123=99+S to get the stated identity. No floating point or control profile enters the proof.

## Pool across all three actual cocliques, with the division by eight unchanged

For a charge-two norm-34 field b, the only possible δ against an eligible C are −6,1,8. Indeed δ≡1 mod 7. At δ≤−13, b+c would have charge four with cost 56+2δ≤30<44. At δ=15, b−c has neutral norm 26, ruled out including its nonunit part; at δ=22 it has the impossible neutral norm 12, and larger δ make the cost negative. At δ=−6, b+c has charge four, cost 44, so every entry of b+c is 0 or −1. Consequently b has only 0 and +1 on C, only 0 and −1 off C, and its cost and sum give exactly six positives and 28 negatives. In particular **all six positive sites belong to C**.

No field can have δ=−6 at two distinct eligible cocliques C_i,C_j. For c_i=−1_{C_i}, k=|C_i∩C_j|, the field f=b+c_i+c_j+1 has charge −3 and norm
```
34+22+22+2(−6−6+k)−132+99=21+2k.
```
Here k=1 or 8: seven-orthogonality gives k≡1 (mod 7), and k=15 would put c_i−c_j in the absent Fano shell. Thus the norm is 23 or 37. The former is below the charge-three mass floor 33. At the latter norm, every field is unit: negate to positive charge three and, at an entry ≥2, subtract d_i to obtain charge two and cost ≤20; at an entry ≤−2, add d_i to obtain charge four and cost ≤44, which must be all nonpositive units at equality although the marked entry then equals +1. If the entry is ≤−3 the cost is already <44. The unit (3,37) type is absent on this face. All translations are equalities in the graph field group, not just in a formal theta cone.

Therefore if M=3, each (2,34) field contributes at least twice to the angles 1,8 among all three marks. The normalization 1/8 is unchanged for each C, so
```
Σ_C V_C ≥ 2 Σ_C[K(2,34,1)+K(2,34,8)] ≥ 4W234.
```
At S=3 this requires 27≥144; at S=0 it requires 213≥252. Both are impossible. The program checks all eight input tuples via 6n=291+5M+2S and W234=189−42M−9S, leaving exactly the four listed at the top. Run `python3 two_type_true_hoffman.py` alongside higher_moments.py, with its existing dependencies and SymPy. No independence of different extensions is assumed.

## Actual graph implications on this two-type face

Every maximal determinant-49 extension contains exactly one eligible Hoffman coclique. At rank 42 it is the unique one in the graph. At rank 40 the isotropic lines in the four-dimensional minus-type original seven-discriminant space are the 50 maximal extensions. Every coclique has isotropic residual value, so a graph coclique with zero original seven-class is eligible in all 50 extensions; a nonzero one is eligible in precisely its own line. Writing m for the former count and u for the latter gives 50m+u=50. Equivalently the actual graph either has a unique Hoffman coclique of original seven-class zero, or has exactly 50, one on each distinct nonzero isotropic line. This argument uses that in Witt index one two distinct isotropic lines cannot be orthogonal. It neither assumes nor constructs a graph.
