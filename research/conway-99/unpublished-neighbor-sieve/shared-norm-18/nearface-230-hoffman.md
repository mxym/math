# Exactly three compatible cocliques force no extra unit (1,23) marks on the U230-only augmentation

The [subsequent signed/unsigned argument](nearface-230-exclusion.md) excludes this entire support. This note is the intermediate three-coclique identity.

Fix one determinant-49 maximal extension H and suppose all its selected unit types except neutral norm18, neutral norm24 and (2,30) are absent. The oriented eligible norm14 population F is zero and the number M of eligible Hoffman cocliques is at most three. Indeed the [scalar certificate](nearface_230_scalar.py) uses the full **fixed-H** inequality 2D≤3L+(75/2)S+(525/4)F from [the blocked-edge proof](nearface-four-exclusion.md); that estimate requires only N16=N20=U125=0, which holds here (U230 is not required absent). With the same rational constants its resulting tangent is T_j=35Z+(420−176j)n+25V+105L+(2625/2)S+(18375/4)F+88j²≥0. Positive row combinations yield 100443F≤170208 and 6977520M≤27851472; F is even by antipodality and M integral. Suppose now M=3. The latter are three genuine distinct charge-two fields c=−1_C in the zero residual class; this is not an average over several maximal extensions. Then the extra positive-charge signed-unit (1,23) population S=W123−99 is zero. In particular, N18(H)=408; every residual-zero neutral norm28 is signed-unit, by the inverse single-site correspondence in [the four-family exclusion](nearface-four-exclusion.md). This rules out M=3 with S>0, not M=3 itself, the whole selected support, or any rank.

Use the [existing true-C chart](two_type_true_hoffman.py) independently for each of the three c, this time keeping raw (2,30). All other exclusions there remain valid: the absence of N16 and U226 accounts for the other nonunit sources, so raw (1,27) consists exactly of nine single-site translates per N18 field. Further each eligible norm18 is orthogonal to c since a nonzero pairing, necessarily ±7, gives an excluded (2,26) translate. Thus the only (1,27) angles on c are −3,4. For a fixed true c the angular slots K(a,t,d) are the original chart's residue-averaged signed counts (the nonisotropic true populations are divided by eight); write K below for their arithmetic average over the three actual marks, not over graphs. Isotropic W and K are literal counts before averaging.

The [native exact span check](nearface_230_hoffman.py) gives
```
237−86 S =
 9K(4,46,2)+18K(2,22,8)+9K(2,34,1)+72K(1,23,11)
 +20K(1,29,11)+2K(1,29,4)+2K(1,29,−3)
 +27(K(1,23,4)−77)+6(W234−3K(2,34,−6)).
```
The single-axis identity holds for each c even if its last displayed grouped term is negative; then average all three. The 77 ordinary marks from sites off C give K(1,23,4)≥77. Distinct cocliques C,D intersect in 1 or 8 because F=0 (the otherwise permitted 15 would produce norm14). A (2,34) field b cannot have angle −6 to both: folding b+c+d+1 to charge −3 gives squared norm 21+2|C∩D|, either 23 below the charge-three minimum or 37, whose fields are signed-unit and forbidden here. Consequently the three distinct marked −6 slots total at most all (2,34) fields, giving W234−3K(2,34,−6)≥0, with the normalization the same for all four quantities. Thus S≤237/86<3.

To see the exact divisibility directly, the native scalar quadratic relation on this support at F=0 is 6n=291+2S+5M, n=N18(H)/8; equivalently 3N18(H)=4(291+2S+5M). Hence S+M≡0 modulo three, without assuming equality of any projective populations. At M=3 this gives S=0 and N18(H)=408.
