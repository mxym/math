# The Jacobi theta series at the unique Hoffman coclique is determined by eight short counts

Assume the rank-42 remaining two-type face: among the twelve selected unit types only neutral norms 18 and 24 occur. Let L be the even rank-44 graph lattice of determinant 49 and C the [unique Hoffman coclique](two-type-true-hoffman.md). Write c=−1_C. In the notation of that link put K_at(d) for the eligible charge-a, cost-t fields b with b·c=d, dividing by eight for a nonzero residual quadratic value and by one at zero. W_at denotes the sum over all d. Rank 42 has a single maximal seven-extension, namely the original L. This result assumes no graph automorphisms.

**Theorem.** Put w=−3c°/√7, where c°=c+(2/9)1. Then w belongs to L, w²=22, and the entire two-variable theta series
```
φ(τ,z) = Σ_{v∈L} q^(v²/2) ζ^(v,w),    q=e^(2πiτ), ζ=e^(2πiz),
```
as well as its dual-cusp theta data, are determined by
```
W018, W022, K333(5), K123(−3), K123(4), K024(−7), K335(5), K127(−3).
```
The normalization W000=1 is fixed. These are sufficient parameters, not an assertion that they can be chosen independently or that any values are realized. This full-series uniqueness is not nonexistence of the two-type case.

## Original charge and angle at the two cusps

The [graph dictionary](../../maximal-marked-lattice/README.md) identifies vectors v of L* with folded fields b of charge a=0,3,−3 by v=b°/√7, b°=b+(a/9)1. Their dual Fourier index j=7v²/2 is integral, with t=2j when a=0 and t=2j+11 otherwise. Across the lattice the residue at seven is anisotropic, so v belongs to L exactly when 7 divides j. The negative charge is the negative of the positive charge-three contribution. Multiplying c°/√7 by −3 gives an allowed charge field (fold by a constant), hence a dual vector; its squared norm is 9·(154/9)/7=22, so it is in L by anisotropy. In particular it is primitive since L is even and 22 is square-free. For a canonical v above and d=b·c,
```
r=(v,w)=[22(a/3)−3d]/7,    r ≡ a/3 (mod 3).
```
The integer Fourier angle r hence separates all three signed folds and determines d at fixed charge. All normalized K counts are restored to raw counts by multiplying by eight for 7∤j and by one for 7|j. At the original cusp the index is s=v²/2=j/7; no multiplier eight is used. This also explains one meaning of the first short populations: w+3L has a unique shortest vector of norm 22, and exactly 99+S vectors of norm 28. Indeed this coset contains the three raw original-zero classes of affine charges 1,−2,4 after multiplication of their corrected graph vectors by three (those charges differ by three and the residual class is zero). The squared norm of a member is (9t−11a²)/7. The charge minima, the zero seven-class, and that formula give norm 22 only for a=−2,t=22, and norm 28 only for a=1,t=23; a=4 cannot contribute a smaller norm since its first eligible cost is 46. This interpretation is not needed in the uniqueness argument.

## Finite linear determination

The [exact verifier](two_type_hoffman_jacobi.py) uses costs from the four rank-48 auxiliary charts and, in addition, every canonical pair (0,2j),(3,2j+11) for 0≤j≤35. For each it includes every integer d with |d|≤√(22t), d≡4a modulo seven, and (9d−22a)²≤154(9t−11a²). The signed translations by multiples of c, raw cost cutoffs, charge minima, orthogonality of N18 to c, and its one-site (1,27) translates are exactly those of the [actual coclique identity](two-type-true-hoffman.md). The only additional absences used here are N14=0 and M=1, so that (2,22) can occur only at d=22. There are 218 orbit unknowns. For normalized homogeneous equations impose W222=W000 and W127=9W018, the [auxiliary norm-2/4/6 identities](higher-moments.md), and the same true-axis harmonic equations through even degree 10 as in the actual-coclique computation. No test treats a formal numerical control as a graph.

For each even h=0,2,…,18 let Z_h(u,s) be the dimension-44 zonal harmonic with leading u^h, with trace parameter s=||v||²||axis||². The recurrence (up to an irrelevant common integer multiplier) is given in [the original two-cusp calculation](original-site-populations.md). At the dual chart X=√7 L*, take the axis √7 w. At index j the harmonic value is
```
Z_h(7r,308j).
```
The original-cusp chart at index s uses the very same expression at j=7s, thereby evaluating on √7 times an original vector. In particular this second chart is 7^(h/2) times the harmonic theta of L with the same axis √7w.

For k=22+h, harmonic Poisson summation places the first chart in M_k(Γ₀(7)) of trivial character: the even lattice X has level 7 and square determinant 7^42. The second is **minus its Fricke transform times 7^(10+h/2)**. For fixed axis the normalized weight-k Fricke transformation of the theta of X into that of L contributes −7^11/√det(X)=−7^(−10) in even harmonic degree; the extra 7^(h/2) in our second chart is the preceding vector scaling. As in [the original Fourier chart](original-site-populations.md), use products of two odd-weight level-seven Eisenstein forms with the quadratic character placed on either factor. The standard dimension is 1+2⌊k/3⌋; the checker obtains that many independent first-cusp columns. It then identifies the paired Fourier data through j=35 on the first cusp and s=5 on the second. It performs the computation over the prime field of order 1,000,003: all denominators used are units, and each echelon pivot is verified. Thus the corresponding rational Fourier coefficient matrices have at least the certified ranks. The 218 homogeneous columns have tested row rank 209 over that field. Appending readings of the eight stated counts and W000 gives full rank 218. Consequently over the rationals (indeed over the reals), two putative graphs with the same readings have identical full signed angle histograms at every dual index j≤35. The statement of sufficient coordinates requires only the final full-rank lower bound; it does not require modular rank to equal rational rank beforehand.

## Why the finite calculation determines every coefficient

Take any two such lattices with equal data and subtract their series. For each even h≤22, the dual-cusp zonal harmonic theta difference is zero through j=35, since the entire angle distributions there agree (this holds also for h=20,22, not used in the linear certificate). Its weight k≤44 and level Γ₀(7) of index 8 give valence bound 8k/12≤88/3<30 for the order at the ordinary cusp of a nonzero holomorphic modular form. Vanishing through j=35 therefore forces this weighted theta difference to vanish identically. Applying the Fricke transformation gives the same vanishing of the weighted series at the original cusp. Odd weighted moments vanish separately by antipodes.

On every original shell, equality of even zonal moments through 22 implies equality of ordinary even power moments through 22: start at degree zero and use the monic expansion whose other powers are lower even powers multiplied by fixed powers of the shell norm and the fixed axis norm. Thus, for every τ in the upper half-plane, all z-derivatives of the difference of φ at z=0 through order 22 vanish. For fixed τ the elliptic transformation law under z↦z+1 and z↦z+τ follows by integral pairing and the reindexing v↦v+w. Its index is w²/2=11; a nonzero holomorphic section of that elliptic line bundle has exactly 22 zeros with multiplicity in a period parallelogram (equivalently apply the logarithmic-derivative argument principle and quasi-periodicity). Order at least 23 at zero is impossible. Hence the two Jacobi theta series coincide. The Poisson transformation of the common Jacobi series gives equality at the other cusp too, with the dual normalization explained above.

Run `python3 two_type_hoffman_jacobi.py` next to the previously published native helpers. No large search, floating-point optimization or guessed symmetry occurs.
