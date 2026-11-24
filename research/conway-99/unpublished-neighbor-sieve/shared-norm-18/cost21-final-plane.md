# The shared plane excludes the last rank-42 cost-21 support

Suppose the named unit support at rank 42 is contained in {018,121,125}. The [integer/defect filtration](cost21-four-coclique-walk.md) and [26-point equality case](cost21-26-tight-frames.md) leave only one projected case, with four signed norm-18 fibers of sizes 30,30,29,29, together with their negatives. The [independent original-site marginal check](cost21-eight-parallel-44.md) gives the normalized norm-22 mass 91/2 on this exact tuple; because that shell is nonisotropic, it counts 364 oriented graph fields, or 182 antipodal lines. We choose one signed fiber on each of the four residue lines. The choices within each of the equal-size pairs correspond to perpendicular lines in the anisotropic 7-plane. Within a signed fiber the inner products of distinct vectors are 4 and −3. Between the two perpendicular fibers they are 0 and ±7. Across the pairs, the four constant inner products, after sign choice and ordering, are the entries of the Hadamard matrix H=[[1,1],[1,−1]]. These are ordinary integer graph-field inner products, not scaled modular shell counts. Let E4 be the total number of unordered dot-4 pairs inside the four chosen signed fibers. Let E7 be the number of absolute-dot-7 pairs in the two rectangular cross tables 30×30 and 29×29; each entry is counted once.

**Graph-field upper bound.** Associate a cross pair of absolute dot 7 with the unique unoriented norm-22 line [q] equal to the pair's sum or difference (with signs chosen to yield norm 22). If μ(q) counts its preimages, then Σμ=E7 on 182 lines. In any two decompositions of the same q the two residue classes are the same up to reversing both signs: in the 7-plane the first summand v has v²=4 and v·q=q²/2=4 modulo 7, so there are at most two possibilities, exchanged by v↔q−v. Indeed this is a circle restricted to a line on which the quadratic coefficient is nonzero by anisotropy, and those two possibilities are distinct and orthogonal. Orient q and the two decompositions consistently, as t_i+u_i=t_j+u_j with the t's in the same signed fiber. Then t_i·q=11. Since t_i·t_j=4 or −3 and t_i·u_j is a perpendicular-fiber product with magnitude at most 7, t_i·t_j=4; likewise u_i·u_j=4. Both source pairs are therefore counted by E4, even if the chosen orientation of one fiber must be reversed as a whole.

Conversely a fixed same-fiber dot-4 pair t,t′ has at most two double-decomposition incidences of this kind. Order the pair once and orient q so t,t′ are in the chosen signed fiber. A counterpart in a fixed sign of the perpendicular residue line must solve v−w=t−t′=:d with both v,w in that same signed fiber. Since d²=28 and v,w have equal norm, any further solution v′−w′=d satisfies d·v′=14. If v′≠v, then w·v′=v·v′−14≤−10, impossible in that signed fiber (even w=v′ would give 18). Thus at most one counterpart for each of the two signs. The pair and its oriented counterpart uniquely give q=t+w=t′+v. Double-counting yields Σ binom(μ,2)≤E4. Since binom(j,2)≥3j−6 for every nonnegative integer j,
```
3E7−E4 ≤ 6·182 = 1092.                                  (1)
```
This does not need an a priori multiplicity cap.

**Common plane.** The four fibers lie in a 28-space orthogonal to the 16-dimensional actual Hoffman span. The within-fiber difference spaces coincide within each of the two equal-size pairs; they are two mutually perpendicular spaces of dimension 13. This follows from the saturated 13+13+2 argument in the 26-point note. In their two-dimensional perpendicular complement P, the projections of all members of fiber i agree, say y_i. Every member of fiber i equals y_i plus a vector in its own 13-space: it is perpendicular to differences in the other 13-space because the cross-fiber products there are constant. Thus the matrix of cross products of the projected vectors is exactly H. The first pair spans P since H is nonsingular. Write a,b,c,d for the four squared projected lengths and h=y_1·y_2. The last pair has Gram Hᵗ[[a,h],[h,b]]⁻¹H. Eliminating h gives
```
4ab(c+d)² = (a+b)²(c−d)² + 8(a+b)(c+d).                (2)
```
All are strictly below 18, since a projection of squared length 18 would make every point of its non-singleton fiber identical. Neither this nor (1) uses a high intersection with any equitable 44-set.

**Bounds for one fiber.** Write n for its size, e for its dot-four pairs, A for their adjacency, x=2e/n, and s for its squared projected length. Its raw Gram is 7(3I+A)−3J. The squared norm of its mean bounds s, giving n²s≤(21−3n)n+14e. The vectors after removing y_i have Gram 7(3I+A)−(3+s)J, of rank at most 13. The trace-square inequality gives
```
J(s):=n[13(n−1)(3+s)²−(n−13)(18−s)²]+182e(1−2s) ≥ 0. (3)
```
Indeed the latter Gram has diagonal 18−s, off diagonal −3−s or 4−s, with 2e ordered entries of the latter kind. The coefficient of s² in J is 12n²>0, so an interval on which both endpoint values are negative is impossible.

Independently center the fiber exactly by subtracting its full mean and divide the vectors by √7. For the resulting frame operator B on its 13-space, tr B=T/n, T=3n(n−1)−2e. If D is the variance tr(B−(tr B)I/13)², then
```
0 ≤ 13n² D ≤ V=13[9(n−1)n²+(n−6)2en−4e²]−T².          (4)
```
To check this, let K=I−J/n. The centered Gram is K(3I+A)K. Expanding its square and using Σdegree²≥nx² gives tr B²≤9(n−1)+(n−6)x−x².

For the two perpendicular fibers of the same size n, the raw cross matrix divided by 7 has entries 0,±1 and squared Frobenius norm E_n. Centering it on the left and right can only decrease that norm. Its resulting squared norm is tr(B₁B₂) on the common 13-space. Applying Cauchy to the two traceless parts in (4) yields
```
E_n ≥ [T₁T₂−√(V₁V₂)]/(13n²).                            (5)
```
Here E7=E_30+E_29.

**Tiny integer interval certificate.** [Replay](cost21_final_plane.py) with standard Python. Enclose each of a,b,c,d in a closed interval [i/10,(i+1)/10], 0≤i<180. For every integral 0≤e≤binom(n,2), discard a bin/e combination only by the mean bound, the endpoint test in (3), or V<0 in (4). On each surviving bin retain largest e, smallest T and largest V. T>0 throughout (indeed 2e≤n(n−1)). For each unordered pair of such bins use (5) with those extrema and an upper square root isqrt(V₁V₂)+1, rounding the lower bound up since E_n is integral. Subtract both upper e's from three times that lower bound. This safely bounds 3E_n−(e₁+e₂) from below even though the three extrema need not coincide.

There are 45 unordered bin pairs at n=30 and 120 at n=29. For a pair-of-pairs, discard it only if the two sides of (2) have disjoint endpoint enclosures, taking the smaller absolute difference in its third factor to be max(0,|i−j|−1)/10 and its larger at most (|i−j|+1)/10. The 1,427 surviving boxes give a uniform lower bound of **1112** on 3E7−E4, strictly greater than (1). The rank-42 named support contained in {018,121,125} is therefore impossible. No graph reconstruction or other spectrum case is asserted.
