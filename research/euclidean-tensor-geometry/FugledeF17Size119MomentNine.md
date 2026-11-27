# Size 119 in F_17^3: moments through nine and at most one layer

Assume a spectral pair of size119=7·17. The general preliminaries give D(B)⊂U_{B'}, affine plane cap17, affine line cap7 (the standard min(m,p−m) bound of [Ferguson–Iosevich Lemma 8.2](https://arxiv.org/html/2610.30712v1)), and no complete uniform-normal projective line. A layer is a normal with seven full planes of occupancy17 and other planes empty.

## Six-blocking holds under a low-degree form

Suppose a nonzero homogeneous form F of degree d≤10 vanishes on U_B but some projective line has at most five U_B sites. Its parallel affine slices in B' have at most five directions. The [planar census of the size-136 proof](FugledeF17Size136MomentNine.md) gives maximum five for noncollinear configurations with at most five directions even allowing cap8, so every slice has at most seven by the spatial line cap. Averaging forces all seventeen slices to be collinear seven-sets.

Their support directions use at most five choices, so at least four supports are parallel to an axis e. Projecting them along e yields a four-point cap: three collinear projected locations would put 21 points into a spatial plane, violating cap17. A four-cap determines at least four directions: if its six pairs used only three directions then all three perfect matchings would be pairs of parallel chords; two make a parallelogram and the third is impossible in odd characteristic. For each quotient pair, the difference of the two axial seven-sets has at least thirteen values by Cauchy–Davenport. These give thirteen transverse difference directions plus e, at least fourteen directions in its radial projective line through e. All these lie in U_B, so at least four distinct radial lines are factors of F.

Put k≥4 for the number of distinct factors through e. Each radial nonfactor contains at most 1+d−k≤7 sites of U_B. Any associated affine plane through one of the chosen seven-point lines of B' cannot contain a point outside the line: that point and the seven collinear sites would determine seven distinct transverse directions plus the line's direction, eight in all. Hence each nonfactor plane contains exactly seven points. The occupancy of all eighteen planes through an actual seven-point support is at most 7(18−k)+17k≤226, whereas the pencil identity gives 119+17·7=238, contradiction. Thus under F of degree≤10 every line meets U_B at least six times.

## Moments through eight, and at most one layer

For d=8 write N=|U_B| and n_L=|L∩U_B|. The six-blocking conclusion and absence of full U lines give 6≤n_L≤17. The standard incidence identity gives
```
Σ_L(n_L−6)(n_L−8) = N²−235N+14736 ≥930.
```
Nonfactors contribute nonpositively; at most eight factors each contribute ≤(17−6)(17−8)=99, upper792. Therefore no such form exists, implying vanishing mixed moments through eight by the moment form uniform-normal zeros.

If two distinct layer normals existed, project to their two coordinate axes. The support is X×Y with |X|=|Y|=7, integer row and column occupancies17, and cell cap7. The degree-eight moment conditions force the barycentric form λ_X(x)λ_Y(y)Q(x,y) modulo17, where Q has total degree≤3. The product Vandermonde argument is as in [the size-136 proof](FugledeF17Size136Final.md): the largest total basis degree is12, moment tests of degrees≤8 leave dimension ten, and weighted evaluations of the ten monomials of degree≤3 give that orthogonal complement. The exact checker [verify-fuglede-f17-size119-two-layers.js](verify-fuglede-f17-size119-two-layers.js) enumerates the 75 affine level-set classes, 2850 unordered pairs, allowed degree-three rows from four starting entries, and the across-row coefficient interpolation restrictions. Its depth counts [2850,661614,9049191,7123972,258953,282,0,0,0,0] give no complete grid. Thus each member has at most one layer.

## Degree-nine heavy factors

Suppose F is a nonzero degree-nine form vanishing on U_B, so U_B is six-blocking as proved above. Counting the incidence sum Σ_L(n_L−6)(n_L−9) gives integer lower bound576. Nonfactor contributions are nonpositive. A factor with n_L≤14 contributes at most (14−6)(14−9)=40, and any factor contributes at most (17−6)(17−9)=88. At most four factors with n_L≥15 would bound the total by 4·88+5·40=552. Thus at least five factors contain ≥15 sites of U_B.

In such a ≥15-uniform pencil, there are at most three nonuniform profiles. The planar Radon Vandermonde identity forces them affine or constant modulo17; a nonconstant affine profile has least residue mass136>119, so cannot occur. A nonuniform constant residue profile must be a layer. The Radon constant equation 7(b−1)=0 shows there is exactly one such profile. All five heavy factor lines therefore pass through the sole possible layer normal of B. Any radial nonfactor there has at most 1+9−5=5 sites of U_B, contradicting six-blocking. Thus degree-nine forms vanish identically in the moment application, and all mixed moments through nine are zero.

This is a partial statement at cardinality119.
