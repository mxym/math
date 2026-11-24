# An integer and graph-spectral filtration on the rank-42 cost-21 face

Suppose the seven-rank is 42 and among the twelve selected signed-unit species only 018,121,125 may occur. Then there are **no norm-14 Fano fields**, and each of the eight signed residues has **10, 11 or 12** positive-charge cost-21 fields. The proof leaves 5, 8 and 4 projected aggregate controls respectively. These are necessary low-mass data, not graphs or integral extensions. In particular, 10 is not eliminated here.

Use the [residue balance and native site bounds](rank42-u121-residues.md) and the [Hoffman overlap spectral cap](hoffman-overlap-spectral-cap.md) with its sharpened constant 114. With raw positive-charge populations denoted by G, rank 42 means the original sector is the full eligible zero sector (the sole H is zero). W is G/8 on nonisotropic species and G on isotropic species, so W121=r is an integer but a general nonisotropic W need not be. The four N18 populations on representatives of opposite sign pairs are a,a,b,b; their four antipodes have the same respective counts with a,b≥18. Thus N18=4(a+b), and 72|a−b|≤G125 by the residue theorem. Previous proofs give 9≤r≤13, 181≤N18≤260, G444≤600, and 6M−2W446−W014≤114.

## Exact eight coordinates

In the existing original-site chart set all nine other named unit populations equal to zero and impose the rank-42 original/eligible zero-sector equalities. The checker constructs the resulting exact 8-dimensional row coordinates as (1,r,f,M,S,Q,x,y), where f=N14/2, M=W222 counts actual Hoffman cocliques, S=W123−99−14f≥0 counts the additional unit fields, and Q=G444 is raw. The two last coordinates count all positive-one slots in positive charge (4,44),(4,46), respectively, not an assumed individual-root symmetry: the original-site averages times 99 and the appropriate orbit factor count slots. Sign reversal in the canonical site chart selects the negative slot at charge −4. Cost and sum force each (4,44) field to be nonpositive unit, so x=0. Each (4,46) field has exactly one +1 or exactly one −2 and no other exceptional site, since the sum of b_i(b_i+1) is two. Thus y is exactly the number of positive-subtype (4,46) fields, with 0≤y≤W446.

The exact inverse of the 8-by-8 matrix verifies
```
n = N18/4 = 88−23r/6+26f/3+M/3+S/2+Q/24,
W446 = 720−18r+50f−16M+2S+3Q/2.
```
Here n=46,…,65. The first identity and nonnegativity give the conservative envelopes 0≤f≤3, 0≤M≤81, 0≤S≤55. The checker loops these integers for each r, solves for Q, and retains only 0≤Q≤600. It evaluates all native nonnegativity inequalities, the stated spectral and site bounds, and S≥0. At fixed (r,f,n,M,S,Q) these are affine one-variable inequalities in y; intersect their integer intervals by signed floor/ceiling. This is a bounded integer calculation, with no floating optimization, symmetry averaging of integer masses or assertion of sufficiency. There are respectively **0,5,12,19,5** remaining projected aggregates, and all 41 have f=0. In particular no 15-overlap pair remains on this face.

## The one-overlap graph has a specified eigenvalue

For each aggregate retain all signed class sizes a≥b≥18 satisfying a+b=n and the preceding difference bound. Let c=44−d(a)−d(b)−2, where d(t)=ceil(24(t−1)/(t+24)). By the orthogonal-span argument in the preceding spectral cap, c is an **upper** bound for the dimension of the real span of the centered cocliques; no exact span rank is assumed. Put l=M−c. With no Fano, their Gram is 7(2I−A+4J/9) for the unsigned simple one-overlap graph A. Its e edges satisfy e≤W446−y: the distinct-field injection for one-overlap pairs lands in the one-double subtype only, because c_C+c_D takes value −2 at their common site and nowhere has a positive value.

Since r>0, the positive-edge reflection gives a literal point excluded from every Hoffman coclique (G337 is absent). At this point every centered indicator takes the same nonzero value. Hence every linear dependency of the centered indicators has coordinate sum zero; it is killed by J. At least l **actual eigenvalues equal 2** for A. This is stronger than just l eigenvalues above a Rayleigh threshold.

If the spectral radius is ≤2, each component supports at most one eigenvalue 2 by Perron simplicity, and such a component needs at least three vertices. Also the edge-deletion bound in the previous paper gives l≤e/3. The trace zero and squared trace 2e give 4Ml≤2ec by Cauchy on the other c eigenvalues after reserving l copies of 2. If instead the spectral radius rho is >2, there are at least l+1 eigenvalues ≥2 and so 3(l+1)≤e. Reserve rho and exactly l eigenvalues equal to 2. The remaining c−1 eigenvalues sum to −rho−2l, and
```
2e ≥ rho²+4l+(rho+2l)²/(c−1),       rho ≥ 2e/M.
```
Substitution (the RHS is increasing in nonnegative rho) and clearing positive denominators gives the exact necessary test
```
4e²c+8elM+4l(M−1)M² ≤ 2e(c−1)M².
```
Using a larger c than the true rank cannot cut an actual graph: it merely reserves fewer copies of 2; Cauchy applies to the actual remaining c or c−1 eigenvalues. For each class-size option test every integer 0≤e≤W446−y_lo. If either permitted spectral case passes, retain the aggregate; no conclusion about a graph follows from passing. This leaves **0,5,8,4,0** aggregates for r=9,…,13. The five r=10 rows, in the notation (f,n,M,S,Q, y_lo,y_hi) before the spectral refinement, are (0,59,27,0,8,0,120), (0,59,28,0,0,0,92), (0,60,28,0,24,0,128), (0,60,28,1,12,0,112), (0,60,28,2,0,0,96).

Replay [the exact checker](cost21_integer_filtration.py) with `python cost21_integer_filtration.py` next to `original_site_populations.py` and `rank36_three_types.py` with their usual SymPy dependencies. The output reports both layers separately.

The [actual complement involution and walk bounds](cost21-four-coclique-walk.md) leave a single aggregate control on this support: r=10, N18=236, M=27, S=0, G444=8. It is not a graph witness or an exclusion of other supports.
