# Size 65 in F_13^3: exclusion of parallel layers

Assume a hypothetical size-65 spectral pair whose mixed moments through degree seven vanish (the [preceding size-65 moment proof](FugledeF13Size65MomentsSeven.md)). A layered member B is supported in five parallel planes and has thirteen points in each. We prove no such member exists. This does not exclude all size-65 pairs.

## Graph and level normalizations

Write \(z=s\), \(s\in S\), for the five layer coordinates. The plane \(L\) of their horizontal difference directions has at least one missing direction, since \(D(B)\) is contained in the spectrum's uniform-normal set, which contains no projective line. Take that missing direction to be the \(y\)-axis; each slice is then a graph \((x,f_s(x))\) over the entire field. Affine changes \(z\mapsto az+b\) let us enumerate the ten affine orbits of \(S\subset\mathbb F_{13}\) of size five. These changes, and all later common affine coordinate changes, preserve vanishing moments of total degree at most seven, incidence caps and the absence of a full line in \(D(B)\).

Degree-four Lagrange interpolation in \(z\) isolates each layer's moments of planar degree at most three. The resulting identities \(\sum_x x^i f_s(x)=0\) for \(i=0,1,2\) imply the reduced polynomial representing \(f_s\) has degree \(d\le9\): its coefficients of degrees 12, 11 and 10 appear separately via the field power sums. Degree 0 or 1 would place all thirteen sites on a line. For \(2\le d\le9\), the graph can be individually put in the form \(f(x)=x^d+\sum_{i=2}^{d-2} a_i x^i\): rescale \(y\) to make the leading coefficient 1, translate \(x\) to kill degree \(d-1\), remove constant and linear terms by a \(y\)-shear and translation. These maps preserve local moment constraints and the cap of five on each line. All possible original graphs are recovered from the normalized representatives by
\[
 (x,y)\longmapsto (\alpha x+x_0,\ \beta y+\gamma x+y_0)
 \quad(\alpha,\beta\ne0).
\]
The per-slice translations are not treated as common changes until the moment argument below.

The three nontrivial low-moment checks remaining after the normalization are \(\sum f^2=\sum x f^2=\sum f^3=0\). The first two test coefficients 12 and 11 of \(f^2\), as \(d\le9\), and the third is a direct sum over the field. Testing each slice's line cap requires only the affine lines \(y-\tau x=b\), since vertical fibers are singletons. The standalone checker visits 5,229,044 normalized coefficient arrays and retains one graph with zero quartic moment, namely the parabola, and 2,158 graphs with nonzero quartic moment, counting representatives with their specified polynomial normalization.

## Common quartic and canonical fifth moments

For a graph slice let \(P_{j,s}(u,v)=\sum_{(x,y)}(ux+vy)^j\). Put \(Q_s=P_{4,s}\), \(R_s=P_{5,s}\), \(T_s=P_{6,s}\), \(W_s=P_{7,s}\). Vanishing total-degree-seven moments means \(\sum_s s^i P_{j,s}=0\) for \(0\le i\le7-j\). At degree four, the one-dimensional annihilator on the levels gives
\[
 Q_s=\lambda_s Q,\qquad \lambda_s=\Big(\prod_{t\in S,\ t\ne s}(s-t)\Big)^{-1}.
\]
If \(Q=0\), all slices must be parabolas in the common graph coordinates. The Fourier/Gauss-sum argument in [the parabola-layer note](FugledeF13Size65ParabolaLayers.md) rules this out.

For \(Q\ne0\) we can make a **single common** horizontal triangular linear change \((x,y)\mapsto(\alpha x,\beta y+\gamma x)\) so the projective quartic \([Q]\) is the least representative in its triangular orbit. A projective orbit is computed using \(\alpha=1,\beta\ne0,\gamma\) arbitrary: the removed overall scalar only rescales the homogeneous quartic. Quartic lines are represented by their coefficient vectors in order \(u^{4-j}v^j\), divided by the first nonzero coefficient. Use \(Q_*\) for the resulting canonical coefficient vector, and write \(Q_s=w_s Q_*\) with \(w_s=A\lambda_s\) and \(A\in\mathbb F_{13}^{\times}\). The checker finds 22 such projective quartic orbits. Every normalized graph is tested under all \(\alpha,\beta\ne0\), \(\gamma\) arbitrary, retaining those giving their canonical common quartic line. Thus individual inverse graph normalizations and the single common quartic choice are both accounted for.

Let \(k\) be the first nonzero coefficient index of \(Q_*\) (the exponent of \(v\)). The two-dimensional subspace \(Q_*\cdot\mathrm{Lin}\) in quintics has a canonical complement obtained by setting coefficients \(k,k+1\) to zero: subtraction of a multiple of \(uQ_*\), then a multiple of \(vQ_*\), does this uniquely. A translation by \((a,b)\) adds \(5(au+bv)Q_s\) to the fifth moment since all lower slice moments up through three are zero. Thus each slice has a unique translation making its fifth polynomial \(R_s\) belong to this complement. These individual translations can be implemented by a **single common affine shear in \(z\)** for any valid union of five slices: in the original moment identities \(\sum_s s^i P_{5,s}=0\), \(i=0,1,2\), project to \(Q_*\cdot\mathrm{Lin}\) along the complement. The two coefficients of the translation linear form, multiplied by \(w_s\), then each annihilate \(1,s,s^2\). This two-dimensional annihilator consists exactly of \((\lambda_s(a+bs))_{s\in S}\) by interpolation. Since \(w_s=A\lambda_s\), the translating coordinates themselves are affine functions of the level \(s\). The shear preserves every global geometric and moment condition, so it is legitimate to fix these translations during the census. In the complement the fifth identity becomes \(R_s/w_s=C+sD\) for a pair of fixed quintics \(C,D\).

The translated sixth and seventh binary forms are computed exactly by binomial expansion: for translation linear form \(\ell\), they become \(T_s+6\ell R_s+15\ell^2Q_s\) and \(W_s+7\ell T_s+21\ell^2R_s+35\ell^3 Q_s\), using the forms *before* translating on the right. The checker retains each distinct actual translated graph realizing its moment forms; it does not identify graphs merely because their signatures coincide.

## Census and geometric exclusions

The checker [verify-fuglede-f13-size65-layers.js](verify-fuglede-f13-size65-layers.js) runs without dependencies. For each level orbit, projective quartic representative and nonzero common scalar \(A\), it tests each pair of available \(R_s/w_s\) at the first two levels. This determines \(C+sD\), and the other three levels must realize those exact values. There are 15,240 surviving fifth scenarios. For each, choose the sixth/seventh signatures to meet the linear equations
\[
 \sum_s T_s=0,\qquad \sum_s sT_s=0,\qquad \sum_s W_s=0.
\]
A two-plus-three sum table over the field gives exactly 1,140 signature tuples. The distinct actual normalized graphs recorded at each signature give 1,944 graph unions (counted with the specified level and quartic choices). Of these, 456 obey the bound thirteen on all affine planes; every one determines all fourteen projective directions of some plane. This is impossible for a spectral member. Thus neither member of a hypothetical size-65 pair can be layered, and in particular every projective line has at most ten uniform normals, by the Radon deduction in the degree-seven note.
