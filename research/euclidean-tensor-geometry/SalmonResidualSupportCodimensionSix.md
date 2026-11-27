# Salmon residual support has codimension at least six

Let \(X=\widehat{\sigma_4}((\mathbb P^3)^3)\), \(I=I(X)\), and \(J=J_{5,6,9}\). The support of \(I/J\) has dimension at most 34 inside the 40-dimensional \(X\). This strengthens the codimension-five support bound without asserting any global ideal equality.

## Inverse-slice points

On an inverse-slice chart the commutator scheme of three \(4\times4\) matrices is reduced locally whenever a linear combination \(X_1\) of the matrices has at least three distinct eigenvalues. To see this, first fix its generalized eigenspace blocks at the point. Nearby, simultaneously conjugate the triple by \(1+H\), with \(H\) varying over off-block matrices, and require the first matrix in the conjugated coordinates to be block diagonal. The resulting map to the ambient space of triples is étale at the point: for the first matrix the derivative off the blocks is \([H,X_1]\), an isomorphism there by the disjoint spectra, and the coordinates of the other two matrices are unrestricted. Now the equations \([X_1,X_i]=0\) for \(i=2,3\) eliminate the off-block components of \(X_i\) by the same invertible Sylvester maps. The remaining equations are the independent commuting equations inside each block, scheme-theoretically. The only block possibly larger than one has size two. In size two separate scalar and traceless coordinates; the Lie bracket \(\bigwedge^2\mathfrak{sl}_2\to\mathfrak{sl}_2\) is an isomorphism, so the equations are precisely the \(2\times2\) minors of the \(3\times3\) matrix of the three traceless parts. This rank-one determinantal ring is prime. Dimension-one blocks impose no equations. Thus the local commuting scheme is reduced by étale descent, and the inverse-slice quintic commutation equations give \(I\) locally by the earlier inverse-slice argument.

Among the algebra-dimension-three cases of the [previous support estimate](SalmonResidualSupportCodimension.md), this removes \(\mathbb C^3\), since the generating triple has a linear combination with all three character values distinct. The earlier orbit estimates for \(\mathbb C\times\mathbb C[\epsilon]/\epsilon^2\) and \(\mathbb C[t]/t^3\) decrease by at least one: their embedded normalizers contain, beyond the centralizer, positive-dimensional automorphisms of the algebra, obtained by conjugating the nontrivial Jordan summand. Specifically scaling the nilpotent generator lifts by diagonal conjugation of its Jordan basis for each representation type, so it suffices that the normalizer increases by one. The square-zero radical-dimension-two case already has dimension at most 33 on the inverse chart. Lower algebra dimensions have smaller bounds. Algebra dimension four is already covered. Thus any bad inverse-slice points have dimension at most 34.

## Compressing just one mode

In type \((2,4,4)\) with no inverse slice, two fixed coordinate slices are independently singular, giving two independent determinant hypersurface conditions, for dimension \(32-2+4=34\) including the varying support. Type \((1,4,4)\) is smaller.

For \((3,4,4)\) all-singular, the [previous source-dimension argument](SalmonResidualSupportCodimension.md) leaves only the unique dimension-36 source type \((\mathbb C[x,y]/(x,y)^2)\times\mathbb C\), with its unique non-inverse factor the compressed one. In fact the other regular/dual-regular non-Gorenstein algebra types have automorphism dimension at least five: in the rank-one Hilbert-function \((1,2,1)\) case, \(x\mapsto a x+b y+c x^2\), \(y\mapsto d y+e x^2\), \(ad\ne0\), gives five parameters, and the local length-four square-zero case has \(\mathrm{GL}_3\). The exceptional noncyclic square-zero \(2+2\) type has source dimension at most 35. The one-projection fiber dimension four and varying support dimension three then give image dimension at most 34 for all these cases.

The remaining source tensor is the multiplication tensor of \((\mathbb C[x,y]/(x,y)^2)\times\mathbb C\), up to mode-wise basis changes; its non-inverse factor is the output. Its projected image closure is irreducible of dimension at most 35: the source type is one orbit, the projections are a single fixed-surjection type, and support variations are covered by an irreducible Grassmannian bundle, or equivalently by mode actions on a fixed projection. A sample in the projected image is
\[
 e_0 e_0 e_0+e_1(e_1 e_0+e_0 e_1)+e_2(e_2 e_0+e_0 e_2)
 +(e_0+e_1+e_2)e_3e_3 .
\]
The checker produces 24 independent quintic derivatives at this sample with minor \(31\bmod101\); it gives a regular local scheme exactly as before. Thus the bad support misses a nonempty open of the exceptional image closure and has dimension at most 34 there.

## Compressing three modes and smaller strata

The \((3,3,3)\) compression has irreducible closure of dimension at most 35 (27-dimensional core subject to a nonzero nonic, plus three Grassmannians). It is irreducible because the compressed rank-four secant is irreducible and the associated support bundle is irreducible. The [generic local scheme proof](SalmonTripleCompressionLocalIdeal.md) supplies a good point, so any bad subset has dimension at most 34. Two deficient modes with at least one rank at most two already have dimension at most 31. It remains only to control the \((3,3,4)\) locus.

See the companion note [double-compression analysis](SalmonCodimensionSixDoubleCompression.md) for the exhaustive double compression and the six other exact rank checks.
