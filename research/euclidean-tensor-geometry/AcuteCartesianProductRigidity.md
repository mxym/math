# Local rigidity of nonobtuse Cartesian products

Let \(X=\{x_i:i\in I\}\) and \(Y=\{y_j:j\in J\}\) each contain at least two distinct sites, and assume their difference spaces \(U,V\) are orthogonal. Work in exactly the intrinsic affine space of the product, identified after translation with \(U\oplus V\), with baseline sites \(x_i+y_j\). Fix one base label \(1\) in each factor and set
\[
\alpha=\min_{\substack{u\in U\\\|u\|=1}}\max_i |(x_i-x_1)\cdot u|,\qquad
\beta=\min_{\substack{v\in V\\\|v\|=1}}\max_j |(y_j-y_1)\cdot v|.
\]
Both are positive. If a labelled configuration of distinct points \(p_{ij}\) satisfies
\[
\varepsilon:=\max_{ij}\|p_{ij}-x_i-y_j\|
    \ \le\ \frac{1}{60\sqrt{\alpha^{-2}+\beta^{-2}}},
\]
and is nonobtuse, then it is still the orthogonal Cartesian product of two nonobtuse labelled factors, of dimensions \(\dim U,\dim V\). In particular it has right angles, and no acute configurations occur in that neighborhood.

This excludes product templates such as five three-dimensional sites times a segment as sources for ten acute points in \(\mathbb R^4\). It does not exclude non-product templates or give a global size upper bound. This is an intrinsic-dimension statement, not an obstruction to dimension-adding constructions such as [Gerencsér–Harangi](https://arxiv.org/abs/1709.03411) or [Zakharov](https://arxiv.org/abs/1707.04829). Targeted primary-source searches did not reveal a matching local classification; publication priority is not asserted.

## Four points in two pairs

Suppose the four points \(c\pm u,d\pm v\) are nonobtuse, and put \(h=c-d\). The angles at the first pair subtended by the second pair show \(\|h\|^2+\|u\|^2-\|v\|^2\ge2|h\cdot u|\). Exchanging the two pairs yields \(\|h\|^2+\|v\|^2-\|u\|^2\ge2|h\cdot v|\). In particular
\[
 |h\cdot u|+|h\cdot v|\le\|h\|^2,\qquad
 \big|\|u\|^2-\|v\|^2\big|\le\|h\|^2.                 \tag{1}
\]
If all four angles are acute then the inequalities are strict.

## Rectangles force factor separation

Define
\[
D=\tfrac12\max_{i,k,j,l}\|p_{ij}-p_{il}-p_{kj}+p_{kl}\|.
\]
Since the baseline is additive, \(D\le2\varepsilon\). Fix any two different \(Y\)-labels \(j,l\). Abbreviate
\[
a_i=(p_{ij}+p_{il})/2,\quad v_i=(p_{ij}-p_{il})/2,\quad
w_i=v_i-v_1,\quad X_i=x_i-x_1.
\]
Then \(\|w_i-w_k\|\le D\), \(\|w_i\|\le D\), and \(\|(a_i-a_k)-(X_i-X_k)\|\le2\varepsilon\).

On the rectangle with \(X\)-labels \(i,k\), pair the opposite corners \((p_{ij},p_{kl})\), \((p_{il},p_{kj})\). The difference of pair midpoints is \(h=v_i-v_k=w_i-w_k\), and their half diagonals are
\[
u_\pm=\tfrac12(a_i-a_k\pm(v_i+v_k)).
\]
By \(|h\cdot u_+|+|h\cdot u_-|\le D^2\) and \(u_++u_-=a_i-a_k\),
\[
 |(w_i-w_k)\cdot(X_i-X_k)|\le D^2+2\varepsilon D=:E.                \tag{2}
\]
The second inequality of (1) gives
\[
 |(a_i-a_k)\cdot(v_i+v_k)|\le D^2.                                 \tag{3}
\]
Sum the three left-hand expressions inside absolute values in (3) along the directed triangle \(i,k,1,i\). The \(2v_1\) term in \(v_i+v_k=w_i+w_k+2v_1\) cancels because the \(a\)-differences telescope. Replacing \(a_i-a_k\) by \(X_i-X_k\) in the remaining expressions changes the sum by at most \(12\varepsilon D\). The remainders \(X_1=w_1=0\) cancel, giving
\[
 |X_i\cdot w_k-X_k\cdot w_i|\le3D^2+12\varepsilon D.               \tag{4}
\]
The same conclusion is trivial if the three labels are not distinct. On the other hand (2) bounds \(|X_i\cdot w_i|\) and \(|X_k\cdot w_k|\) by \(E\), by taking the second label to be \(1\); expansion of (2) then yields \(|X_i\cdot w_k+X_k\cdot w_i|\le3E\). Combining with (4),
\[
 |X_i\cdot w_k|\le3D^2+9\varepsilon D
\]
for every \(i,k\). By subtracting two such tests, \(|X_i\cdot(w_k-w_m)|\le6D^2+18\varepsilon D\le30\varepsilon D\). The definition of \(\alpha\) bounds the \(U\)-projection of every \(h=v_k-v_m\) by \(30\varepsilon D/\alpha\). Since the fixed pair \(j,l\) was arbitrary, this holds for every rectangle midpoint difference. Swapping the roles of \(X,Y\) bounds every \(V\)-projection by \(30\varepsilon D/\beta\); it gives the same midpoint differences up to sign. Because \(U,V\) are orthogonal and fill the ambient space, this implies
\[
D\le30\varepsilon D\sqrt{\alpha^{-2}+\beta^{-2}}\le D/2.
\]
It follows that \(D=0\).

Every mixed difference now vanishes, hence \(p_{ij}=p_{i1}+p_{1j}-p_{11}\). Within any of its rectangular parallelograms, nonobtuseness at two adjacent vertices gives both signs of the inner product between the side directions, so all difference directions of the two factors are orthogonal. They have the original dimensions: \(\{p_{i1}-p_{11}\}\) projects to a spanning set on \(U\), since its dot products against unit \(u\in U\) differ from those of \(x_i-x_1\) by at most \(2\varepsilon<\alpha\); similarly for \(V\). Orthogonality and ambient dimension imply equality of the dimensions. Each factor is nonobtuse by holding the other label fixed. Conversely any orthogonal product of nonobtuse factors is nonobtuse because emanating dot products decompose into the sum of the two factor dot products (differences with a coincident factor endpoint contribute zero or a squared norm). Finally every such nontrivial product has right angles at its rectangular corners.

## Why an extra dimension defeats the obstruction

The centroid version of the lower-dimensional cube perturbation from [Gerencsér–Harangi](https://arxiv.org/abs/1709.03411) applies to every finite nonobtuse set. Put the original sites in a hyperplane and move one site \(x\) slightly toward the original centroid in that hyperplane, by an amount proportional to \(t^2\), and by \(t\) in a perpendicular direction. At an unperturbed center \(y\) with a former right angle between \(x,z\), the centroid movement makes it strictly acute: \((z-y)\cdot(s-y)\ge0\) for every original site \(s\), with strict inequality for \(s=z\). At the moved point, the new squared height \(t^2\) outweighs the horizontal perturbation by choosing its proportionality constant sufficiently small. Already acute angles stay acute. Proceed through the original labels with successively small displacements, preserving the angles of all triangles previously made acute. This shows why the missing orthogonal direction in the proof is an essential dimensional hypothesis.
