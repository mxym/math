# Symmetry breaking in the nine-point quartic kissing problem

For a \(60^\circ\) code of unit vectors let
\[
 C(X)=\min_{p_i\ge0,\ \sum p_i=1}\ \sum_{ij}p_ip_j f(x_i\cdot x_j),
 \qquad f(t)=t^4-t^2/4.
\]
There is a strict gap between the best vertex-transitive nine-point code and the unrestricted problem:

* **Maximum over transitive codes across all dimensions:** \(0.15628694668\ldots\), uniquely attained up to isometry by the rank-four cyclic configuration below.
* **A nontransitive five-dimensional example:** \(0.158737<C(X)<0.158738\). Its strong graph (join scalar products strictly below \(-1/2\)) is connected and factor-critical.
* **Upper bound for all nine-point codes in any dimension:** \(C(X)\le0.161\), improving \(0.163\). Thus for every ambient dimension at least five, **no global maximizer is vertex-transitive**, and the supremum restricted to factor-critical codes also strictly exceeds the transitive maximum. The exact unrestricted value remains open.

The example shows that symmetry breaking is not just an artifact of joining disconnected orthogonal codes. The Fourier argument adapts the [seven-point transitive calculation](https://github.com/mxym/math/blob/4f75d746375dfefc460c3bc2b69f5065d8e6bb09/research/euclidean-tensor-geometry/KissingSharpHeptagonalCapacity.md); at nine there is a second regular group to handle and an explicit asymmetric code that beats the optimum. The same rank-four cyclic code also uniquely maximizes the **mean strength** of the consecutive edges in an arbitrarily ordered nine-point code, without requiring transitivity for that mean problem.

## The transitive possibilities

Take the permutation image of the isometry group. A Sylow \(3\)-subgroup of a transitive group of degree nine acts transitively: its order is nine times the 3-part of a point-stabilizer order. A central element of order three has no fixed point, and gives three blocks of size three. Choose an element cycling the blocks. If it has order nine it is a regular nine-cycle. Otherwise it has order three and together with the commuting central element gives a regular elementary abelian group of order nine. In the latter case every nonzero translation has order three, and a strong lag would give a triangle of strong edges, which is impossible since the squared norm of the sum of three vectors cannot be negative. All off-diagonal costs are then nonpositive.

For the cyclic case, circulant Gram matrices have lags \(g_j=\sum_{k=0}^4p_k\cos(2\pi jk/9)\) for \(j=1,2,3,4\), where the \(p_k\) form a probability vector. Conversely each such choice with all \(g_j\le1/2\) is realizable. On any transitive code the uniform masses minimize the energy: the matrix with entries \(f(x_i\cdot x_j)\) is positive semidefinite. Indeed any nine points embed in \(\mathbb R^9\), where \(f=P_0/396+(22/117)P_2+(80/143)P_4\) in normalized Gegenbauer polynomials. Average the masses over the transitive group. Thus \(C=[3/4+2\sum_j f(g_j)]/9\). Lag three cannot be strong, and no two of the three unit lags \(1,2,4\) can both be strong: doubling permutes them up to sign and these two lags would give a triangle. If there is a strong lag, relabel it as lag one.

## A strict Fourier extremum

Put \(a=\cos(2\pi/9), b=\cos(4\pi/9), c=\cos(8\pi/9)\). The lag table, with rows \(j=1,\dots,4\) and columns \(k=0,\dots,4\), is
\[
 V=\begin{pmatrix}1&a&b&-1/2&c\\1&b&c&-1/2&a\\
 1&-1/2&-1/2&1&-1/2\\1&c&a&-1/2&b\end{pmatrix}.
\]
Set \(\omega=1/(a+1/2)\). The candidate has \(p=(0,0,0,1-\omega,\omega)\) and lags \(x=V_{\bullet,3}+\omega(V_{\bullet,4}-V_{\bullet,3})\), with columns numbered from zero. Here \(x_2=1/2\), \(x_1=-0.847296355\ldots\), and \(|x_3|,|x_4|<0.185\). The claimed exact transitive maximum is \([3/4+2(f(x_1)+f(x_3)+f(x_4))]/9\).

Let \(u=(p_0,p_1,p_2,1/2-g_2)\ge0\). Eliminating \(p_3,p_4\) gives \(g_j-x_j=B_j\cdot u\). If \(d_j=(V_{j,4}-V_{j,3})/(a+1/2)\), the first three entries of \(B_j\) are \(V_{j,k}-V_{j,3}-d_j(V_{2,k}+1/2)\); the fourth is \(-d_j\). Every entry of \(B_1\) is strictly positive and, coordinatewise, \(|B_3|+|B_4|<7B_1\). The [exact scalar checker](verify-kissing-nonagon-symmetry.py) verifies these comparisons by bracketing the three real roots of \(8t^3-6t+1\). In particular \(g_1\ge x_1\), with equality only at the stated vertex.

On \(x_1\le t\le-1/2\) the secant slope of \(f\) relative to \(x_1\) is \((t+x_1)(t^2+x_1^2-1/4)\le-9/10\), since \(x_1<-0.84\). For \(|t|\le1/2,\ |z|\le0.185\), the absolute slope \(|(t+z)(t^2+z^2-1/4)|\) is at most \(1/8\): use \((0.30+0.185)/4\) for \(|t|\le0.30\), and \((0.50+0.185)\,0.16\) otherwise. Since \(f(g_2)\le f(1/2)=0\), the net change in the sum is at most \((-9/10+7/8)(g_1-x_1)\). This proves strict extremality off the stated vertex whenever a strong lag is present. In its absence the uniform cost is at most \(1/12\).

For the mean edge strength, average the Gram matrix of **any** ordered nine-point code over its cyclic shifts. The preceding linear bound gives mean strength at most \(-x_1\). At equality every individual lag-two entry is \(1/2\). The averaged Gram matrix is supported on the complex Fourier frequencies \(K=\{3,4,5,6\}\bmod9\); positivity forces the original matrix onto this same support. The diagonal and lag-two diagonal uniquely determine a symmetric matrix on that support. At each sum \(k+l\bmod9\) there are at most two unordered pairs in \(K\); their two observation multipliers are \(1\) and \((\zeta^{2k}+\zeta^{2l})/2\) for \(\zeta=e^{2\pi i/9}\). Distinct pairs have distinct second multipliers: with the product fixed, the sum determines both roots, and doubling is invertible mod nine. Hence the original Gram matrix equals its cyclic average. In particular the maximizer of the mean-strength problem has rank four and is unique up to isometry of the ordered code.

## A strictly better, factor-critical code

The [companion checker](verify-kissing-nonagon-symmetry.py) lists nine integer five-vectors; normalize each by its own length. All pair products are strictly below \(1/2\). The ten strong edges form three internally disjoint paths between vertices 6 and 8 (zero-based):
\[
 6,0,4,8;\qquad 6,1,5,8;\qquad 6,2,7,3,8.
\]
Deleting any one vertex leaves a perfect matching. The normalized Gram entries need not be rational, but **their squares are**. Thus every quartic cost is rational. Exact elimination verifies that the cost matrix \(F\) has positive pivots, and that \(z=F^{-1}\mathbf1\) is strictly positive. The unique minimizing masses are \(z/(\mathbf1^\top z)\); their cost is \(1/(\mathbf1^\top z)\), in the strict interval above. All checks are standard-library rational arithmetic.

## Global bracket and replay

The [Gram replay](verify-kissing-nonagon-global.py) reuses the pinned affine-quartic box solver and the complete triangular-graph census. An independent five-set gives \(C\le3/20\). Of the 290 nine-vertex triangle-free classes with independence number at most four, 170 are factor-critical. All 170 pass at \(0.161\): 68,206 continuous boxes in the reported replay, 34,187 integer-dual leaves, and one incompatible-interval leaf. The largest tree has 13,029 boxes. For the remaining classes the [canonical barrier argument](https://github.com/mxym/math/blob/1a6fdc1dc8d4a4a1df7aef313b34e9c21b472400/research/euclidean-tensor-geometry/KissingNinePointCapacityAnd127Matching.md) leaves \(7+1\) or \(5+1+1\) after deletion. Since cross costs are nonpositive, combining local masses gives inverse capacity at least \(1/.2015+4/3\) or \(1/.252+8/3\), respectively; both exceed \(1/.161\).

Run from this directory:
~~~sh
python3 verify-kissing-nonagon-symmetry.py
python3 verify-kissing-nonagon-global.py census
python3 verify-kissing-nonagon-global.py
~~~
The latter verifier accepts optional individual class indices; use standard Python with NumPy, SciPy and threadpoolctl, not optimized mode. Its pinned predecessors are retained in the same directory.
