# Exact cubic rigidity of the remaining length-17 M3 patterns

**Yongxian Zhang.** AI-assisted mathematical development and internal verification; no peer review or priority claim.

This supplements the [projective Cartan reduction](Matrix3BorderApolarityProjectiveCartan.md). All 29 triples consisting of the complementary Cartan-free shapes and their Cartan-enabled middle shapes **actually pass the four lower-degree necessary tests** over the rationals, not merely after reduction modulo 101. A [second checker](verify-mm3-cartan-projective-exact-survivors.js) computes ranks by fraction-free Gaussian elimination with BigInt coefficients, primitive normalization by gcd, and no finite-field operations. The side-shape ranks in degrees \((210),(120)\) and for the \((220)\) wedge test respectively are \((385,387,945)\) and \((387,385,945)\). Every listed middle shape passes the respective upper bounds \((388,388,952)\), and all cubic multiplication matrices have exact rank 712 in the 729-dimensional ambient space.

Moreover the resulting 17-dimensional cubic inverse system is **the same for all 29** up to a cyclic change of tensor factors. In zero-based row/column coordinates put
\[
 A_0=\langle a_{01},a_{02},a_{11},a_{12}\rangle,\qquad
 B_0=\langle b_{01},b_{02}\rangle,\qquad
 C_0=\langle c_{02},c_{12}\rangle .
\]
Then
\[
 I_{111}^{\perp}=\mathbb C M_3\oplus(A_0\otimes B_0\otimes C_0)
\]
for any candidate ideal. The 16 monomials on the right obey every pair slice condition. For \(AB\) the shared indices specify one of the two allowed positive roots in the upper \(2\times2\) outer cell rectangle; \(CA\) is complementary. In \(BC\) the outer cell is \((0,2)\); every middle shape has the full diagonal and all positive roots there, including the three offdiagonal slices from these choices and the remaining matched slice. The checker verifies this annihilation directly on every generator, and \(M_3\) is independent of the 16 monomials since its support is disjoint from theirs. The exact rank computation gives equality. An ideal with Hilbert function 17 in degree \((111)\) cannot add another cubic relation.

This does not assert that these forced cubics and pairs extend to any ideal with all the required Hilbert degrees or belong to the component of limits of distinct points. It identifies a single explicit cubic Grassmannian target on which stronger topological or higher-degree tests can concentrate.

## Scheme intersection with the Segre variety

Write \(L=\mathbb C M_3\oplus(A_0\otimes B_0\otimes C_0)\), and denote the \(M_3\) coordinate by \(\lambda\) and the 16 box coordinates by \(w_{abc}\). In the \(A\)-flattening of the general vector in \(L\), the minor on rows \(a_{20},a_{21}\) and columns \(b_{00}\otimes c_{02}, b_{10}\otimes c_{02}\) is \(\lambda^2\); its two crossed entries are zero. Use \(a_{20}, b_{00}\otimes c_{02}\) as one corner and any box position \((a,b\otimes c)\) as the opposite corner. Both crossed entries are scalar multiples of \(\lambda\), since the first row and first column are each outside the box. The new minor is \(\lambda w_{abc}\) modulo \(\lambda^2\). Thus the Segre intersection ideal contains \(\lambda\) times each projective coordinate, so \(\lambda=0\) scheme-theoretically in projective space. On that hyperplane the remaining Segre equations impose exactly the smaller Segre product \(\mathbb P A_0\times\mathbb P B_0\times\mathbb P C_0\) with its reduced scheme structure.

In particular every limiting support point is in this product box, not merely in the 17-dimensional span. This does not rule out a limit of spans whose intersection support or saturated subscheme fails to span its limiting plane: nonsaturation is precisely the remaining concern.
