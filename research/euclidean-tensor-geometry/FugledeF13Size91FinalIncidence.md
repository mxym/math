# No 91-point spectral subset of \(\mathbb F_{13}^3\): final incidence contradiction

Continue from the [geometric stage](FugledeF13Size91Geometric.md) and [weighted-profile stage](FugledeF13Size91WeightedProfiles.md). Write \(u_B,c_B,r_B\) for the number of \(U,C,R\) projective normal directions of \(B\), respectively. Its projective nonuniform set is \(V_B=C_B\cup R_B\). The weight sum of 567 gives \(21c_B+7r_B=567\), so
\[
 r_B=81-3c_B,\quad
 u_B=102+2c_B,\quad
 |V_B|=81-2c_B.
\]
The degree-eleven moment form \(H_B=M_{11}^B\) has zero set \(Z_B=U_B\cup C_B\). Indeed if the residues of a profile are \(at+b\), this moment equals \(-a\) by the field power sums. The form is nonzero: if \(R_B\) were empty, a pencil through any secant with \(a\in[2,4]\) points would have only nonempty occupancies seven or thirteen; with \(s\) of them seven the equation \(6s=13(7-a)\) is impossible, since \(13\mid s\) gives \(s=0,13\) and \(a=7,1\) respectively.

## 6. At most seven layered normals per member

Every projective line contained in \(Z_B\) is a rational line factor of \(H_B\): a nonzero homogeneous binary degree-eleven form has at most eleven projective roots, fewer than fourteen. Every such factor line has between six and thirteen uniform points, and all its nonuniform normals are type \(C\). For a factor line, use the pencil through any affine line parallel to its annihilator and containing at least one \(B\) point. This gives \(6s=13(7-a)\) with \(6\le s\le13\) uniform planes and \(1\le a\le4\) points on the affine line, so \(s=13,a=1\). Thus each line factor contains exactly one \(C\) normal. Conversely each \(C\) normal lies on a factor line: by blocking in the partner it belongs to some tight line, and a tight line containing its weight \(21\) has no other nonuniform normal. All such lines have fourteen zeros. Consequently
\[
 c_B\le k_B^{\rm lin}\le 11,
\]
where \(k_B^{\rm lin}\) counts distinct rational line factors. At most six such factors can pass through any point: otherwise a nonfactor line through that point would have at most \(1+11-7=5\) distinct zeros, contradicting the six-point lower bound from \(D(B')\subseteq U_B\).

For \(k\) distinct projective lines with maximum concurrence \(t\), their union has at most
\[
 \min\{14k-k(k-1)/t,\ 13t+1+(k-t)(14-t)\}
\]
points. For the first bound, if a point occurs on \(j\) lines, its contribution \(j-1\) to the overcount is at least \(j(j-1)/t\), and \(\sum j(j-1)=k(k-1)\) counts ordered intersections. For the second, the initial maximal pencil contributes \(13t+1\), and any remaining line (not concurrent at its point) meets its \(t\) lines in distinct points. If after stripping rational line factors with multiplicity the residual has degree \(s>0\), it has at most \(1+14(s-1)\) projective zeros: through one such zero, no line is a factor, and each of the fourteen lines contains at most \(s-1\) other zeros. Constant residuals add zero. With \(k=8,9,10,11\) and \(2\le t\le6\), the [arithmetic verifier](verify-fuglede-f13-size91-arithmetic.js) gives combined zero set bounds \(124,118,113,123\), respectively. For \(k=10\) the residual cannot have degree one, since that would add a distinct rational line factor. The maximum possible residual degree in the other cases is \(11-k\).

If \(c_B\ge8\), then \(k_B^{\rm lin}\ge8\) and \(|Z_B|=102+3c_B\ge126\), contradicting all the bounds. Thus \(0\le c_E,c_A\le7\).

## 7. Polarity mixing rules out two nonuniform sets

Put \(N=|V_E|=81-2c_E\), \(M=|V_A|=81-2c_A\). Every point of \(V_A\) corresponds to a tight line in \(E\), with either three \(R_E\) points or one \(C_E\) point. Each distinct \(C_E\) lies on at least one such line, by blocking, and distinct \(C_E\) points cannot give the same line. Hence the incidence \(I=\mathbf1_{V_E}^{T}P\mathbf1_{V_A}\) is at most \(3M-2c_E\). Interchanging sides also gives \(I\le3N-2c_A\).

For any two projective point subsets of sizes \(N,M\), the polarity identity \(P^{T}P=13I+J\) gives
\[
 I\ \ge\ \frac{14NM-\sqrt{13N(183-N)M(183-M)}}{183}.
\]
Indeed decompose each indicator into its constant part plus a mean-zero vector. Cross terms vanish because \(P\mathbf1=14\mathbf1\), and on the mean-zero subspace the operator has norm \(\sqrt{13}\); the indicator-centered lengths are \(\sqrt{N(1-N/183)}\) and \(\sqrt{M(1-M/183)}\). The arithmetic verifier checks the 64 pairs \(0\le c_E,c_A\le7\) by exact integer inequalities. With \(I_{\max}=\min(3M-2c_E,3N-2c_A)\) it obtains \(d=14NM-183I_{\max}>0\) and \(d^2>13N(183-N)M(183-M)\) every time. Thus the spectral upper bound is strictly smaller than the universal lower bound. This contradiction finishes the proof.

Together with the 104/117 exclusions, the only still-possible cardinalities for a spectral counterexample to Fuglede in \(\mathbb F_{13}^3\) are \(26,39,52,65,78\), without asserting the existence of any of them.
