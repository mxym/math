# Exact projective Cartan reduction for the length-17 M3 border-apolar search

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review or priority claim.

**Proposition.** Let \(M_3\) denote complex \(3\times3\) matrix multiplication. Any length-17 border-apolar ideal fixed by the upper Borels of its three stabilizer factors has a triple of bidegree inverse systems from a list of at most **29** explicit rational triples, up to cyclic change of factors. In particular none of its three bidegree inverse systems can use a genuinely free Cartan line. In every surviving triple two inverse systems are Cartan-free, in fixed complementary shapes, and the third has Cartan directions. This is only a reduction: it does not exclude the surviving triples or improve \(17\leq\underline R(M_3)\leq20\).

The enumeration and algebraic certificates can be replayed with [verify-mm3-cartan-projective-r17.js](verify-mm3-cartan-projective-r17.js) in Node.js, without packages. The upper-Borel condition is the one used by [Conner–Harper–Landsberg](https://arxiv.org/abs/1911.07981) to obtain the lower bound 17. [Mańdziuk, §6](https://arxiv.org/html/2609.12121v1#S6) recovers that bound by testing at length 16; the square test used here is Mańdziuk's. The upper bound 20 is due to [Smirnov](https://doi.org/10.1134/S0965542513120129). [Landsberg, §9.4](https://arxiv.org/abs/2108.06263) already reports constructing candidates for border rank 17 and undertaking deformation tests; our incremental contribution is the replayable all-parameter elimination, the use of the square test at length 17, and the common necessary pair shapes, not the observation that border apolarity yields candidates. The [November 2026 numerical study](https://arxiv.org/abs/2602.21797) does not change the exact interval.

## 1. Borel-stable pair spaces

Write \(A=U\otimes V^*,\,B=V\otimes W^*,\,C=W\otimes U^*\), with each inner dimension 3, and let \(E=I_{110}^{\perp}\subset U\otimes\operatorname{End}(V)\otimes W^*\) be a candidate pair inverse system. Apolarity forces \(U\otimes\mathbf{1}_V\otimes W^*\subset E\). After splitting off that summand by the trace, the remaining dimension is eight. In each of the nine outer cells \((i,k)\) the diagonal tori distinguish all root lines \(E_{l,j}\), \(l\ne j\), along with the two-dimensional traceless diagonal space. Distinct outer cells have distinct \(U,W\) characters. The subspace in cell \((i,k)\) must be contained in those in \((i-1,k)\) and \((i,k+1)\) when defined, by the outer simple-root actions. At each cell it must be stable under the two positive simple-root adjoint actions in \(V\).

Use positive and negative masks on \((01,02,12)\), denoting the upper roots and their transposes respectively. With no negative roots the possible positive masks are \(0,2,3,6,7\). If the diagonal part is a line, then for each missing positive root its functional annihilates that line. Thus the only additional options with no negatives are: mask 3 and line \(K_{12}=\ker(d_1-d_2)\); mask 6 and line \(K_{01}=\ker(d_0-d_1)\); or mask 7 and an arbitrary diagonal line. A negative simple root forces its coroot \(H_{01}=(1,-1,0)\) or \(H_{12}=(0,1,-1)\), respectively, by taking its bracket with the corresponding positive simple root. Either coroot forces both positive simple roots, hence also the highest positive root. Both negative simples force full diagonal, and the negative highest root forces both negative simples. The full-diagonal cases thus have positive mask 7 and negative masks \(0,1,4,5,7\) in the bit convention \(01,02,12\); the checker encodes the two negative simples by bit values \(1,4\). Each possible local type follows by these closure conditions, and no other adjoint brackets are needed since the positive simples generate the upper nilpotent Lie algebra.

A free line needs four dimensions (itself and the three positive roots), so if two appear those two cells use the entire budget of eight. They must be comparable, since two incomparable nonzero cells force a third nonzero cell toward the upper corner. Their lines must coincide by nesting. If a free line is nested with a prescribed one-dimensional diagonal space then the value is fixed by equality. Consequently each pattern has at most one projective parameter, and the checker enumerates all patterns by choosing local types in outer order \((0,2),(0,1),(0,0),(1,2),\ldots,(2,0)\), checking inclusion in both previously chosen adjacent cells. It gives 227 patterns, of which 29 retain a free parameter. This count is only used for replay; to exclude arbitrary complex free values one needs the next step.

## 2. Algebraic reduction of every P¹ family

For each free line use the basis vector \((1,t,-1-t)\) for finite \(t\), with infinity \((0,1,-1)\). In the inverse system \(E\) the matched entries in the cell have the identity vector and this vector. In its ideal space \(F=E^\perp\) the remaining matched generator is the cross product of these two vectors. Along with offdiagonal coordinate vectors this supplies all columns on which the three tests are built.

At length 17 the multiplication matrices for \(F\cdot A^*\) and \(F\cdot B^*\) in degrees \((210),(120)\) must each have rank at most \(405-17=388\). The \((220)\) square test uses the matrix
\[
 E\otimes A\otimes B\longrightarrow\Lambda^2 A\otimes\Lambda^2 B,\qquad
 \left(\sum a_i\otimes b_i\right)\otimes a\otimes b\longmapsto
 \sum(a_i\wedge a)\otimes(b_i\wedge b).
\]
Its rank must be at most \(17\cdot81-\binom{17}{2}-289=952\), by [Mańdziuk, Corollary 4.2 and Lemma 4.6](https://arxiv.org/html/2609.12121v1#S4). This remains necessary for nonsaturated border-apolar limits.

Each matrix splits into torus weight blocks. The code encodes the nine diagonal characters by powers of 17, and entries in a column have a unique shared weight. The digit bounds in these degrees prevent weight aliasing; the split matrix rank is the sum of the block ranks. Each column is constant or affine in \(t\). In a test rejecting the generic point, the checker chooses a nonzero square minor in every nonzero-rank block by Gaussian elimination at \(t=7\bmod 101\). The resulting determinant is a nonzero **integer polynomial**, not just its reduction at that point. Its degree is bounded by the number of selected columns that depend on \(t\). At integer arguments \(0,\ldots,d\) the checker evaluates it by exact Bareiss elimination with integer pivoting, then interpolates using forward differences in the falling-factorial basis. Taking the primitive part preserves the entire zero set.

For each of the 29 patterns, one chosen test exceeds the necessary bound by summing orders of these minors; the split is 9 tests of \((210)\), 9 of \((120)\), 11 of the \((220)\) square. Every selected nonconstant minor in these rejecting tests has all its linear factors in
\[
 t+2,\qquad 2t+1,\qquad t-1.
\]
This statement is checked over the integers by exact polynomial division after clearing denominators, not inferred from a finite-field sample or from a modular GCD. Therefore each free family can satisfy its necessary tests only at \(\{\infty,-2,-1/2,1\}\). Infinity is tested separately using its homogeneous line vector. Replaying the three rank tests modulo 101 at those rational values and on the discrete patterns gives a list of 55 candidate pair spaces. Modular ranks are used only as lower bounds for complex ranks (for \(t=-1/2\) use \(50\bmod101\), valid since 2 is invertible). The count 55 describes this conservative screen, not a claim that every candidate passes the tests over \(\mathbb C\).

## 3. Cubic screen and surviving necessary patterns

For any triple \((I_{110},I_{011},I_{101})\), prolonging the three pair ideals to degree \((111)\) must have codimension at least 17. The matrix has 729 rows; a generator of a pair ideal is added for each variable of the other factor. In the checker singleton equations and opposite-coefficient two-term equations first identify coordinates with zero or with each other by union-find, and exact Gaussian elimination over \(\mathbb F_{101}\) handles the rest. It checks every ordered candidate triple up to cyclic rotation; testing only unordered triples would not justify this result.

The only remaining triple indices are \((11,k,29)\), where
\[
 k\in\{195,196,197,198,200,201,202,203,205,207,208,209,210,
 211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226\}.
\]
All are discrete and have \((111)\) codimension 17 modulo 101. Patterns 11 and 29 consist of the four cells \(i\in\{0,1\}\), \(k\in\{1,2\}\), each with the two positive roots \(\{01,02\}\) and \(\{02,12\}\), respectively, and no diagonal extras. These agree with the two residual pair shapes in the [Cartan-free certificate](Matrix3BorderApolarityCartanFree.md). The third member has Cartan directions and is selected from the enumerated local types, uniquely encoded by its index.

Even an exact finite list of discrete candidates is not a certificate of border rank at least 18. The calculation does not test all higher-degree ideals or membership in the component of limits of distinct points.

## 4. Any surviving witness would have non-apolar saturation

The pair of type 11 gives a useful structural consequence beyond discreteness. In that orientation its only allowed off-diagonal products \(a_{uv}b_{jk}\) have \(j=0\), since the positive middle roots are \(01,02\). In \(S/I\), let \(m_{ik}=a_{i\ell}b_{\ell k}\), independent of \(\ell\) by the matched-coordinate equations. For any \(a_{uv}\), choose \(\ell\in\{1,2\}\setminus\{v\}\). Then \(a_{uv}b_{\ell k}\in I\), as this is a forbidden off-diagonal, so \(a_{uv}m_{ik}=0\) in \(S/I\). Consequently all \(A\)-coordinates annihilate \(m_{ik}\) and \(m_{ik}\) belongs to the multihomogeneous saturation of \(I\). But it pairs to 1 with the \(AB\) contraction of \(M_3\) by \(c_{ki}^*\), so \(m_{ik}\notin I_{110}\). The saturation is not apolar, as also witnessed by \(m_{ik}c_{ki}\) in degree \((111)\).

Thus any actual length-17 Borel-fixed witness in this reduction must be nonsaturated. This does not exclude nonsaturated limit ideals and does not by itself give a cactus-rank bound.
