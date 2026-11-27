# Size 78 in \(\mathbb F_{13}^3\): tight-profile divisibility contradiction

**Theorem.** No spectral subset of \(\mathbb F_{13}^3\) has 78 points. Complete proof: first use [the grid stage](FugledeF13Size78GridMoments.md) and [the cross-moment stage](FugledeF13Size78CrossMoments.md) to obtain moment vanishings through degree nine. The remainder is given here, with the exact verifier [verify-fuglede-f13-size78-tight.js](verify-fuglede-f13-size78-tight.js). This is a cardinality exclusion in finite-field Fuglede, not a resolution at all cardinalities.

## 5. Profiles on the tight pencils

Write \((E,A)\) for a hypothetical size-78 spectral pair, with \(D(B)\) the projective directions of nonzero differences, \(U_B\) the uniform normals of a member \(B\), and \(V_B\) the complement of \(U_B\) in \(\mathrm{PG}(2,13)\). We use plane cap 13 and the degree-nine vanishings, no line cap beyond what was needed to prove them. If \(n_t\) are the thirteen affine plane occupancies of \(B\) at any normal, \(0\le n_t\le13\) and their residues are evaluations of a quadratic or lower polynomial. This follows from orthogonality of the profile to the evaluation vectors of \(1,t,\dots,t^9\) and the three-dimensional complementary space spanned by \(1,t,t^2\). Assign the weight
\[
 w_B(v)=\frac{\sum_{t}\binom{n_t}{2}-13\binom62}{13}.
\]
It is zero exactly on \(U_B\) by convexity. The possible nonuniform profile types are:
- \(C\): constant residue, hence six entries 13 and seven zeros. Weight 21.
- \(R\): affine but nonconstant residue, hence exactly the occupancies \(0,1,\dots,12\) (mass 78 precludes representing the zero residue by 13). Weight 7.
- \(Q\): genuinely quadratic residue, of form \(c+a(t-h)^2\), \(a\ne0\). Its weight is an integer at least four, as checked below.

For reference, let \(P\) be the projective polarity matrix \(P_{v,d}=\mathbf1_{v\cdot d=0}\) with \(P^2=13I+J\), \(P\mathbf1=14\mathbf1\). The vector of sum-of-pair occupancies \(q_B\) equals \(P T_B\) where \(T_B(d)\) counts unordered pairs of difference direction \(d\). Applying \(P\) sends \(q_B\) to \(13T_B+\binom{78}{2}\mathbf1\). Substituting \(q_B=13w_B+195\mathbf1\) yields
\[
 T_B=P w_B-21\mathbf1,\qquad \sum_v w_B(v)=489 .
\]
If \(B'\) is the other member, \(D(B)\subset U_{B'}\); for each \(d\in V_{B'}\) the projective line \(d^\perp\) has total \(w_B\) weight 21, and is called tight. The positive weights are at least four, so its number \(b\) of nonuniform normals satisfies \(1\le b\le5\).

For a tight pencil project along the annihilator of its two-dimensional normal space to the affine plane. The Radon identity used in the 91-point proof is now \(\sum_{i=1}^{b}g_i(l_i(x,y))=6(b-1)+13 f(x,y)\), where \(g_i(l_i(x,y))\) are its nonuniform line sums. After reduction modulo 13 the Vandermonde relation at homogeneous degree \(j\) forces each coefficient of degree \(j\ge b-1\) to vanish, for \(j>0\).
- If \(b=1\), the bad profile has constant residues, giving a single \(C\) of weight 21.
- If \(b=2\), all bad profiles have constant residue zero, impossible because \(6(b-1)\not\equiv0\).
- If \(b=3\), all profiles are affine; they cannot all have constant residue zero, and the linear relation in three distinct projective directions requires all three to be nonconstant (any two independent). This gives three \(R\)'s, weights \(7,7,7\).
- If \(b=4\), no \(C\) can fit with other positive weights. If all were \(R\), the weight would be 28. Thus there is a genuine quadratic, and the degree-two relation among forms in distinct directions forces all four to be genuine quadratics (no nonzero relation among at most three such squared forms).
- If \(b=5\), the weights must be \(4,4,4,4,5\); in particular all are genuine quadratics.

For the exact arithmetic check, translate a genuine quadratic's argument to \(a t^2+c\), test every \(a\ne0,c\), take least residues, and assign exactly \((78-\sum \mathrm{residues})/13\) zeros to occupancy 13 if this is an integer in the allowed range. This number determines the weight independently of which zeros are lifted. There are 96 admissible centered profiles; all weights are integers at least four.

For \(b=4,5\) the checker normalizes three directions to \(x,y,x+y\), with the others \(x+s y\) for \(s\in\{2,\dots,12\}\). In \(g_i(l_i)=c_i+a_i(l_i-h_i)^2\), the free last one or two nonzero \(a_i\)'s determine the first three by the quadratic equation \(\sum a_i l_i^2=0\). Translation makes the first two \(h_i\) zero; the next two are then determined by \(\sum a_i h_i l_i=0\) from the last \(h_i\), free only when \(b=5\). For each leading choice it tests every centered mass-78 profile of each coefficient, all permitted zero lifts (via their count, which does not affect the residue congruence), and requires the weights sum 21. It tests the remaining constant congruence \(\sum_i(c_i+a_i h_i^2)=6(b-1)\) modulo 13. For \(b=4\) there are 2160 weight-qualified centered tuples, with 48 surviving that congruence, all with weights \(4,4,4,9\). For \(b=5\) there are 1800 weight-qualified tuples and 900 survivors, all with weights \(4,4,4,4,5\). All surviving profiles use no lifts. These tests are necessary conditions, so no assumption of realizing any of the survivors is needed.

## 6. Divisibility in the polarity graph

Consider the bipartite graph of projective incidence between \(V_E\) and \(V_A\): \(v\) and \(d\) are neighbors when \(v\cdot d=0\). Every vertex has total neighbor weight 21, so none is isolated. By the tight-pencils classification its neighbors are all one type (\(C\), \(R\), or \(Q\)), and in the \(Q\) case exactly one neighbor has higher weight than four (five or nine). Thus each connected component is of constant type on each of its sides: any two vertices joined by a length-two path on one side are of the same type, and general same-side connectivity concatenates such paths.

For each component the total weight on either side is equal. Indeed \(\sum_{(v,d)\text{ edge}} w_E(v)w_A(d)\) restricted to the component equals \(21\sum_v w_E(v)\) as well as \(21\sum_d w_A(d)\). If either side is type \(C\) or \(R\), the component's weight on each side is divisible by seven. In a \(Q\)-to-\(Q\) component, sum the \(E\)-weight incident to the higher-weight vertices on the \(A\) side. Each \(E\)-vertex is counted exactly once because it has precisely one such neighbor, and each higher-weight vertex in \(A\) has neighbor weight 21. Thus the component's \(E\)-total is again divisible by seven. Summing over all components gives \(7\mid489\), which is false. This concludes the proof.

Combined with the exclusions of sizes 91, 104 and 117, only sizes \(26,39,52,65\) remain possible for a spectral counterexample in \(\mathbb F_{13}^3\).
