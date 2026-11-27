# No 65-point spectral subset of \(\mathbb F_{13}^3\)

**Theorem.** No subset of cardinality 65 of \(\mathbb F_{13}^3\) is spectral. This removes one cardinality in the finite-field Fuglede problem; it does not settle the entire field.

The geometric inputs are [no layered member](FugledeF13Size65NoLayers.md) and [vanishing moments through degree eight](FugledeF13Size65MomentsEight.md), for both members \(E,A\) of a hypothetical spectral pair. The plane cap is 13 from the elementary spectral-pair reductions. The new step is a bound on the *sum of squares* of weights in every tight projective pencil, followed by weighted projective incidence mixing. Degree-nine moment vanishing is not needed.

## 1. Weights and tight pencils

For \(B=E,A\), let \(n_t(v)\) count points with \(v\cdot x=t\), for a representative of a projective normal \(v\). Let \(U_B\) be the uniform normals (all counts 5), and \(V_B\) their complement. On \(\mathbb F_{13}\), the orthogonal complement of the evaluations of \(1,t,\dots,t^8\), under the unweighted bilinear pairing, is the evaluation space of polynomials of degree at most three. Indeed the product degrees are at most eleven and all field power sums through eleven vanish, and the dimensions are complementary. Thus every profile is cubic or lower as a residue class function.

Write \(q_B(v)=\sum_t\binom{n_t(v)}2\), and \(w_B(v)=(q_B(v)-130)/13\). Power sums applied to the polynomial of degree at most six for \(\binom{n_t(v)}2\bmod 13\) show that these weights are integers. They are nonnegative by convexity and vanish exactly on \(U_B\). A constant residue is either an integer constant five or a layered profile (five counts 13, eight zeros); layers were excluded. A nonconstant affine residue profile has least-residue sum 78, above 65. Therefore every nonuniform profile is genuinely quadratic or cubic.

For projective polarity let \(P_{v,d}=1\) when \(v\cdot d=0\) and zero otherwise. It satisfies \(P^2=13I+J\) and \(P\mathbf 1=14\mathbf 1\), where \(J\) is all-ones on the 183 projective points. If \(T_B(d)\) counts unordered pairs of \(B\) with projective difference direction \(d\), then \(q_B=P T_B\) and \(\sum T_B=\binom{65}{2}=2080\). These identities give
\[
 T_B=P w_B-20\mathbf 1,\qquad \sum_v w_B(v)=410.
\]
For every normal \(d\in V_{B'}\) of the other member, \(T_B(d)=0\): spectral orthogonality gives \(D(B)\subset U_{B'}\). Call its perpendicular line tight; its weights sum to 20.

## 2. Local squared weights

Project along \(d\) for a tight line \(d^\perp\). For its \(b\) nonuniform profiles \(g_i\) in distinct linear forms \(l_i\), the integer planar Radon identity is
\[
 \sum_i g_i(l_i(x,y))=5(b-1)+13 f(x,y),
\]
where \(f\) is the projected multiplicity. This counts the 14 affine lines through \((x,y)\), with all other points counted once. In particular the left side is constant modulo 13 as a formal polynomial: its degree is below 13 in each variable. In homogeneous degree \(j\le 3\), any \(j+1\) distinct projective powers \(l_i^j\) are independent (Vandermonde in a chart with all these directions finite). Thus no genuine cubic occurs for \(b\le4\) and no genuine quadratic for \(b\le3\). Tight weight 20 precludes \(b=0\), and the exclusion of affine and layered profiles therefore gives \(b\ge4\).

The [quadratic](verify-fuglede-f13-size65-quadratic-tight.js) and [cubic](verify-fuglede-f13-size65-cubic-tight.js) exact verifiers center each degree-two profile as \(a t^2+c\) and each degree-three profile as \(a t^3+c t+d\), \(a\ne 0\), by a translation of the input. Counts in \([0,13]\) are the least residues, except that zeros can be lifted to thirteen. The mass determines the number of lifts, independent of their locations for the weight. The enumeration gives minimum weight 4 for a genuine quadratic and 3 for a genuine cubic. Thus \(b\le6\).

* At \(b=4\) all profiles are quadratic. Normalize the pencil to \(x,y,x+y,x+s y\), \(2\le s\le12\). Try the last quadratic coefficient and use the homogeneous degree-two equation to determine the first three. Translate the plane to center the first two quadratics. The homogeneous degree-one equation forces the remaining two centers zero, since their two forms are independent. The complete mass/weight/constant-residue census gives only the multiset \((4,4,6,6)\), squared sum 104.
* At \(b=5\), if there is no genuine cubic, all weights are four. If there is a genuine cubic, all five are genuine by the degree-three independence rule. Normalize to \(l_i=x,y,x+y,x+s y,x+t y\), \(2\le s<t\le12\). Try the last two nonzero leading coefficients; the cross-term equations determine and check the third coefficient, then the pure powers determine the first two. Translate the plane to center the first two cubics. Now the degree-two equation in the last three independent squared forms forces all their centers zero, because those quadratic coefficients are minus three times their centers times the nonzero leading coefficients. Choose mass-65 centered profiles and check aggregate weight 20, zero linear sum and constant sum \(5(5-1)\bmod 13\). These necessary tests leave exactly 2,160 normalized tuples, with weights \((3,3,4,4,6)\) in 1,800 cases and \((3,3,3,3,8)\) in 360. Their squared sums are 86 and 100.
* At \(b=6\), no further computation is needed. Six integer weights each at least three and summing to twenty have squared sum at most \(5^2+5\cdot3^2=70\).

Consequently on every tight pencil the sum of squared weights is at most 104. These arithmetic tests do not assume that a residue-compatible tuple extends to a globally valid configuration.

## 3. Incidence contradiction

Multiply the tight-pencil bound at \(d\in V_A\) by \(w_A(d)\) and sum; after interchanging the sums, the inner sum at \(v\in V_E\) is exactly \((P w_A)(v)=20\). Therefore
\[
 20\|w_E\|^2\le104\cdot410,\qquad
 20\|w_A\|^2\le104\cdot410.
\]
The squared norms are at most 2132. On the mean-zero subspace \(P\) has operator norm \(\sqrt{13}\) since \(P^TP=13I+J\). Removing the mean \(410/183\) from both weights yields
\[
 w_A^TPw_E \ \ge\
 \frac{14\cdot410^2}{183}
 -\sqrt{13}\left(2132-\frac{410^2}{183}\right)
 >8200.
\]
The strict inequality is the exact integer comparison \(852800^2>13\cdot222056^2\). Yet tightness makes the left side exactly \(20\cdot410=8200\), a contradiction.

This argument builds on finite-field moment and weighted-pencil methods, in particular [Fallon, Mayeli and Villano](https://arxiv.org/abs/1902.02936) and [Ferguson and Iosevich](https://arxiv.org/abs/2610.30712) for smaller primes, and complements [Malikiosis's high-cardinality bound](https://doi.org/10.1007/s43670-023-00078-2). Taking the separate field-13 exclusions for sizes 78, 91, 104 and 117 into account, and Malikiosis's large-size bound, the remaining nontrivial candidate sizes for this field are 26, 39 and 52.
