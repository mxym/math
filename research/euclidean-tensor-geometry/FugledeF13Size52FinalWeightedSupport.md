# No 52-point spectral subset of \(\mathbb F_{13}^3\)

**Theorem.** No subset of cardinality 52 of \(\mathbb F_{13}^3\) is spectral.

The [geometric and moment stage](FugledeF13Size52MomentsSevenNoLayers.md) excludes all layered members of a hypothetical spectral pair and gives vanishing mixed moments through degree seven. The final contradiction uses *mixed* incidence between one support indicator and the other occupancy weight, rather than between two weight vectors. It requires a census of individual profiles and the possible leading coefficients of a four-profile pencil, not a census of cubic or quartic pencils.

## Occupancy weights

For either member \(B\), let \(n_t(v)\in[0,13]\) be its thirteen parallel plane counts at a projective normal \(v\). Degree-seven moment vanishing implies that the residues of each profile are a reduced polynomial of degree at most four: evaluations of polynomials of degree at most four annihilate those of degree at most seven by the field power sums, and the dimensions add to thirteen. Constant residue profiles are uniform (all four) or layered (already excluded); nonconstant affine profiles have least-residue mass 78, so do not occur.

With \(V_B\) the nonuniform normals, put
\[
 w_B(v)=\frac{\sum_t\binom{n_t(v)}2-13\binom42}{13}.
\]
Weights are nonnegative and vanish precisely outside \(V_B\). They are integers since the polynomial of degree at most eight representing the pair count modulo thirteen sums to zero. Let \(P\) be projective polarity, \(P_{d,v}=\mathbf1_{d\cdot v=0}\), with \(P^2=13I+J\) and \(P\mathbf1=14\mathbf1\). For unordered difference pair counts \(T_B\), applying \(P\) to \(P T_B=78\mathbf1+13w_B\) and using \(\sum_dT_B(d)=\binom{52}{2}=1326\) gives
\[
 T_B=P w_B-18\mathbf1,\qquad
 \sum_vw_B(v)=330.
\]
If \(d\) belongs to the partner's \(V\), spectrality gives \(T_B(d)=0\). Thus \(d^\perp\) has weight sum eighteen; call it a tight pencil.

## Local bound on a tight pencil

For \(b\) nonuniform directions on that pencil, project along \(d\). The planar Radon identity is
\[
 \sum_{i=1}^{b} g_i(l_i(x,y))=4(b-1)+13f(x,y)
\]
for distinct projective forms \(l_i\). The contribution in each positive homogeneous degree vanishes modulo thirteen. In degree \(j\le4\), any \(j+1\) distinct projective powers \(l_i^j\) are independent. Consequently no pencil with \(b\le3\) can have a nonuniform profile, no \(b=4\) pencil contains a cubic or quartic profile, and no \(b=5\) pencil contains a quartic profile.

The [exact verifier](verify-fuglede-f13-size52-weighted-support.js) enumerates each degree \(j=2,3,4\) profile \(at^j+\sum_{i=0}^{j-2}c_i t^i\) with \(a\ne0\). The missing \(t^{j-1}\) term is removed by translating the input. The mass determines how many zero residues must be lifted to thirteen; each lift contributes 78 to the pair count. The minimum positive weights are respectively 4, 3 and 2. Quadratics have only weights four or six. For four nonuniform directions normalize the forms to \(x,y,x+y,x+s y\), \(2\le s\le12\). Testing the last nonzero coefficient \(a_3\) determines all others by the quadratic relation. None of the 132 resulting leading vectors admits profile weights summing to eighteen. For comparison, the exclusion of a 52-point **Boolean planar projection** with exactly four special directions is already given by [Qihang Wang, Appendix A](https://arxiv.org/html/2609.20495v2#A1); the tight-pencil case projects injectively because its direction is absent from the difference set. Our arithmetic check is directly on the weights. Thus every tight pencil has \(5\le b\le9\).

Write \(S=\sum w^2\) on a tight pencil. If \(b=5\) its weights are at least three, giving \(S\le6^2+4\cdot3^2=72\). If \(b=6\) they are at least two, giving \(S\le8^2+5\cdot2^2=84\). For \(7\le b\le9\) the latter minimum gives \(S\le60\). In every case \(S\le12b+12\).

## Mixed incidence closes the proof

Write \(N_B=|V_B|\). For each \(d\in V_A\), multiply its tight pencil inequality by \(w_A(d)\), and sum. Interchanging the sums uses \((P w_A)(v)=18\) at each \(v\in V_E\), so
\[
 18\|w_E\|^2\le12\cdot18N_E+12\cdot330,\qquad
 18N_E=\sum_{d\in V_A}w_A(d)b_d\ge5\cdot330.
\]
The same holds with \(A,E\) interchanged. Hence \(92\le N_B\le165\) (the upper bound uses minimum positive weight two), and \(\|w_B\|^2\le12N_B+220\).

Exchange members if necessary to have \(N_A\ge N_E=N\). The exact mixed incidence \(\mathbf1_{V_A}^{\,T}P w_E=18N_A\), together with \(\|P\|=\sqrt{13}\) on the mean-zero subspace, gives
\[
 \left\|w_E-\frac{330}{183}\mathbf1\right\|^2
 \ge \frac{(14\cdot330/183-18)^2\,N_A}{13(1-N_A/183)}
 \ge \frac{(14\cdot330/183-18)^2\,N}{13(1-N/183)}.
\]
This contradicts \(\|w_E-(330/183)\mathbf1\|^2\le12N+220-330^2/183\): clearing positive denominators, the difference has the sign of
\[
 (14\cdot330-18\cdot183)^2 N
 -13(183-N)\bigl(183(12N+220)-330^2\bigr).
\]
The verifier checks all 74 integer cases; the minimum is \(3958656>0\).

Together with the other cardinality exclusions, this leaves 26 and 39 as the remaining nontrivial sizes for Fuglede over \(\mathbb F_{13}^3\). The present theorem does not settle either of those sizes.
