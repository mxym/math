# No 91-point spectral subset of \(\mathbb F_{13}^3\): weighted-profile stage

This is the second part of the proof, following the [geometric stage](FugledeF13Size91Geometric.md). We use its notation, line cap four, and the vanishings through degree nine in both members.

## 4. The Radon identity and full planes

For a projective line \(L\) in the normal plane, project a member \(B\) along \(L^\perp\) to \(\mathbb F_{13}^2\), with projected integer multiplicity \(f\). Here \(L^\perp\) means the one-dimensional annihilator of the associated two-dimensional normal space. Remove its uniformly seven line sums; write \(b\) for the number of remaining nonuniform directions, with profile sums \(g_i(l_i(x,y))\), where each \(l_i\) is a nonzero linear form in its distinct direction. Counting the fourteen lines through \((x,y)\) gives the integer Radon identity
\[
  \sum_{i=1}^{b}g_i(l_i(x,y))=7(b-1)+13f(x,y).
\]
Choose some uniform normal as a vertical direction and make \(l_i=y-s_i x\) for the others, with distinct \(s_i\). Modulo thirteen, the identity is formal after writing the reduced univariate polynomial for each \(g_i\). Its homogeneous degree-\(j\) part gives \(\sum_i c_{ij}s_i^h=0\) for \(0\le h\le j\), where \(c_{ij}\) is the coefficient of \(t^j\) in \(g_i\). This follows from the binomial theorem (\(j\le12<p\)); the Vandermonde matrix forces these coefficients zero for \(j\ge b-1\) and \(j>0\).

If \(L\) has at least eleven uniform normals, then \(1\le b\le3\). Every nonuniform profile is constant or affine modulo thirteen. A nonuniform profile constant modulo thirteen consists of seven \(13\)'s and six zeros: any nonzero constant residue gives a constant integer profile, necessarily uniform. If all are constant modulo thirteen, the identity gives \(7(b-1)\equiv0\pmod{13}\), so \(b=1\). Otherwise \(b=3\), and all three are nonconstant affine because any two distinct \(l_i\) are independent, so in a nonzero linear relation all three coefficients are nonzero. Each such profile has exactly the occupancies \(1,2,\dots,13\), as its residues run through the field and its sum is \(91\). In either case, every nonuniform profile of this pencil has a full thirteen-point plane.

Now if \(v\) is the normal of a full thirteen-point plane of \(B\), the geometric verifier and spectrality give at least eleven uniform points on \(v^\perp\) for the partner \(B'\). At least one of its nonuniform points \(w\in v^\perp\) must exist (no projective line is all uniform) and has a full plane of \(B'\) by the high-pencil calculation. Applying the same argument to \(w\) gives a high-uniform pencil \(w^\perp\) in \(B\). Its point \(v\) is nonuniform because it has a full plane, and its profile must consequently be one of the previously stated two types. This proves that a nonuniform profile with any occupancy thirteen is either constant modulo thirteen (type \(C\): \(13^7,0^6\)) or nonconstant affine modulo thirteen (type \(R\): \(1,2,\dots,13\)). In particular a genuine quadratic profile has all occupancies at most twelve.

## 5. Tight weighted lines exclude genuine quadratic profiles

The moment vanishings through degree nine imply that every occupancy profile, modulo thirteen, is quadratic or lower. Indeed the annihilator of evaluations of \(1,\dots,t^9\) is the three-dimensional space of evaluations of \(1,t,t^2\). For a projective normal \(v\) with occupancies \(n_j\), define
\[
 q_B(v)=\sum_j\binom{n_j}{2},\qquad
 k_B(v)=(q_B(v)-13\binom72)/13 .
\]
Then \(k_B=0\) exactly on \(U_B\), by convexity. The affine and layered nonuniform profiles have \(k_B=7\) and \(k_B=21\), respectively. For a genuine quadratic profile, translating its input gives \(n_j\equiv c+a j^2\pmod {13}\) with \(a\ne0\). The [arithmetic verifier](verify-fuglede-f13-size91-arithmetic.js) tries all \(12\cdot13\) centered polynomials and counts how many residues zero must be lifted to thirteen to obtain mass 91. It finds 96 possibilities for \((a,c)\) including allowable lifts, and in all cases \(k_B\) is an integer at least four. This computation is valid even before imposing that such a quadratic cannot have a full plane; in the actual proof we impose the latter when enumerating tight pencils.

Let \(T_B(d)\) count unordered pairs of \(B\) in projective difference direction \(d\). Write \(J\) for the all-ones matrix and \(P\) for the projective polarity incidence matrix \(P_{v,d}=\mathbf1_{v\cdot d=0}\). Then \(P^2=13I+J\), \(P\mathbf1=14\mathbf1\), and \(P T_B=q_B\). Applying \(P\) again and substituting \(\sum_d T_B(d)=\binom{91}{2}=4095\) yields
\[
 T_B=P k_B-21\mathbf1,\qquad \sum_v k_B(v)=567.
\]
In particular if \(d\in V_{B'}\) then \(d\notin D(B)\), and the line \(d^\perp\) is tight: \(\sum_{v\in d^\perp} k_B(v)=21\). Such a line has at most five nonuniform points, because each positive weight is at least four.

A tight line cannot have five nonuniform points unless their weights are \(4,4,4,4,5\), in which case all five are genuine quadratics. If it has four nonuniform points, none can be type \(C\) (weight 21). If any profile is genuinely quadratic, all four are: the degree-two part of the Radon identity cannot have a nonzero relation between at most three quadratic forms \(l_i^2\) in distinct projective directions, by the Vandermonde argument. Without any genuine quadratic all four would be type \(R\) of weight seven, which is not tight. Thus both the four- and five-profile cases require all profiles genuine quadratic with no lifts to thirteen.

The arithmetic verifier excludes both cases using the following complete search, not a grid search over hypothetical sets. Three distinct projective directions can be sent to forms \(x,y,x+y\) by an invertible linear change, allowing scalar rescaling of each form. The remaining forms are \(x+s y\) and optionally \(x+t y\), with \(2\le s<t\le12\) in the five-profile case, \(2\le s\le12\) in the four-profile case. Write the centered residue profiles \(c_i+a_i(l_i-h_i)^2\). Their nonzero leading coefficients must have quadratic sum zero. Choosing the last one or two \(a_i\)'s freely determines the first three from the coefficients of \(x^2,xy,y^2\). Translate \(x,y\) to set the first two centers zero. The linear coefficient equations then determine the next two centers in terms of the last center (if present), using independence of \(x+y,x+s y\). For each \(a_i\), the allowed \(c_i\)'s have mass 91 from least residues (no lift) and record \(k_B(v)\). Their weights must sum to 21. Finally, the constant equation is
\(\sum_i(c_i+a_i h_i^2)=7(b-1)\) modulo thirteen. At four profiles the checker sees 11 masks, 132 leading vectors and 264 choices of centered constants with weight 21; at five it sees 55, 5940 and 900, respectively. None passes the constant equation for any allowed centers.

Therefore every tight line has at least eleven uniform points, and its nonuniform profiles are only the \(C\) or \(R\) types by Section 4. Every normal \(v\in V_B\) lies on such a line: \(V_{B'}\) is blocking (as \(U_{B'}\) has no complete line), so choose \(d\in V_{B'}\cap v^\perp\). Thus all profiles are of type \(U,C,R\), with weights \(0,21,7\). All occupancies now have affine residues, so \(M_{10}^B=0\) by the field power sums. The projective contradiction is in the [closing note](FugledeF13Size91FinalIncidence.md).
