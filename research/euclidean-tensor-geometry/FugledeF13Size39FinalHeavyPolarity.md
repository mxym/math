# No 39-point spectral subset of \(\mathbb F_{13}^3\)

**Theorem.** No 39-point subset of \(\mathbb F_{13}^3\) is spectral.

For a hypothetical spectral pair \(E,A\), the [geometric stage](FugledeF13Size39MomentsFiveNoLayers.md) excludes layers and limits the number of uniform normals on any projective line to eight. The [sixth-moment stage](FugledeF13Size39MomentsSix.md) proves all mixed moments through degree six vanish and bounds every affine plane section by nine sites. The final proof below does **not** assume that degree-seven moments vanish.

## Weights and two seventh-moment curves

For either member \(B\), let \(n_t(v)\) count points on the plane \(v\cdot x=t\), and put
\[
 w_B(v)=\frac{\sum_t\binom{n_t(v)}2-39}{13},\qquad V_B=\{v:w_B(v)>0\}.
\]
Moment orthogonality gives plane-count residues of degree at most five. The pair-count polynomial of degree at most ten sums to zero modulo thirteen, so the \(w_B(v)\) are integers, positive exactly at nonuniform normals. Let \(P_{v,d}=\mathbf1_{v\cdot d=0}\) be projective polarity, so \(P^2=13I+J\) and \(P\mathbf1=14\mathbf1\). As in the [arithmetic reduction](FugledeF13Size39ConditionalMomentSevenEndgame.md), the unordered difference counts satisfy
\[
 T_B=P w_B-15\mathbf1,\qquad \sum_v w_B(v)=249.
\]
For each \(d\in V_{B'}\) of the opposite member \(B'\), \(d\notin D(B)\), hence the line \(d^\perp\) is tight: its \(B\)-weights sum to 15. This gives a bipartite incidence graph on \(V_B,V_{B'}\). Write \(b_d\) for the number of positive weights on \(d^\perp\).

Define \(F_B(v)=\sum_{x\in B}(v\cdot x)^7\). The coefficient of degree five of the reduced profile at \(v\) is \(-F_B(v)\), by the field power sums. Thus \(F_B(v)\) is nonzero precisely at genuinely quintic profiles. Both polynomials \(F_E,F_A\) are nonzero: otherwise the [one-sided quartic counting contradiction](FugledeF13Size39ConditionalMomentSevenEndgame.md) applies on whichever member has all profiles of degree at most four. Also, \(F_{B'}\) vanishes on \(D(B)\), because \(D(B)\) is contained in the uniform normals of \(B'\).

## Local bounds and large-plane normals

The profile verifiers give \(1\le w_B(v)\le 6\) at every positive weight. Constant nonuniform residues (layers), affine residues and genuine quadratics do not occur; cubics have weight 3, and the quartic and quintic bounds are in the [quartic](verify-fuglede-f13-size39-quartic-tight.js) and [quintic](verify-fuglede-f13-size39-quintic-seven.js) verifiers.

There are at least six positive weights on each tight pencil, because at most eight normals are uniform. On a tight pencil of exactly six profiles, the Radon relations make each profile of degree at most four, and the exact census leaves only weights \((2,2,2,2,3,4)\), with squared sum 41. On a tight pencil of exactly seven profiles with no quintic the weights are \((2,2,2,2,2,2,3)\), with squared sum 33. With at least one quintic, the exact seven-profile census yields squared sum at most 47. Additionally, the verifier shows that **at least two** of the seven profiles each have some occupancy at least eight. In the five projective mask normalizations already used in the arithmetic reduction, two surviving tuples have two such profiles and ten have three.

For \(b_d\ge8\), the elementary maximum of the squared sum among \(b_d\) positive integer weights at most six summing to fifteen is obtained by concentrating all excess over one into as few coordinates as possible. For example \(b_d=8\) gives \((6,3,1,1,1,1,1,1)\) with squared sum 51, and \(b_d=9\) gives 47. In every case, including \(b_d=6,7\), the squared sum \(S_d\) satisfies
\[
 S_d\le 4b_d+19.
\]

Call \(v\in V_B\) a large-plane normal if \(n_t(v)\ge8\) for some \(t\). Every eight-site configuration in an affine plane of \(B\) determines at least eight directions. Indeed it has no four collinear points, and the [exact planar verifier](verify-fuglede-f13-size39-heavy-incidence.js) finds that a noncollinear planar set with this cap and at most seven directions has size at most seven. It fixes a triangle, enumerates all 330 seven-direction masks containing its three directions and visits 40,771 compatible recursive nodes. Thus \(F_{B'}\) has at least eight zeros on the projective line \(v^\perp\), so that line divides this nonzero degree-seven form. There are at most seven distinct large-plane normals in \(B\).

## Weighted support has size at least 124

Partition tight pencils into three classes:
1. No genuinely quintic profile. Then \(F_B\) vanishes on the entire projective line, so the line divides \(F_B\). There are at most seven such pencils and their total opposite weight is at most \(7\cdot6=42\). Their \(b_d\) are at least six.
2. At least one genuinely quintic profile and \(b_d=7\). By the exact census every such line contains at least two large-plane normals. Each large-plane normal \(v\) has opposite neighbor weight sum 15 by \(T_{B'}(v)=0\). Therefore the total opposite weight of this class is at most \(7\cdot15/2\).
3. All other pencils. If a quintic occurs at all, independence of any six fifth powers in the Radon relations gives \(b_d\ge7\); consequently this remaining class has \(b_d\ge8\).

Put \(N_B=|V_B|\). Count weighted edges, with weight \(w_{B'}(d)\) attached to the opposite endpoint. This gives
\[
 15N_B=\sum_{d\in V_{B'}} w_{B'}(d)b_d
 \ge8\cdot249-2\cdot42-\frac{7\cdot15}{2}=1855.5.
\]
Hence \(N_B\ge124\), for either member.

## Mixed incidence contradiction

Multiply \(S_d\le4b_d+19\) by \(w_{B'}(d)\) and sum. Tightness at each endpoint gives
\[
 15\|w_B\|^2\le4\cdot15N_B+19\cdot249.
\]
Exchange \(E,A\) if necessary so that \(N_A\ge N_E=N\). The exact mixed incidence \(\mathbf1_{V_A}^{T}P w_E=15N_A\) and \(P^TP=13I+J\) imply
\[
 \left\|w_E-\frac{249}{183}\mathbf1\right\|^2
 \ge
 \frac{(14\cdot249/183-15)^2N_A}{13(1-N_A/183)}
 \ge
 \frac{(14\cdot249/183-15)^2N}{13(1-N/183)}.
\]
The interval is \(124\le N\le182\), as each member has some uniform normal from the other's nonempty difference set. For each integer \(N\) in that interval the last expression exceeds \(4N+19\cdot249/15-249^2/183\), the upper bound from the squared weights. Clearing positive denominators, the [integer verifier](verify-fuglede-f13-size39-heavy-incidence.js) finds a minimum positive gap of \(26278434\). This is a contradiction.

The geometric input adapts [Ferguson and Iosevich's \(p=11\) methods](https://arxiv.org/abs/2610.30712); here the high-occupancy profile count and two nonzero seventh-moment curves replace the need to prove seventh-moment vanishing. With the separate cardinality exclusions already proved, only size 26 remains for the finite-field Fuglede problem over \(\mathbb F_{13}^3\).
