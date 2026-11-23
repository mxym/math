# Sixth-degree site tests for the three simultaneous positive field shells

Continue the notation of [the simultaneous tensor](hoffman-positive-short-field-tensor.md). Set R_i(b), B_i(b), Y_i(b) to the numbers of oriented norm 56,70,112 fields in the chosen saturation for which |f_b|=i. If the saturation has no roots (R=0), every exterior site b has at least 168 distinct Y fields with |f_b| at least three. This makes no claim that one can choose the saturation with R=0.

## Exact angular identities

For any homogeneous harmonic polynomial H_d on the 33-dimensional residual space, write R(H_d), B(H_d), Y(H_d) for the sums on the three lattice shells of norms 2,5/2,4 *before* the evaluation scaling. Then

    Y(H_2) = -414 R(H_2) - 56 B(H_2);
    Y(H_4) =  282 R(H_4) + 88 B(H_4);
    Y(H_6) = -174 R(H_6) - 56 B(H_6).

The first is the traceless part of the simultaneous tensor. For the other two pass to its same E7 gluing U of rank 40. In weight 26 the full-level cusp space is the line spanned by Delta E14, with q^2 coefficient -48 times the q coefficient. Apply this first to H_6(x) on U. The norm-four shell projects with the usual 126 and 56 multiplicities and the roots project with multiplicity one (the auxiliary-only projections vanish). This gives -48-126=-174. Next apply to H_4(x)(|x|^2-41|e|^2/7), where e is the 7-dimensional coordinate. This is harmonic: the two Laplacians on the products give 82H_4 and 14H_4 respectively. The multipliers for Y, R paired with E7 norms two, and B paired with E7 norms 3/2 are respectively 4, -68/7, -44/7; at norm two on the T roots the multiplier is 2. Hence 4Y-1224R-352B=-96R, giving the stated identity.

Define eta(s)=s^2(s^2-1)(s^2-4)/360. At every b,

    sum_i eta(i) Y_i(b)
       = 76 B_0 + 56 B_1 + 44 B_2 + 128 B_3 + 268 B_4 + 16 B_5
         -72 R_0 -147 R_1 -232 R_2 -81 R_3 + 136 R_4.

Here is a short exact rational recipe to check the elimination independently. With s=(x,m_b), u=|x|^2, use H_d(s,u)=sum_h a_h(12u)^h s^(d-2h), a_0=1 and a_h/a_(h-1)=-(d-2h+2)(d-2h+1)/(2h(33+2d-2h-2)). The Laplacian vanishes termwise. At u=4 the coefficients of eta in H_0,H_2,H_4,H_6 respectively are 1048/25641, 4441/43290, 103/2952, 1/360. On the right replace each by the same H_d evaluated at u=2,5/2 with the associated shell multipliers above. For d=0 use Y=1549B-2880R, just Y=92940+218R and B=60+2R. The resulting values at the integer magnitudes are precisely the displayed coefficients. Cauchy gives i≤4,5,6 respectively for R,B,Y.

## Why at least 168 fields at every site in the rootless case

If R=0, the positive-shell extreme-site injection gives B_5=0. All remaining B coefficients are at least 44 and B has size 60, so the displayed left side is at least 2640. At i=0,1,2,3,4,5,6 the eta values are 0,0,0,1,8,35,112. It remains essential to limit the number with i≥5.

Each y∈T of norm four with positive evaluation 6 gives y-m_b/2 of norm one. Differences of distinct such vectors are in the rootless even lattice T, hence have norm at least four. Consequently there can be at most two; they occur in the complementary pair y,m_b-y (the only way for these unit vectors to be at squared distance four is to be opposite). They are distinct since |m_b/2|²=3. For n vectors y∈T_4 with positive evaluation ≥5, k of which have evaluation 6, each distinct pair has inner product at most two by the same minimum. Cauchy gives

    (5n+k)^2 ≤ |m_b|² |sum y|² ≤ 24 n(n+1).

For k=2 this implies n=2; there are four oriented fields at magnitude six and none at five, so the remaining 2192 of angular mass requires at least 274 further fields at magnitudes three or four. For k=0 it gives n≤24; at most 48 oriented fields have magnitude five. If h counts all fields of magnitude at least three, the weighted mass is then at most 8h+(35-8)48. Thus h≥(2640-1296)/8=168. These are simultaneous true graph evaluations, conditional on that saturation being rootless; this constraint alone does not exclude the graph.