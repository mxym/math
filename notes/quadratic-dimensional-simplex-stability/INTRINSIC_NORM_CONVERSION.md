# Intrinsic norm conversion from first-moment anchors to relative projection errors

Written mathematical proof, 7 October 2026; included in the independent analytic model audit. This refinement is separate from the earlier releases.

## Inputs and conclusion

Use the invariant and actual convex-body cone law in [imports/POLYNOMIAL_REFINEMENT.md](imports/POLYNOMIAL_REFINEMENT.md), Section 3, and the exact [cone-law source](sources/entry005-v3.md), Section 4. Write n=d+1, d>=3, and e=e(K)>=0. Let S be any prescribed maximum-volume simplex in K; translate its centroid to zero. No Euclidean normalization is needed.

Put Q=K-K and define the norm N(y)=h_Q(y), whose dual norm on u is the gauge p_Q(u). Then the [integrated assignment theorem](imports/weighted_anchors.md) supplies d+1 support anchors and an assignment with

    h = E N(X-w_I) <= C e/(1+n e) <= C e,
    C = (d+1)^3(d+2).

If h<1/(2d), their polar simplex P contains K and satisfies P subset 2dQ. For every unit projection direction u,

    0 <= [pi_P(u)-pi_K(u)]/pi_P(u) <= 3d^2 h.

In particular, with H=3d^2(d+1)^3(d+2), e<=1/H gives a genuine enclosing simplex P and relative projection deficits <=H e. These estimates contain no Euclidean radius factor and no exponentially large volume comparison.

## 1. Maximum-simplex asymmetry and support diameter

Let alpha_i be the barycentric coordinates of S. Replacement maximality gives |alpha_i(x)|<=1 for x in K. The barycentric coordinates of -x/d in S are (1-alpha_i(x))/d; they are nonnegative and sum to one. Therefore

    -K subset dS subset dK.

For a support point x of the cone law, h_K(x)=1. Hence

    N(x)=h_K(x)+h_K(-x)<=d+1=n.

The diameter of the support in this norm is <=2n. The frozen integrated assignment theorem has factor n(n+1)/2 and D/B=n e/(1+n e). Multiplication gives precisely C=n^3(n+1), with the displayed denominator preserved.

## 2. Intrinsic directional dispersion

For nonzero u, use the homogeneous projection function pi_K(u)=||u||_2 |K projected onto u-perp|. Let v=u/||u||_2. Every chord of K parallel to v has length at most rho_Q(v), because every difference of two points of K belongs to Q. Also rho_Q(v)=||u||_2/p_Q(u). Fiber integration yields

    |K| <= rho_Q(v) pi_K(v),
    pi_K(u)/|K| >= p_Q(u).

Cauchy's formula with centering thus gives

    E (u.X)_+ = pi_K(u)/(d|K|) >= p_Q(u)/d.

The dual-norm estimate |u.(x-w)|<=p_Q(u)N(x-w) shows that the assigned law has positive directional moment at least (1/d-h)p_Q(u). Its support function is at least this mean. Consequently

    (1/d-h) Q^polar subset T=conv(w_0,...,w_d).

For h<1/(2d), zero is interior to T, its polar P is an enclosing simplex, and

    K subset P subset 2dQ.

Every w_i lies on the boundary of K^polar, so h_K(w_i)=h_P(w_i)=1.

## 3. Weight correction without an absolute-coordinate loss

Let q_i be the vertex of P opposite the facet with normal w_i. Let lambda_i>0 be the barycentric coordinates of zero in T. The cone law of P is sum lambda_i delta_w_i; its centered probabilities are unique. Its anchor barycentric functions are

    alpha_i(x)=lambda_i(1-q_i.x).

Put p_i=P(I=i) and c=sum p_i w_i. Since E X=0, N(c)<=h. Therefore

    p_i-lambda_i=-lambda_i q_i.c,
    |q_i.c|<=2d h=r,
    p_i >= (1-r)lambda_i.

The last inequality is used multiplicatively, avoiding the maximum norm of an anchor.

For f_K(u)=E_nu |u.X| and f_P(u)=E_nuP |u.X|,

    (1-r) f_P(u)
      <= E |u.w_I|
      <= f_K(u)+h p_Q(u)
      <= (1+dh/2) f_K(u),

where f_K(u)>=2p_Q(u)/d from Section 2. Hence

    [pi_P(u)/|P|]/[pi_K(u)/|K|]
      <= (1+r/4)/(1-r).

All denominators are positive under the strict h gate.

## 4. Mixed volume and relative projection error

The containment P subset 2dQ gives h_P(y)<=2dN(y) for every y. Thus

    z=E_nu [h_P(X)-1]
      <= E h_P(X-w_I)
      <=2dh=r.

Nonnegativity follows from K subset P and h_K(X)=1. The cone-law mixed-volume identity identifies z=V(K[d-1],P)/|K|-1. Minkowski's first inequality gives

    |P|/|K| <= (1+z)^d <= (1+r)^d.

Combining with Section 3,

    pi_K(u)/pi_P(u) >= (1-r)/[(1+r)^d(1+r/4)].

For 0<=r<1, the three factors a=1-r, b=(1+r)^(-d), c=(1+r/4)^(-1) lie in [0,1]. The elementary inequality 1-abc <= (1-a)+(1-b)+(1-c), together with the derivative bound 1-(1+r)^(-d)<=dr and 1-(1+r/4)^(-1)<=r/4, yields

    1-pi_K(u)/pi_P(u)
      <= (d+5/4)r
      = 2d(d+5/4)h
      <=3d^2 h  (d>=3).

The deficit is nonnegative by inclusion. This is relative to pi_P, not absolute volume or normalized projection volume.

## 5. Boundary and zero cases

For H=3d^2 C and e<=1/H, h<=1/(3d^2)<1/(2d), so every strict gate is valid, including e=1/H. The right side H e is at most one. When e=0, h=0; the same steps imply P=K from equality of projections and inclusion, or from zero relative caps. The prescribed S and its centroid have not been replaced: the only initial change was translation by that same centroid, and every subsequent metric conclusion about S can be translated back.

## Imported inputs and scope

The only imported special inputs are the actual cone-law identity D/B=n e/(1+n e) and the first-moment weighted-anchor theorem proved in the frozen release. Classical Cauchy, mixed-volume and Minkowski identities are used exactly as in that release. The new estimates are the intrinsic diameter/dispersion, multiplicative weight correction, and relative conversion. No abstract law is asserted to be a convex-body example.
