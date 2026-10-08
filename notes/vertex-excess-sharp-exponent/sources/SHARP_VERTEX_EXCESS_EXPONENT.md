# Vertex excess determines the sharp simplex-stability exponent

8 October 2026. Complete traditional proof with explicitly identified standard
mixed-volume input and a finite-facet specialization of the retained actual
Entry005 chain. No independent audit or Lean formalization of this new theorem
is asserted. The earlier compact-limit Main does not by itself supply the
facet-incidence hypothesis used below.

## 1. Main theorem

Let d>=3 and r>=1 be integers. Put

    n=d+1,
    k=min(r,d-1),
    H_d=3d^2(d+1)^3(d+2),
    T_(d,r)=min{64(d+1)r,16(d+1)^2}.

Let K be a full-dimensional convex d-polytope with at most d+1+r vertices,
and let S be **any prescribed maximum-volume inscribed simplex**. With the
original centroid of this same S, and with the original actual Entry005
defect e(K),

    E(K,S) <= T_(d,r) H_d^(1/k) e(K)^(1/k).                         (1)

The exponent 1/k is optimal in this class: no exponent beta>1/k can hold
uniformly near zero defect, even with an arbitrary constant depending on
d and r. A specified actual family satisfies

    lim E(K_t,S_t)/e(K_t)^(1/k)
        = (d+1)[(d+1)^2/(k(k+1))]^(1/k).                          (2)

Thus the sharp exponent is

    1/min(r,d-1).

In particular, one extra vertex gives exponent one, two extra vertices give
exponent one-half in every d>=3, and the unrestricted exponent 1/(d-1)
appears once the vertex allowance reaches 2d. Formula (1) does not optimize
the dimension coefficient. The separate all-circuit theorem gives a much
better exact local coefficient when r=1.

The new geometric ingredient is an apex-count projection estimate. The
factor T_(d,r) is inherited from the already proved few-vertex retention
theorem and unrestricted retention theorem, respectively.

## 2. A cone-volume lemma with finitely many inner apex points

Let C=conv(0,B) be a full-dimensional N-dimensional cone, where B is a compact
convex (N-1)-body in an affine hyperplane ell=1 and ell is linear. Suppose
z_1,...,z_m belong to B, and rho<=s_j<=1 with 0<=rho<1. Put

    L=conv(B,s_1 z_1,...,s_m z_m).

Then

    |L|/|C| <= 1-rho^min(m,N).                                    (3)

In particular it is at most 1-rho^m if m<=N.

### Proof

The case rho=0 is immediate. Move each s_j z_j radially toward zero to
rho z_j. This enlarges the hull, because s_j z_j lies on the segment from
rho z_j to z_j in B. Let Z=conv(z_1,...,z_m), of dimension h<=m-1.
It is enough to bound conv(B,rho Z).

Set q=N-1. Its section at ell=s, rho<=s<=1, is

    [(s-rho)/(1-rho)] B + [rho(1-s)/(1-rho)] Z.                     (4)

Translation identifies these sections with q-dimensional Minkowski sums.
Use the standard mixed-volume polynomial and its monotonicity:

    |aB+bZ|_q
      =sum_{j=0}^q binom(q,j) a^(q-j)b^j V(B[q-j],Z[j]),
    0<=V(B[q-j],Z[j])<=|B|_q   because Z is contained in B.

Terms with j>h vanish because dim Z=h. One can see this last statement
directly from the polynomial: after choosing coordinates with Z in an
h-dimensional affine subspace, |B+tZ|=O(t^h), while the mixed-volume
coefficients are nonnegative.

For a=(s-rho)/(1-rho), b=rho(1-s)/(1-rho), the beta integral gives

    binom(q,j) integral_rho^1 a^(q-j)b^j ds
       = (1-rho)rho^j/(q+1).

The Jacobian converting ds to normal height cancels against
|C|=height(B)|B|_q/N. Therefore

    |L|/|C| <= (1-rho)sum_{j=0}^min(h,q)rho^j
             =1-rho^(min(h,q)+1)
             <=1-rho^min(m,N).

This includes N=1: q=0 and the calculation is simply the length ratio
of intervals. All bodies in the intended application are polytopes.
Only the ordinary Minkowski volume polynomial, nonnegativity, and
monotonicity of mixed volumes are used; no Alexandrov--Fenchel stability
estimate or unproved inverse-Minkowski assertion is an input. QED.

The power and constant in (3) are sharp. In the standard N-simplex
conv(0,e_1,...,e_N), take the m inner points rho e_1,...,rho e_m, m<=N,
and the full opposite base conv(e_1,...,e_N). Its omitted region is the
simplex conv(0,rho e_1,...,rho e_m,e_(m+1),...,e_N), of relative volume
exactly rho^m.

## 3. Apex count improves a hyperplane-projection cap

Let P be a full-dimensional d-simplex, d>=2, and let K be a full-dimensional
polytope contained in P. Fix a vertex v of P with opposite facet B, and let
lambda_v be its P-barycentric coordinate. Define

    rho=1-max_{x in K}lambda_v(x).

Suppose at most r+1 vertices of K lie outside B, where r>=1. Then some
unit direction u parallel to B satisfies

    [pi_P(u)-pi_K(u)]/pi_P(u) >= rho^min(r,d-1).                    (5)

### Proof

If rho=0 the assertion is trivial. Full dimension gives rho<1. Translate
v to zero and write ell=1-lambda_v, so ell is linear, ell(B)=1, and
P=conv(0,B). Enumerate K's vertices outside B as q_1,...,q_j. Full dimension
ensures j>=1, and by assumption j<=r+1. Each has the unique representation

    q_i=s_i z_i,  z_i in B,  rho<=s_i<1.

The other K vertices lie in B, so K is contained in conv(B,q_1,...,q_j).

If j>=2 and z_1!=z_2, project orthogonally in the direction z_1-z_2,
which is parallel to B. The projected z_1 and z_2 coincide. Of q_1 and
q_2 retain only the point with the smaller s_i: the other point lies on
the segment from that retained point to their common projected base point.
Thus, after projection, at most j-1<=r inner apex points suffice.

If j>=2 and z_1=z_2, first discard the farther of q_1 and q_2 and choose
any nonzero direction parallel to B. If j=1, choose any such direction
and retain its single apex point. In every case the projected K is
contained in a hull consisting of the entire projected base and at most
m<=r inner apex points, all still having depth at least rho.

The functional ell descends to this projection, so pi(P) is a genuine
(d-1)-dimensional cone with base of dimension d-2. Its volume is positive.
Apply (3) in N=d-1 dimensions. The relative missing volume is at least
rho^min(m,d-1), which is at least rho^min(r,d-1), proving (5). QED.

The only combinatorial hypothesis in (5) is the number of vertices outside
the particular opposite facet. Other facets of P need not be facets of K
for this single-vertex statement.

For 1<=r<=d-1 the power and constant in (5) are also attained by the
geometric family

    K=conv(e_1,...,e_d,rho e_1,...,rho e_(r+1)) inside
    P=conv(0,e_1,...,e_d).

Project along e_1-e_2. The first two rays coincide, and the projected body
is exactly the sharp cone example above with N=d-1 and m=r. It has relative
projection deficit rho^r in that direction. Each facet of P supports a
full facet of K. This observation gives exact sharp examples for the new
geometric step, while Section 7 separately verifies the original invariant.

## 4. Facet-supported outer simplices and vertex excess

Assume now that K has at most d+1+r vertices and is contained in a simplex
P whose every facet hyperplane is also the hyperplane of an actual facet
of K. Each such K facet is a (d-1)-polytope and has at least d vertices.
Consequently at most r+1 vertices of K lie outside each facet of P.

Suppose moreover that all actual hyperplane projections obey

    pi_P(u)-pi_K(u) <= delta pi_P(u)   for every unit u,              (6)

where 0<=delta<=1. Apply (5) separately at every P vertex. Since
k=min(r,d-1), this gives

    max_{x in K}lambda_i(x) >= 1-delta^(1/k)   for every i.          (7)

Thus the relative-projection-to-near-vertex exponent improves from
1/(d-1) to 1/k. This step is exact and independent of ambient conditioning.

The actual-facet condition is essential to the counting argument. Mere
support contact h_K(w_i)=1 does not imply that a supporting hyperplane
contains d vertices of K. Section 5 supplies this condition using a
specific finite facet law; it is not silently imported from a general
compact-limit law.

## 5. Finite-facet specialization of the actual Entry005 enclosure chain

Here we justify applying (7) to the enclosing simplex constructed by the
retained argument. This is a traditional finite-polytope specialization,
not a claim that the compiled compact-limit Main already proves the
stronger facet condition.

Normalize the **prescribed** maximum simplex S affinely as in the retained
quadratic proof, keeping its own centroid at zero and the unit ball inside
S. Affine invariance preserves e, E, vertex count, and the maximum-simplex
property. For the actual irredundant facets of K let n_F be distinct outward
unit normals, h_F=h_K(n_F)>0 their support numbers, and s_F their areas.
Use the finite probability law

    mu = sum_F p_F delta_(X_F),
    p_F=s_F h_F/(d|K|)>0,
    X_F=n_F/h_F.                                                  (8)

It has mean zero by sum_F s_F n_F=0, is supported in the unit ball because
h_F>=1, and satisfies h_K(X_F)=1. Its exact brightness identity is

    integral <z,X>_+ dmu(X)=|z| pi_K(z/|z|)/(d|K|).

The finite lifted/horizontal determinant identities give, with

    A=E|det(X_1,...,X_d)|,
    B=E|det((X_1,1),...,(X_(d+1),1))|,

    a(K)=B/((d+1)A),
    (B-A)/B=(d+1)e(K)/(1+(d+1)e(K)).                              (9)

These are the actual finite-facet identities already available in the
project. In the retained source tree their exact interfaces include
`PyramidEntryDefect.finite_halfspace_entryA_lifted_moment` and
`PyramidMomentDefect.finite_halfspace_defect_over_first_moment`.
The unit, distinct-normal, positive-support, compactness assumptions are
all satisfied by the irredundant facet presentation used in (8).

Apply the general mean-zero, unit-ball seminorm assignment theorem directly
to this finite law. With N=h_(K-K), it gives d+1 affinely independent
anchors w_i in the support of (8), and the same intrinsic assignment bound

    h:=integral N(X-w_(I(X))) dmu
       <= (d+1)^3(d+2) e(K)/(1+(d+1)e(K)).                         (10)

The relevant generic source is the seminorm first-moment assignment theorem;
`FiniteBodyWeightedAssignment.finite_body_cone_first_moment_assignment`
also explicitly demonstrates the finite-law support conclusion. No
compact-limit identification is required here.

Every chosen w_i is literally one of the X_F. Therefore

    P={x:<w_i,x><=1 for every i}

is an intersection of d+1 **actual K facet halfspaces**. Under the same
gate h<1/(2d), the retained support/brightness proof makes P a genuine
enclosing simplex. Its facets contain the corresponding full K facets,
giving precisely the extra hypothesis in Section 4.

All subsequent estimates of the retained enclosure chain are valid for
the same finite law: the seminorm width estimate, multiplicative correction
of its anchor probabilities, and brightness comparison are finite sums.
The volume-root inequality can be obtained directly here from Minkowski's
first inequality and the finite first mixed-volume formula:

    (|P|/|K|)^(1/d) <= integral h_P(X) dmu(X).

Thus there is no new limiting-law or subsequence passage. The original
calculation yields, for 0<=e(K)<=H_d^(-1),

    pi_P(u)-pi_K(u) <= H_d e(K) pi_P(u)   for every unit u.          (11)

The endpoints and strict enclosure gate are the same as before: (10) gives
h<=1/(3d^2)<1/(2d) even at e=H_d^(-1). This completes the finite-facet
bridge needed for (7). No newly compiled Lean bridge is claimed.

## 6. Retention of the original maximum and all defect scales

For 0<=e<=H_d^(-1), set delta=H_d e and rho=delta^(1/k). Equations (7) and
(11) give the required near-vertex points in K.

The already proved all-scale retention bounds for the same prescribed S
are

    E(K,S)<=64(d+1)r rho   when K has at most d+1+r vertices,
    E(K,S)<=16(d+1)^2 rho  without a vertex-count restriction.

Taking their minimum proves (1) in this defect range. They retain the
centroid and carrier of the original prescribed S, including arbitrary
nonvertex maxima; only harmless vertex relabeling is used internally.

For e>H_d^(-1), the universal maximum-simplex bound E<=d+1 suffices, since
(H_d e)^(1/k)>1 and T_(d,r)>=d+1. At e=0, (7) has rho=0 and the same
retention theorem yields E=0 without division by e or rho. Undoing the
normalization proves (1) for the original K, S, and centroid.

## 7. Exact lower family and sharpness

Put m=k+1 and start with the m-dimensional equal-intercept truncated simplex

    C_t={x_i>=0, t<=sum_i x_i<=1},  0<t<1.

It has 2m vertices. The retained exact actual-defect formula is

    e_m(C_t)
      =t^(m-1)[m(m-1)-(m+1)(m-2)t-2t^m]
        /[(m+1)(1-t^m)(m+1+(m-1)t^(m-1))].

Its simplex T_t=conv(e_1,...,e_m,t e_1) is maximum, and
E(C_t,T_t)=(m+1)t. Set

    K_t=pyr^(d-m) C_t,   S_t=pyr^(d-m) T_t.

It has 2m+(d-m)=d+1+k<=d+1+r vertices. Every full-dimensional vertex
simplex must contain every new pyramid apex, so S_t stays maximum; the
separately affine determinant argument also covers arbitrary inscribed
vertices. Its worst barycentric coordinate stays -t, giving E(K_t,S_t)=nt.

The pyramid-invariant quantity delta=dimension+1-1/a satisfies

    delta~m(m-1)t^(m-1)=k(k+1)t^k.

In ambient dimension d,

    e_d(K_t)=delta/[n(n-delta)]~k(k+1)t^k/n^2.

This proves (2). For every beta>1/k, E/e^beta diverges as t decreases to
zero, proving optimality of the exponent. These are actual polytopes and
actual prescribed maxima; no arbitrary probability law is substituted.

## 8. Dependencies and status

New geometric results: the cone apex-count bound (3), the projection collapse
argument (5), and their use of vertex excess through actual facet incidence.
The finite-law specialization explicitly strengthens the output of the old
enclosure argument while keeping its original defect and constant H_d.

Standard input: the Minkowski volume polynomial, nonnegative monotone mixed
volumes, and Minkowski's first inequality. The latter was already used in the
retained traditional chain. A later formalization must implement or connect
the apex-count prismoid polynomial; it is not present merely because the old
compact-limit theorem compiled.

Retained project inputs: the actual finite-facet defect/brightness identities,
the general seminorm assignment and intrinsic enclosure estimates, the
64nr and 16n^2 retention bounds, and the audited equal-intercept truncation
plus pyramid formulas. No stronger all-minor stochastic-matrix conjecture,
no forest-gap conjecture, and no unproved two-vertex-excess classification
is used in this proof.

The exponent classification is a written theorem pending independent review.
No first-discovery claim has been made; a focused comparison with prior
polytope stability and prismoid/mixed-volume results remains necessary.

Primary reference for the standard mixed-volume facts used in Section 2:
F. Bihan and I. Soprunov, *Criteria for strict monotonicity of the mixed
volume of convex polytopes*, arXiv:1702.07676v2 (2017), Introduction and
Section 2, especially the essential-collection criterion in Theorem 2.2.
Their strict-monotonicity theorem is not needed here. The ordinary
polynomial and monotonicity properties are classical; they are not claimed
as new ingredients of this investigation.
https://arxiv.org/abs/1702.07676
