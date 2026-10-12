# Independent referee report: sharp vertex-excess exponent

Date: 8 October 2026.

## Verdict and scope

**PASS for the traditional mathematical theorem and its sharpness claim.** For every integer d >= 3 and r >= 1, the proof establishes the exponent 1/min(r,d-1), uniformly over full-dimensional convex d-polytopes with at most d+1+r vertices and over **every prescribed maximum-volume inscribed simplex**, with that simplex's original centroid. The stated constant T_(d,r) H_d^(1/k), actual Entry005 defect, zero-defect endpoint, and exact lower-family limit all survive this review.

No core mathematical gap was found. In particular, Section 5 is a valid finite-facet specialization of the old argument, rather than an invalid assertion that the old compact-limit theorem already knows facet incidence. The proof does not need the unproved all-minor/forest conjectures or a classification of two-extra-vertex polytopes.

This is an independent analytic and source-interface review of the new result. It is **not** a compilation, fresh kernel replay, or Lean formalization of the new theorem. The already audited old source theorems remain retained inputs. I inspected their relevant statements and proof interfaces and independently reconstructed the finite-law geometric chain. No manuscript or old formal source was edited, no large dependency was compiled, and nothing was published. The author's auxiliary numerical/exact scripts were not used as a substitute for proof.

### Frozen reviewed files

- Main: `research_math/vertex_excess_sharp_exponent_20261008/SHARP_VERTEX_EXCESS_EXPONENT.md`, 350 lines. SHA-256: `8da4c012d4099465b4702ce4091ba4d1e2cc7862c12e8eb55cbd7467414e0f05`.
- Separate geometric-sharpness addendum: `research_math/vertex_excess_sharp_exponent_20261008/SHARPNESS_BOUNDARY_ADDENDUM.md`. SHA-256: `3e6246f7557b3a927fb5a556efc962d8b7d55746070597d3453d56446f6d42ac`.

The main verdict is already valid for the frozen main theorem: its actual-defect sharpness is proved by Section 7 independently of the added geometric-sharpness claim. The addendum correctly completes the latter claim as well.

## 1. Cone lemma: section formula, dimensions, integral, and sharpness

The radial enlargement is in the correct direction. For rho <= s_j <= 1 and rho < 1,

    s_j z_j = theta_j rho z_j + (1-theta_j) z_j,
    theta_j = (1-s_j)/(1-rho) in [0,1].

Consequently L is contained in conv(B,rho Z), where Z=conv(z_1,...,z_m). Every convex combination of its two convex layers can be grouped into one point in each layer. Solving the height equation gives exactly

    a=(s-rho)/(1-rho), b=rho(1-s)/(1-rho),
    section at ell=s: a B + b Z.

There is no hidden translation/scaling error in using mixed volumes here: choose b_0 in the base plane and identify the ell=s plane by subtracting s b_0. Since a+b=s, the identified section is a(B-b_0)+b(Z-b_0). The same q-dimensional Euclidean measure is used throughout.

With q=N-1 and h=dim Z <= m-1, monotonicity yields

    0 <= V(B[q-j],Z[j]) <= |B|_q.

For j>h those terms vanish. One direct justification is to translate Z into an h-dimensional linear subspace and bound B+tZ inside a product box with h side lengths O(1+t) and all remaining side lengths O(1). Its q-volume is O(t^h); nonnegative polynomial coefficients then force every higher coefficient to be zero. This also covers h=0. Alternatively the essential-collection criterion gives the same conclusion.

The substitution s=rho+(1-rho)u gives

    binom(q,j) integral_rho^1 a^(q-j)b^j ds
      = (1-rho)rho^j binom(q,j) integral_0^1 u^(q-j)(1-u)^j du
      = (1-rho)rho^j/(q+1).

The ell-height Jacobian is 1/||ell||. The volume of C is |B|_q/[N||ell||], so division cancels both that Jacobian and the factor q+1=N. Thus

    |L|/|C| <= 1-rho^(h+1) <= 1-rho^min(m,N).

Both inequality directions are correct because 0<rho<1 and h+1 <= min(m,N). The cases rho=0 and N=1 are harmless and should be treated as the manuscript does, before any problematic limiting convention.

The sharp cone example is correct up to the immaterial boundary convention in the words “omitted region”: the complement of the hull has the **volume** of the closed simplex with intercepts rho on the first m axes and one on the rest. Its relative volume is rho^m. When m>N, saturation at N can also be realized by including all N base vertices among the apex rays and adding redundant points.

Minor editorial recommendation only: explicitly say N,m are positive integers in the lemma statement. The application always has m>=1; no empty-apex case is used.

## 2. Projection collapse and actual-facet counting

For rho>0, every off-base vertex q_i has s_i=ell(q_i)>0, and z_i=q_i/s_i belongs to B. The representation is unique. Full dimensionality gives rho<1 and at least one off-base vertex.

If z_1 differs from z_2, orthogonal projection along z_1-z_2 is valid because ell(z_1-z_2)=0. The height functional therefore descends to the quotient/projection space. Write the common projected base point as z'. If s_1<=s_2, then s_2 z' belongs to the segment [s_1 z',z']; discarding the farther projected point is legitimate. This removes one point from j<=r+1 off-base vertices, giving at most r. If the two z_i are equal, the same redundancy already exists before projecting. If j=1, the one remaining point still obeys m=1<=r.

Projection of the full-dimensional simplex has dimension d-1, and its base has dimension d-2: a nonzero tangent direction has been removed from the base plane, while ell survives. Thus applying the cone lemma with N=d-1 has no hidden degeneracy. The exponent comparison rho^min(m,d-1) >= rho^min(r,d-1) is again in the correct direction.

For Section 4, a facet of a full-dimensional d-polytope contains at least d of its vertices. If an enclosing simplex facet plane is that actual K-facet plane, at most (d+1+r)-d=r+1 K-vertices lie outside it. The hypothesis therefore gives exactly the count required by the projection lemma. Combining its lower projection deficit with the assumed upper deficit delta gives the stated near-vertex coordinate bound with exponent 1/k.

This counting would indeed be invalid for a general supporting contact plane. The manuscript recognizes and resolves that distinction rather than conflating a support point with a facet.

## 3. Finite actual cone law and the generic assignment theorem

Normalize the prescribed S, preserving its own centroid, so 0 is its centroid and the unit ball lies in S. Maximum-volume replacement gives |alpha_i^S(x)|<=1 for x in K. Hence -K is contained in dS and therefore in dK. In particular, for each actual cone-law atom X_F with h_K(X_F)=1,

    N(X_F)=h_K(X_F)+h_K(-X_F) <= d+1=n.

The irredundant facet data satisfy s_F>0, h_F>=1, and distinct unit normals. Facet-cone volume gives sum s_F h_F=d|K|, so the displayed p_F are positive and sum to one. Surface-area balance gives mean zero. Unit-ball support and the support-height identity follow directly. Cauchy's formula and mean zero give the displayed positive-part brightness identity with the exact factor d|K|.

The support of this finite law is exactly its actual atoms. The horizontal moment A is positive because boundedness of K forces its normals to span the ambient space. The lifted moment B is positive as well: positive weights and mean zero put zero in the interior of the atoms' convex hull, whose affine span is full dimensional. There is an affinely independent (d+1)-tuple with positive sampling probability. Thus all positivity and integrability hypotheses of the generic theorem are discharged by actual geometry.

I inspected the exact retained interfaces in:

- `PyramidEntryDefect.lean`: `Entry005.finite_halfspace_entryA_lifted_moment`;
- `PyramidMomentDefect.lean`: `Entry005.finite_halfspace_defect_over_first_moment`, plus positive horizontal/lifted moments;
- `SeminormFirstMoment.lean`: `Entry005.unit_ball_seminorm_first_moment_assignment`;
- `FiniteBodyWeightedAssignment.lean`: finite-body first-moment positivity and actual-support anchor output;
- `FiniteHalfspaceConeLaw.lean`: probability, centeredness, ball support, and brightness identities.

The first two use the actual finiteHalfspaceConeLaw of the actual halfspace polytope and exactly the original entryA/entryDefect. There is no surrogate invariant. The generic seminorm theorem assumes neither a compact approximation sequence nor an unidentified limiting law. Its cost is

    h <= R*n*(n+1)*(B-A)/B.

With R=n and (B-A)/B=ne/(1+ne), this is

    h <= n^3(n+1)e/(1+ne),

exactly (10). In particular no factor n has been dropped. Jensen's B>=A and A>0 also provide e>=0.

The manuscript's `PyramidEntryDefect.*`/`PyramidMomentDefect.*` wording is best read as module-qualified references: the actual Lean namespace is `Entry005`. This is only a citation-style detail.

## 4. Independent reconstruction of the finite-law enclosure chain

Here is a complete check that the old compact-limit implementation is not being assumed to provide the new conclusion.

Let m_K(z)=E<z,X>_+ and f_K(z)=E|<z,X>|=2m_K(z). The elementary sheared-cylinder volume argument gives

    |<z,y>| <= d*m_K(z)*N(y).

Let p_i be the assignment masses. Positive-part Lipschitz continuity yields

    sum_i p_i <z,w_i>_+ >= (1-dh)m_K(z).

For h<1/(2d), the right side has a positive uniform lower bound on the unit sphere, since K contains the unit ball. Thus the convex hull of the affinely independent anchors contains zero in its interior. Its polar intersection P is a genuine d-simplex. Since every w_i is an actual X_F, K lies in P and every P inequality is an actual K facet inequality. Each corresponding K facet lies in the P facet, giving the required full facet incidence.

For z in P, the left side of the preceding inequality is at most one, hence m_K(z)<=2. The same width estimate gives

    P contained in 2d(K-K).

Let lambda_i>0 be the barycentric coordinates of zero in the anchor simplex, and q_i the polar vertex opposite w_i. The affine identity

    alpha_i^w(x)=lambda_i(1-<q_i,x>)

holds by its values on all anchors. The actual cone probabilities of P have the same mass and mean equations as lambda, hence agree with lambda. If c=sum p_i w_i, then

    |<q_i,c>| <= 2dh,
    p_i=lambda_i(1-<q_i,c>) >= (1-2dh)lambda_i.

Meanwhile the width estimate and absolute-value Lipschitz continuity give

    sum p_i |<z,w_i>| <= (1+dh/2) f_K(z).

Put a=2dh<1, using a different letter from vertex allowance r. Exact actual brightness identities therefore imply

    (1-a) pi_P(u)/|P| <= (1+a/4) pi_K(u)/|K|.

For the scale inequality, the finite first mixed-volume formula gives directly

    integral h_P(X) dmu = [sum_F s_F h_P(n_F)]/(d|K|)
                       = V(K[d-1],P)/|K|.

Minkowski's first inequality bounds this below by (|P|/|K|)^(1/d). Subadditivity, h_P(w_i)=1, and P contained in 2d(K-K) bound it above by 1+2dh=1+a. Combining gives

    pi_K(u)/pi_P(u) >= (1-a)/[(1+a)^d(1+a/4)].

For 0<=a<1, the missing fraction is at most

    a + d*a + a/4 = 2d(d+5/4)h <= 3d^2 h  (d>=3).

Thus the complete finite-law chain yields precisely the required projection bound, without invoking any subsequence or compact-limit identification. With C=n^3(n+1) and H=3d^2C, e<=1/H gives h<=1/(3d^2)<1/(2d), including equality at the defect threshold. Finally 3d^2 h<=He. This verifies both H and every strict gate.

## 5. Retention and the quantifier over all prescribed maxima

I reviewed `BOUNDED_VERTEX_EXCESS_RETENTION.md` and the old unrestricted retention argument/source. The hypotheses needed are exactly K contained in P and one actual K-point with each P-coordinate at least 1-rho. They make no extra demand on P or on the new cap exponent.

For the bounded-vertex proof, near maximizers may be chosen to be actual vertices. They are distinct when rho is in its local range. A maximum vertex simplex omits at most r of the comparison vertices. The restriction to that omitted block, determinant telescoping, and substochastic determinant matching give disjoint caps of loss eta=8r rho<=1/8. Equality in independently sampled determinant expansion then forces each vertex of **any prescribed maximum S**, even a nonvertex one, to be supported in one distinct cap. No claim that all maxima are vertex simplices is needed.

The inverse bootstrap is sound. With W the coordinates of this same S, B=W^(-1), beta=max|B-I|, and W_jj>=1-eta, one obtains beta<=eta/(1-2eta)<=1/6. The actual maximum-volume replacement bounds for the comparison points then improve every column loss to at most 4rho. Reapplying the inverse estimate yields B_ij>=-8rho. The exact original-centroid dilation threshold is -E/n. Therefore E<=8n rho locally. The universal replacement bound E<=n handles rho>1/(64r), yielding the stated all-scale 64nr rho.

The independent unrestricted argument yields 16n^2 rho for the same prescribed S. Taking the minimum is valid because both estimates concern the same K,S,rho. It does not optimize over different maxima or different centers.

At e=0, the cap coordinate loss is zero and retention gives E=0 without dividing by e or rho. At e=1/H every strict enclosure condition is still strict. Above the threshold, E<=n and T_(d,r)>=n give the claimed global estimate. Affine transport preserves the selected original S and its centroid, and there is no change of quantifier on undoing normalization.

## 6. Actual lower family, including the two-dimensional core

The core dimension m=k+1 is at least 2 and at most d. The stated truncation has exactly 2m vertices. Every nondegenerate vertex simplex uses all m rays, one doubled; its determinant magnitude is (1-t)t^j for some j>=0. Therefore T_t using all top vertices and t e_1 is maximum among vertex tuples. Multiaffinity and the triangle inequality extend this upper bound to arbitrary inscribed tuples, so its maximality is genuine.

The barycentric coordinates are

    beta_0=(1-sum x_i)/(1-t),
    beta_1=x_1-t beta_0, beta_i=x_i (i>=2).

On C_t, beta_0 lies in [0,1], every coordinate is >=-t, and at t e_2 one equals -t. This gives E(C_t,T_t)=(m+1)t about the actual centroid.

The retained raw facet calculation gives the exact displayed e_m(C_t). It can also be checked directly with c=1/(m-1)!, q=t^(m-1), and b=1-q:

    H_core = c^m b^(m-1)[m+1+(m-1)q],
    L_core = c^(m+1)b^(m-1)[1+(m-1)q-(m-1)t^m-q t^m],
    |C_t|=(1-t^m)/m!, a=L_core/(m|C_t|H_core).

Subtracting 1/(m+1) gives the manuscript's formula. Its numerator bracket is

    (m+1)(m-2)(1-t)+2(1-t^m)>0,

valid for every m>=2. This explicitly resolves a small scope concern: some retained sharpness statements were written for d>=3, but their facet/determinant computation works at m=2 as well. At m=2 the formula simplifies to

    e_2(C_t)=2t/[3(3+t)], delta=2t/(1+t).

Thus the r=1 layer is covered rather than silently assumed from a d>=3 statement.

For completeness, the actual pyramid identity may be independently derived from raw facets. If a p-body has facet area-normal/support pairs (u_i,b_i), volume V, horizontal sum H, and lifted sum L, its unit-height pyramid has side pairs ((u_i,b_i)/p,b_i/p) and bottom pair ((0,-V),0). Consequently

    H_pyr=p^(-(p+1))L+V*p^(-p)H,
    L_pyr=V*p^(-(p+1))L, |pyr K|=V/(p+1).

Using a=L/(pVH) gives a(pyr K)=a/(1+a). Hence delta=dimension+1-1/a is exactly pyramid invariant; this calculation uses the actual facets, not a probabilistic surrogate.

Every full-dimensional vertex simplex of an iterated pyramid includes every new apex, so the pyramid of T_t remains maximum. Multiaffinity again handles arbitrary inscribed vertices. At each pyramid step, old barycentric coordinates are multiplied by a number in [0,1], the new apex coordinate is nonnegative, and the base still realizes -t. Therefore E(K_t,S_t)=nt exactly.

The vertex count is 2m+(d-m)=d+1+k<=d+1+r. Since

    e_m/t^k -> k(k+1)/(k+2)^2,
    delta/t^k -> k(k+1),
    e_d=delta/[n(n-delta)],

we get e_d/t^k -> k(k+1)/n^2 and the exact ratio in (2). For beta>1/k, the exponent 1-k beta is negative, so E/e_d^beta diverges. This defeats every finite constant depending on d,r. The specified family is within the literal at-most-vertex class for every r, including r>=d-1.

## 7. Geometric-sharpness addendum

The addendum's actual area-normal vectors are correct. For i<=m=r+1 the removed coordinate-facet simplex has scale product rho^(m-1); for i>m it has product rho^m. The new cut facet has the stated area-normal vector by the usual intercept determinant calculation. The top facet is unchanged, and the vectors balance exactly.

Cauchy's formula therefore yields exactly

    loss(u)=rho^(m-1)
      [A_abs+rho B_abs-|A+rho B|]/[A_abs+B_abs+|A+B|].

The denominator is positive for every nonzero u. The numerator is nonnegative by the triangle inequality and at most the denominator. Hence the loss is at most rho^r for **every** direction. With u=e_1-e_2 it equals rho^r. This proves the maximum-over-directions assertion, including the subset of directions parallel to the opposite facet, and resolves the logical distinction between one equality direction and sharpness of an existential-direction inequality.

All stated K-facet incidences and the d+1+r vertex count hold for 0<rho<1. The body is exactly an iterated pyramid over the m-dimensional equal truncation. If writing pi_P(u) for nonunit u, the text should clarify either normalized-direction evaluation or homogeneous brightness; the ratio is identical under both conventions.

## 8. Standard references and one normalization warning

I opened the primary Bihan–Soprunov v2 text and PDF. Its introduction supplies monotonicity and the standard translation/multilinearity properties, and Theorem 2.2 supplies the essential-collection criterion needed for vanishing. The use of these classical facts is appropriate. No strict-monotonicity result from that paper is needed. [Bihan–Soprunov, arXiv:1702.07676v2](https://arxiv.org/html/1702.07676v2).

There is a **source-side normalization typo** worth recording before publication: Theorem 2.1 in that v2 text/PDF writes the coefficient of lambda_1...lambda_q as V(K_1,...,K_q). With its own convention V(K,...,K)=Vol(K), the coefficient must be q!V. The draft's binomial expansion is correctly normalized and does **not** inherit this typo. Its derivation can be tied to the introduction's multilinearity and diagonal normalization instead. This observation changes no theorem or constant in the reviewed manuscript. [Primary PDF, p. 3](https://arxiv.org/pdf/1702.07676v2).

This review did not perform an exhaustive novelty search. It makes no first-discovery claim. Standard mixed-volume, cone-volume, and projection-body literature must remain distinguished from the new complexity-indexed synthesis.

## 9. Final disposition

The main exponent classification, its actual-defect constant, its prescribed-maximum quantifier, and its explicit sharpness family are mathematically established by the reviewed traditional proof together with its identified retained inputs. The separate geometric-sharpness addendum is also correct.

Recommended next-stage edits are expository: state positive integer dimensions/counts in the cone lemma; clarify nonunit brightness notation; make the m=2 core computation explicit; use actual Lean namespaces in code references; and retain the source normalization warning. None is a blocking mathematical revision. For a standalone public paper, expanding the finite-law chain as in Section 4 of this report and recording the exact retained theorem statements would make the dependency boundary easier to audit.

New Lean work would still be needed for the cone/prismoid mixed-volume lemma, the projection collapse/counting step, the finite actual-facet specialization, and the final assembly with the new exponent. The old Main's successful compilation is not a certificate of those new statements.
