# Independent analytic model audit: quadratic dimension growth

Date: 7 October 2026.

## Verdict

**PASS for the stated upper theorem, using the expressly identified frozen cone-law identity and the classical convex-geometric identities.**

For every integer d >= 3, every full-dimensional compact convex body K in R^d, and every prescribed maximum-volume inscribed simplex S, the submitted argument establishes

    E(K,S) <= 16(d+1)^2 [3d^2(d+1)^3(d+2)]^(1/(d-1)) e(K)^(1/(d-1))
           <= 4096 d^2 e(K)^(1/(d-1)).

The centroid is that of the originally prescribed S. No replacement maximum simplex is introduced. No fatal error, counterexample, missing smallness condition, or lost dimension-dependent factor was found. The local geometric estimate and the endpoint e = 0 also pass.

This is an independent analytic **model-written audit**, accompanied by independently written finite exact-arithmetic checks. It is not a Lean proof, other proof-assistant verification, human peer review, a publication, a claim of priority, a novelty certification, or a determination of the optimal dimension order. This public-clean derivative preserves the mathematical content and analytic findings of the original audit.

The qualification about imported inputs is the ordinary dependency boundary of the theorem, not an unresolved analytical gap: the cone-law representation is an explicitly identified prior theorem, and its normalization and applicability were checked here. This audit does not purport to re-prove every theorem in the prior manuscripts.

## 1. Exact scope and reproducibility

The three original proof files audited are listed below by their public release paths. Every SHA-256 value in this section identifies the audited-original bytes, not the public-clean derivative bytes:

1. QUADRATIC_DIMENSION_THEOREM.md, audited-original SHA-256 8b66a2eddd69e8135584712f3a30e7565b2f391007bbfb69af456e29c1d30743.
2. INTRINSIC_NORM_CONVERSION.md, audited-original SHA-256 c2f5b579b1241ce5e06b98573eb3e9b69f328b2e2ad6e455c18a61115ac52a05.
3. intrinsic_caps/INTRINSIC_GEOMETRIC_BRIDGE.md, audited-original SHA-256 7e5a89b6761559cb980670719db10c10d075e1d5918bf6d49c5fb397287385e9.

AUDITED_ORIGINAL_SOURCE_HASHES.json records the public release paths, audited-original byte counts and SHA-256 hashes, and public derivative SHA-256 hashes. It includes the three proof files, imports/POLYNOMIAL_REFINEMENT.md, imports/weighted_anchors.md, sources/HISTORICAL_SOURCE_PINS.json, the four pinned manuscripts in sources/, and imports/SQUARE_PYRAMID_LOWER_BOUND.md. The original audit verified that every historical source byte count and hash matched the original source-pin manifest, reproduced as sources/HISTORICAL_SOURCE_PINS.json, and that the audited-original bytes were unchanged by the independent checker. Public derivative hashes are identified separately and are not the audited-original hashes.

The analytic verdict does not rely on numerical checks as evidence for unrestricted claims. The supplemental check_independent_quadratic_audit.py was independently written and uses exact rational arithmetic. Its output is verification/independent_exact_checks.json.

Notation below: n = d+1, m = d-1, C = n^3(n+1), H = 3d^2 C. The support function of the body L is h_L; its gauge is p_L. The polar is L^circ. The projection function is extended homogeneously to nonzero vectors by pi_L(u) = ||u|| |L projected onto u-perp|.

## 2. Prescribed-simplex origin, asymmetry, and intrinsic polarity

### 2.1 The maximum simplex is available and is nondegenerate

Compactness of K^(d+1) gives a maximizer of the absolute lifted determinant. Since K has interior, the maximum is positive. Thus its centroid lies in the interior of S and hence in the interior of K. Translating by the centroid of the prescribed S is legitimate. No other centering assumption, such as the centroid of K being zero, is used.

For each x in K, replacing vertex i of S by x multiplies its volume by |alpha_i(x)|. The replacement is an inscribed simplex, possibly degenerate, so maximality gives |alpha_i(x)| <= 1 for all i. After the stated translation,

    alpha_i(-x/d) = (1-alpha_i(x))/d.

These coordinates are nonnegative and sum to (n-1)/d = 1. Consequently -K is contained in dS, and therefore in dK. This is valid for every original maximum S, including nonunique maxima.

The same coordinate inequality also gives the universal bound E(K,S) <= n: centroid dilation by 1+t is exactly the region alpha_i >= -t/n. In fact E(K,S) equals n times the largest negative barycentric-coordinate magnitude over K, with zero used if no coordinate is negative.

### 2.2 Correct norm and dual norm

Q = K-K is compact, origin-symmetric, and has interior. Thus N(y) = h_Q(y) is a genuine norm. Its closed unit ball is Q^circ, not Q. Its dual norm is

    N_*(u) = h_(Q^circ)(u) = p_Q(u).

This gives |u dot y| <= p_Q(u) N(y), and support-function comparison with Q^circ indeed uses h_(Q^circ) = p_Q. In the later estimate q_i in 2dQ, the equivalent bound is |q_i dot c| <= 2d h_Q(c). These identifications have the correct orientation; no primal/dual switch is hidden in the proof.

Since h_K(x)=1 at any selected cone-law support point x, asymmetry implies

    N(x) = h_K(x)+h_K(-x) <= 1+d = n.

The support diameter in this norm is therefore at most 2n. Neither N(x) nor this diameter uses a Euclidean outer radius. N may depend on K, which is allowed: the weighted-anchor theorem applies to any fixed norm for each given law.

## 3. Actual cone law, centering, first moments, and support anchors

### 3.1 The law exists at the chosen origin

At the interior origin fixed above, define nu as the pushforward of

    h_K(theta) dS_K(theta)/(d|K|)

under theta -> theta/h_K(theta). Its mass is one by integral h_K dS_K = d|K|, and its expectation is zero by integral theta dS_K = 0. As h_K is strictly positive on the unit sphere, the radial map is continuous and its image is compact. Every image point satisfies h_K(x)=1. Since that equality defines a closed set, it also holds at every point of the topological support, not just almost surely.

Cauchy's projection identity shows that E|u dot X| > 0 for every nonzero u. The support consequently linearly spans R^d. A proper affine hyperplane containing the support would, after taking its expectation, contain zero and be a proper linear hyperplane. Thus the support also affinely spans R^d. This supplies every hypothesis of the weighted-anchor theorem, without a smoothness or finite-facet assumption.

### 3.2 Imported invariant normalization checked

For iid samples of this law use the first absolute moments

    A = E|det(X_1,...,X_d)|,
    B = E|det((X_0,1),...,(X_d,1))|,
    D = B-A.

The pinned sources/entry005-v3.md, Proposition 4.1, states a(K)=B/(nA). Its polytope expansion has the factors d!/(d|K|)^d and n!/(d|K|)^n, respectively, so their ratio divided by n is exactly the pinned facet expression L/(d|K| times H_facet). There is no simplex-volume d! inserted into the lifted random determinant and no second determinant moment substituted.

The source passage to arbitrary convex bodies uses a common interior ball, uniform support-function convergence, weak continuity of surface area measures, and a common compact support for the pushed-forward laws. Hence the identity applies at the centroid of the prescribed S, without the Euclidean normalization used elsewhere in the older proof. In particular,

    D = n A e,
    B = A(1+n e),
    D/B = n e/(1+n e).

The centered determinant cancellation identity gives D >= 0, and A>0, so e>=0 follows. The new proof does not use the old normalization-dependent bound A<=1. The denominator B is retained correctly.

The invariant is exactly the supplied projection-body/pyramid invariant. No polar-projection-body deficit, Rogers-Shephard deficit, or unrelated affine invariant is substituted. Translation invariance is enough for this proof and is part of the supplied invariant's definition/properties.

### 3.3 Selection, singular tuples, and measurability checked

The imported weighted-anchor proof in imports/weighted_anchors.md was checked beyond its final statement:

- Centering gives D = 2 E min(P,N_minus), including singular base tuples.
- Each two-test clipped witness has expectation at most D.
- There are n + choose(n,2) = n(n+1)/2 witnesses in H, each involving d+2 iid samples before conditioning.
- For V equal to the absolute lifted determinant, the tilted measure is V/B times the product law. It has total mass one and gives singular tuples mass zero.
- Its expectation of H/V is E[H 1_(V>0)]/B, which is at most E H/B. The indicator is necessary, and the frozen proof retains it.
- An integrable nonnegative ratio has a point in its probability-one domain no greater than its expectation. No compact minimizer on the open nonsingular set is assumed.
- Affine barycentric coordinates are continuous for each selected nonsingular tuple. Choosing the least index attaining the largest coefficient is Borel measurable.
- If some negative coordinate has magnitude at least one, its clipped witness pays for the full support diameter. Otherwise clipping is inactive and the affine decomposition bounds the distance. The positive-positive pair witnesses pay for all nonmaximal positive coordinates.

This proves the assignment bound in the norm N for atoms and nonatomic laws alike. Anchors are actual support points and affinely independent, not artificial points in an enclosing ball. Applying support diameter 2n gives

    h <= (2n)[n(n+1)/2][n e/(1+n e)]
      = n^3(n+1)e/(1+n e) = C e/(1+n e).

All n factors are present. At D=0 the selection has h=0; there is no division by e or discarded zero-defect case.

## 4. Directional chord dispersion and the enclosing polar simplex

Let u != 0, v=u/||u||, and let rho_Q(v) be the radial function of Q. Every chord endpoint difference parallel to v belongs to Q, so every such chord has length at most rho_Q(v). No claim that the support width equals this radial length is made or needed. Fiber integration gives

    |K| <= rho_Q(v) pi_K(v).

Homogeneity gives rho_Q(v)=||u||/p_Q(u). Multiplying the fiber inequality by ||u|| and dividing correctly yields

    pi_K(u)/|K| >= p_Q(u).

Cauchy's formula and centering then yield

    E(u dot X)_+ = pi_K(u)/(d|K|) >= p_Q(u)/d,
    E|u dot X| >= 2p_Q(u)/d.

The positive-part function is 1-Lipschitz on R. Applying the dual-norm bound to the coupling therefore shows that the assigned law has one-sided directional moment at least (1/d-h)p_Q(u). If this is positive, h_T(u), for T=conv(w_i), is at least that moment. The support-function criterion gives

    (1/d-h)Q^circ subset T subset K^circ.

At h<1/(2d), T contains (1/(2d))Q^circ. Taking polars reverses inclusions, giving

    K subset P=T^circ subset 2dQ.

There are exactly d+1 affinely independent anchors and zero is in the interior of their convex hull. Thus P is a bounded, full-dimensional simplex. Each anchor is a vertex of T and corresponds to an actual facet of P. Consequently h_P(w_i)=1, as required later. This is not merely an intersection of possibly redundant halfspaces.

## 5. Multiplicative weight correction

Let q_i be the vertex of P opposite the facet with normal w_i, and lambda_i>0 the barycentric coordinates of zero in T. The affine coordinate formula

    alpha_i(x) = lambda_i(1-q_i dot x)

is correct: it vanishes on the other d vertices w_j, equals lambda_i at zero, and equals one at w_i by the centered barycentric identity. The cone law of P has support exactly {w_i}, is centered, and has total mass one. Affine independence makes its centered probabilities unique, so they are precisely lambda_i.

For the assigned probabilities p_i and c=sum p_i w_i, centering and convexity of N give N(c)<=h. Since p_i=alpha_i(c),

    p_i-lambda_i = -lambda_i q_i dot c.

As q_i in 2dQ, |q_i dot c|<=2dh. With r=2dh<1 this gives p_i>=(1-r)lambda_i. This is a relative, anchorwise estimate and avoids multiplying a total-variation bound by a large coordinate radius.

For every nonzero u,

    (1-r)f_P(u) <= E|u dot w_I|
                    <= f_K(u)+h p_Q(u)
                    <= (1+dh/2)f_K(u).

Since dh/2=r/4, Cauchy's formula gives

    [pi_P(u)/|P|]/[pi_K(u)/|K|] <= (1+r/4)/(1-r).

All f_K and projection denominators are strictly positive, and 1-r>0 follows from the stated strict gate. This step is one-sided in precisely the direction needed for an upper bound on the missing fraction of P's projection.

## 6. Mixed volume, volume scale, and the relative deficit

P subset 2dQ gives h_P(y)<=2dN(y). Subadditivity and h_P(w_I)=1 give

    0 <= z := E[h_P(X)-1] <= E h_P(X-w_I) <= 2dh = r.

The nonnegative left side follows from K subset P and h_K(X)=1. Directly undoing the radial pushforward shows

    E h_P(X) = [1/(d|K|)] integral h_P(theta)dS_K(theta)
             = V(K[d-1],P)/|K|.

Thus z is the normalized first mixed-volume excess, with the factor d correct. Minkowski's first inequality gives

    V(K[d-1],P)^d >= |K|^(d-1)|P|,

and hence |P|/|K|<=(1+z)^d<=(1+r)^d. The inequality direction is correct: a bound on the mixed-volume excess supplies an upper volume ratio.

Combining this with Section 5 produces

    pi_K(u)/pi_P(u) >= (1-r)/[(1+r)^d(1+r/4)].

The denominator in the final deficit is pi_P(u), the unnormalized projection volume of the enclosing simplex. Neither pi_K(u), normalized projection volume, nor |P| is accidentally used as that denominator.

For 0<=r<1, all three factors 1-r, (1+r)^(-d), and (1+r/4)^(-1) lie in [0,1]. The union-product inequality and elementary derivative bounds give

    1-pi_K/pi_P <= r+dr+r/4 = (d+5/4)r
                 = 2d(d+5/4)h <= 3d^2h.

The last inequality requires d>=5/2, so d>=3 is sufficient. Inclusion makes the deficit nonnegative. This argument does not hide an exponential volume-ratio constant: the estimate is linearized before it enters the relative deficit.

## 7. Exact projection cap and affine issues

Let K subset P, with P a simplex, and let delta be the supremum of relative projection deficits. Because both projected bodies have interior in their projection spaces, denominators are positive. Inclusion gives 0<=delta<=1 (in fact delta<1 for full-dimensional compact K). The proof does not need the stronger strict inequality.

For a vertex p_i of P, set t=1-max_K lambda_i. Compactness attains this maximum. Nonnegativity of P-barycentric coordinates gives t in [0,1]. Choose any nonzero direction parallel to the opposite facet. Such a direction exists for d>=2 and leaves lambda_i invariant along projection fibers. The projected opposite facet has affine dimension d-2, while the projected p_i lies outside its affine hull. Hence the whole projected simplex is a (d-1)-dimensional pyramid with this apex and base.

The portion with descended lambda_i>1-t is, up to its boundary, the apex-centered homothetic copy of the entire projection with ratio t. It has exactly t^(d-1) times the projection volume. The projection of K has no point with lambda_i>1-t. Thus delta>=t^(d-1), and there exists k_i in K with lambda_i(k_i)>=1-rho, rho=delta^(1/(d-1)). This remains true when the projected opposite facet is not a simplex. No Euclidean cap constant, ball radius, or simplicial-base assumption appears.

The stated affine invariance of the relative-projection supremum is also correct. For an invertible linear map L, the homogeneous projection function satisfies pi_(LK)(u)=|det L| pi_K(L^(-1)u). Therefore ratios are carried through the bijection of directions induced by L^(-1). Translations do not change projection volumes. The new proof does not need to rely on this extra invariance.

The optional general support-width cap in Section 7 of the bridge is valid as well. The copy q+t(P-q), t=(h_P(v)-h_K(v))/(h_P(v)+h_P(-v)), lies in the appropriate supporting cap. Projection in a direction orthogonal to v preserves its strict separating coordinate on its relative interior. Its projected volume is t^(d-1)pi_P, yielding the stated inequality. It is not needed to repair or complete the simplex cap argument.

## 8. Stochastic determinants, matching, and the original maximum

### 8.1 Comparison simplex

The matrix Q whose columns are the P-barycentric coordinates of k_i is nonnegative and column-stochastic, with Q_ii>=1-rho. In the independent row-sampling interpretation of its determinant, collision outcomes contribute zero, even permutations +1, odd permutations -1. The identity probability p is at least 1-nrho. All negative outcomes are among the complementary outcomes, so

    det Q >= p-(1-p) >= 1-2nrho.

For rho<=1/(16n), this is at least 7/8, in particular positive. Thus the comparison points are affinely independent, the orientation is known, and their volume ratio to P is det Q. The probabilistic proof does not identify determinant with permanent.

### 8.2 Initial matching for the prescribed maximum S

Fix the arbitrary original S. Its P-barycentric vertex matrix W is nonnegative and column-stochastic. Maximality gives |det W|>=det Q>=1-eta, eta=2nrho<=1/8. Hadamard bounds every column norm by one; since the product is at least 1-eta, every column norm is at least 1-eta. For any probability vector, sum x_i^2<=max x_i, so every column has an entry at least (1-eta)^2>=1-2eta.

These entries must occupy distinct rows. A collision of two such dominant entries has probability at least (1-2eta)^2 under independent column sampling, and hence

    |det W| <= per W <= 1-(1-2eta)^2 <= 4eta < 1-eta.

The strict final inequality holds at eta=1/8 as well. Relabeling the vertices of S matches each column to a different row; it changes neither the simplex nor its centroid.

Now ||W-I||_1<=8nrho<=1/2. The Neumann-series bound yields

    ||B-I||_1 <= 8nrho/(1-8nrho), B=W^(-1).

The row vector of all ones is fixed by W and by B. Each column of B-I consequently sums to zero. In a zero-sum vector, an individual entry has absolute value at most half the sum of absolute values. Therefore

    beta := max_ij |B_ij-delta_ij| <= 4nrho/(1-8nrho) <= 1/2.

There is no missing row/column norm conversion or extra factor n here.

### 8.3 Maximality bootstrap checked algebraically

Writing r_i=1-W_ii, the identity (BW)_ii=1 implies

    B_ii(1-r_i) >= 1-beta r_i,
    B_ii-1 >= (1-beta)r_i/(1-r_i) >= r_i/2.

The denominator is positive because W_ii>=1-4nrho>=3/4. Thus in particular B_ii>=1. Replacing the ith vertex of the same S by k_i gives |(BQ)_ii|<=1. Nonnegativity of column i of Q and its sum one yield

    (BQ)_ii >= (1-rho)B_ii-rho beta.

The use of Q_ii>=1-rho is valid because B_ii+beta>=0. Combining with the replacement inequality gives

    B_ii-1 <= rho(B_ii+beta) <= rho(1+2beta) <= 2rho,

where B_ii<=1+beta follows from the previously established inverse-entry bound. Hence r_i<=4rho for all i. This is the needed improvement from O(nrho) to O(rho); it is genuinely obtained from maximality, not assumed from the initial determinant comparison.

A second inversion now gives

    ||W-I||_1<=8rho,
    ||B-I||_1<=8rho/(1-8rho).

The zero-sum argument bounds every negative entry of B by 4rho/(1-8rho)<=8rho. The final denominator is positive throughout the gate; rho<=1/(16n) is much smaller than 1/16 when n>=4.

Columns of B are the S-barycentric coordinates of the vertices of P. Thus all coordinates on P are at least -8rho. The exact centroid-dilation criterion gives

    P subset z_S+[1+8n rho](S-z_S).

This proves the stronger local conclusion, for the original S and its centroid.

## 9. Gates, endpoints, global assembly, and zero defect

There are two separate smallness parameters; the proof keeps them separate correctly.

1. The intrinsic conversion requires h<1/(2d). If 0<=e<=1/H, then

       h<=Ce<=1/(3d^2)<1/(2d).

   This is strict even at e=1/H. Therefore r=2dh<1, all anchor and weight gates hold, and delta<=3d^2h<=He<=1.

2. The geometric local branch requires rho<=1/(16n). At equality, eta=1/8, ||W-I||_1<=1/2, and beta<=1/2, while the collision contradiction remains strict. Every denominator remains positive. No open-endpoint argument is used.

3. When rho>1/(16n), maximality alone gives E<=n<16n^2rho. Together with the local estimate this proves the uniform bridge E<=16n^2rho for every delta in its full range. It is not necessary to force the conversion's delta into the exponentially smaller local rho gate.

4. For e<=1/H, the bridge gives E<=16n^2 H^(1/m)e^(1/m). For e>1/H, E<=n<n H^(1/m)e^(1/m), which is dominated by the same coefficient. The equality e=1/H is correctly assigned to the first branch.

5. If e=0, h=0 is obtained by the same weighted selection. The origin inclusion is then stronger, all lambda_i are positive, p_i=lambda_i, and the relative deficits vanish. The cap result puts each vertex of P in K, so K=P. At rho=0 the comparison and matching force W to be a permutation matrix for every maximum S; hence S=P up to vertex labels and E=0. No limiting replacement of S or dependence on a uniqueness assumption is needed.

The original translation by z_S is undone at the end. All barycentric and determinant steps reference this prescribed simplex. Matching is only a relabeling. This is the required every-original-simplex statement, rather than an existence statement for a favorable maximum simplex.

## 10. Uniform bound, asymptotic order, and lower-bound scope

For d>=3, n<=4d/3 and n+1<=5d/3 imply C<4d^4 and H<12d^6. The induction d<=3^((d-1)/2) gives

    H^(1/(d-1)) <= sqrt(12) times 27 = 54sqrt(3).

Thus

    G_d <= 16(16/9)(54sqrt(3))d^2 = 1536sqrt(3)d^2 < 4096d^2.

Also log H=6log d+O(1), so G_d=16d^2[1+O(log d/d)]. These are correctly proved for all integer d>=3; finite tables are unnecessary.

The exponent-sharpness statement invokes the pinned actual truncated-simplex family. Its e is asymptotic to d(d-1)t^(d-1)/n^2, and a prescribed vertex-set maximum has E=nt. The source also has other maximum simplices with different E; it does not require all of them to have E=nt. A single prescribed maximum, or the source's stronger lower bound for the best maximum, is enough to obstruct a larger uniform exponent. No abstract probability law is being used as a convex-body example.

The square-pyramid lower bound in imports/SQUARE_PYRAMID_LOWER_BOUND.md was also checked against its supplied direct facet certificate: the realized body has a=1/d, e=1/[d(d+1)], and E=d+1 at the displayed maximum simplex. The counting formula and volume give the claimed lower obstruction n[d n]^(1/(d-1)). This is asymptotically linear, so the upper audit does not close the linear-to-quadratic gap.

## 11. Supplemental independent exact checks

The independent checker constructs actual bodies

    K_t = {x_i>=0, t<=sum x_i<=1}

in dimensions 3, 4, and 5, at t=1/1000, 1/100, and 1/2. It enumerates vertex-set maximum simplices, translates by one such maximum's centroid, derives exact facet cone atoms and probabilities, and recomputes the first determinant moments by unordered-subset expansions with factorial factors.

It checks support-boundary identities, intrinsic support radius and diameter, centering, positive masses, the D/B identity, clipped witnesses and support-anchor assignment, and the exact integrated assignment coefficient. On the six cases passing the strict h gate, it additionally reconstructs the selected polar simplex, checks barycentric weight correction, the mixed-volume normalization and volume inequality, and the relative projection bound in every nonzero {-1,0,1}^d direction: 696 directions in total. It checks the bridge at all 36 vertex-set maximum simplices across the nine bodies. It additionally checks 400 exact rational instances of the relative-product inequality and exact matching/inverse endpoints for d=3,...,29.

All checks pass. They are regressions for arithmetic, direction, and normalization errors. They do not establish a theorem for arbitrary convex bodies, all directions, nonatomic laws, or all continuum-valued maximum simplices. Those claims are supplied by the analytic arguments above. The checker uses explicit errors rather than Python assertions so running it with optimization cannot silently disable its checks.

## 12. Issues and suggested clarifications

No mathematical repair is required for this source snapshot. The following optional editorial changes would make a self-contained presentation easier to audit; none changes the coefficient or hypotheses:

- Spell out once that the unit ball of N=h_(K-K) is (K-K)^circ and its dual norm is p_(K-K). The present text is correct, but these objects are easy to reverse.
- Repeat the actual cone-law pushforward formula in the intrinsic companion, so readers do not have to locate its definition in imports/POLYNOMIAL_REFINEMENT.md.
- Explicitly note that centering upgrades linear support span to affine support span, and that the boundary equality h_K=1 holds on the closed support by continuity.
- In the bootstrap, show the intermediate inequality B_ii(1-r_i)>=1-beta r_i. This makes the inequality direction and the subsequent lower bound B_ii>=1 transparent.
- Keep the three proof files together, with AUDITED_ORIGINAL_SOURCE_HASHES.json, if the statement is circulated. They form one proof; the short theorem file alone deliberately imports its substantive arguments from the companions.

The result should be described as a complete written proof that passed independent analytic model audit, with its explicit dependencies, until further verification is actually obtained.
