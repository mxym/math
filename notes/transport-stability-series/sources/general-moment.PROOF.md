# The sharp binary source–moment envelope

Research continuation, 8 October 2026; endpoint-proof revision following the batch analytic review. That review accepted the main envelope and identified a local inference gap in the two endpoint proofs. The comparison-based replacements below await a limited recheck. No formal verification or publication is claimed. This extends the binary geometry to a general moment budget rather than adding only a special source example. All source and target hypotheses and the dependence on the preceding candidate are stated below.

Throughout, the symbol ~ in response and modulus formulas denotes two-sided comparison by fixed positive constants, not an exact leading coefficient. Constants may depend on the fixed source and moment function, but not on the displayed varying masses or small distance w.

## 1. Source and target response functions

Fix the single product source from the binary mass-phase candidate: d>=2, with the same first marginal whose actual formula on a fixed initial interval is

    f(t)=c t^(alpha-1)L(t) exp(-t^2/2),   alpha>1,

where L is positive C^2 and satisfies t(log L)'->0 and t^2(log L)''->0, extended with a C^2 strongly convex potential and quadratic far tail. The other marginals are the symmetric compact bump g. Let F be the first-marginal CDF, q=F^(-1) on (0,1/2], and T=q(1/2). This source remains fixed for every target budget and distance parameter in a given theorem.

Let Phi:[0,infinity)->[0,infinity) be continuous, convex, strictly increasing, with

    Phi(0)=0,   Phi(1)=1,
    r -> Phi(r)/r^2 nondecreasing on (0,infinity).        (M)

The normalization at one is inessential. Define the rare-atom radius and its L^2 energy scale by

    R(u)=Phi^(-1)(1/u),            0<u<=1,
    E(m)=sqrt(m) R(m),             0<m<=1/2.             (1.1)

R is decreasing on (0,1], so R(1-m) in Section 3 is within its defined domain. The assumptions (M) give Phi(r)>=r^2 for r>=1, making Phi unbounded and its inverse well-defined. E is nondecreasing and continuous on (0,1/2], and 0<E(m)<=1. Indeed

    E(m)=[Phi(R(m))/R(m)^2]^(-1/2).

Allow either a finite or infinite limit of Phi(r)/r^2 as r->infinity. Thus this theorem includes a purely quadratic budget, as well as genuine uniform-integrability budgets.

The target class is

    C_(Phi,2)={mu: #supp(mu)<=2, integral Phi(|y|) dmu<=1}.

Define Omega_(Phi,2), its minimum-positive-atom-mass variant Omega_(Phi,2,eta), and its fixed-mass-vector variant Omega_(Phi,[m]) exactly as in the binary candidate, using this moment budget. For the latter, both targets have mass vector (1-m,m). Dirac and coincident-label degeneracies are permitted and merged; zero labels do not count. There is no separate support-radius bound.

Put

    J(t)=E(F(t)),       0<t<=T,
    B(t)=t J(t),
    H(r)=max_(r<=t<=T) J(t)/t.                           (1.2)

B is continuous strictly increasing, since t is strictly increasing and J is positive and nondecreasing. Also B(t)->0 at zero. Let h_w=B^(-1)(w) for 0<w<B(T).

### Theorem A: one sharp envelope for the source and arbitrary moment growth

There are constants c,C,w_0>0, depending only on the fixed source and Phi, such that, simultaneously for 0<w<=w_0,

    Omega_(Phi,[m])(w)
       ~ w+min{E(m), [w E(m)/q(m)]^(1/2)},     0<m<=1/2;       (1.3)

    Omega_(Phi,2,eta)(w)
       ~ [w H(max{h_w,q(eta)})]^(1/2),        0<eta<=1/2;     (1.4)

    Omega_(Phi,2)(w) ~ [w H(h_w)]^(1/2).                  (1.5)

The constants are independent of m,eta,w. The source and Phi are fixed. The radius R(m), including its possible divergence at small m, is paid for by the actual moment budget.

These statements use no centered-potential estimate (P). Their sole geometric input is the all-orientations halfspace estimate (H) in Section 2, whose complete written proof is in Section 2 of the preceding binary manuscript; its argument is recalled here. The batch analytic review accepted that geometric input, the binary mass theorem, and the present main envelope. The additional moment optimization is given here explicitly. The repaired endpoint proofs in Section 7 remain subject to the limited recheck; no full formalization or historical-priority claim follows from the review.

## 2. Geometric and coupling inputs, with dependency boundary

For H_(m,u), the upper halfspace of rho-mass m with unit normal u, the needed bound is

    rho(H_(m,u) triangle H_(m,v))
       <=C min{m, angle(u,v) m/q(m)},    0<m<=1/2.       (H)

Why this applies: the zero-extended source density is continuous and W^(1,1), and |x|r is W^(1,1). For the weighted score A=1+|x||grad log r|, the boundary power alpha>1 and the fast transverse/tail decay give

    A^*(u)<=C/q(u),    integral_0^m A^*(u)du<=C m/q(m).

The last step uses the inverse-CDF power 1/alpha<1. The divergence theorem on an arbitrary halfspace yields

    integral_(boundary H) |x|r <= integral_H A d rho <=C m/q(m).

Along a moving normal with the mass kept fixed, the derivative of the threshold is the boundary average of the normal's derivative dotted with x. Its weighted absolute normal velocity is therefore at most twice the weighted |x| trace. Integrating along a shortest spherical path proves (H), combined with the trivial 2m bound. This is the same complete argument and regularity justification in `../binary_mass_phase_20261008/PROOF.md`, Section 2; no new premise about arbitrary sources is being inferred.

The coupling input is purely finite-dimensional. Write two centered binary targets as the laws of

    v(I-m),      z(J-n),

where I,J are Bernoulli of means m,n<=1/2. A coupling is described by tau=P(I=J=1), and its cost is

    m(1-m)|v|^2+n(1-n)|z|^2-2(tau-mn) v dot z.           (2.1)

For acute vectors and m<=n, the optimal endpoint tau=m gives exactly

    W_c^2=m(1-n)|v-z|^2
             +(n-m)[m|v|^2+(1-n)|z|^2].                (2.2)

This identity is independent of any target moment assumption.

For obtuse vectors, tau=0. If m+n<=3/4, the centered Wasserstein cost controls m|v|^2+n|z|^2 from below by a factor 1/4, so the source-map distance is at most C W_2. If m+n>3/4, both masses exceed 1/4; reversing the labels of one target makes the vectors acute and all relevant masses lie in [1/4,3/4]. These two cases handle labels, collisions and opposite vectors without assuming a minimum support separation. A Dirac target gives map distance exactly W_2.

## 3. The upper bound with the general moment response

If mu=(1-m)delta_a+m delta_b is in C_(Phi,2), convexity and (M) give

    |bar_mu|<=1,
    |b-a|<=R(1-m)+R(m)<=2R(m),       0<m<=1/2.           (3.1)

For acute target gaps v,z and m<=n, the same algebra as (2.2), together with nesting of halfspaces of the same normal, bounds the squared map discrepancy by

    C W_2^2 + C |z|^2 rho(H_(m,v/|v|) triangle H_(m,z/|z|)).

The angle is at most C|v-z|/max{|v|,|z|}. Formula (2.2) gives |v-z|<=C W_2/sqrt(m), while |z|<=2R(n)<=2R(m). Thus (H) yields

    ||T_mu-T_nu||_2^2
       <=C [w^2+min{mR(m)^2, w sqrt(m)R(m)/q(m)}]
       =C [w^2+Psi_Phi(w,m)],                            (3.2)

    Psi_Phi(w,m)=min{E(m)^2, w E(m)/q(m)}.

If the gaps are obtuse and m+n<=3/4, the preceding Cw estimate suffices. In the remaining obtuse case, the masses are at least 1/4, so (3.1) bounds both gaps by the fixed constant 2R(1/4). Reversing labels and using (H) yields squared map distance <=C(w^2+w).

For the fixed-mass class, that last case only occurs at m>3/8. By decreasing w_0 below q(3/8)E(3/8), the quantity Psi_Phi(w,m)=wE(m)/q(m) is bounded below by c w throughout that compact mass interval. For minimum-mass and unrestricted classes, the supremum over admissible masses includes m=1/2, which similarly absorbs w and w^2. This proves all required upper estimates in terms of Psi_Phi, uniformly in the mass parameters.

Only convexity was used to bound the mean. Monotonicity of R and E, rather than a power law, supplies the rest.

## 4. Exact-mass lower realization and mass optimization

Given m and t=q(m), use the source's first coordinate X and symmetric transverse coordinate Z. For 0<b<=epsilon t choose ell_b so

    E F(ell_b+bZ)=F(t)=m.

The derivative hypotheses on f, and compact-range regularity up to T, give uniformly

    ell_b=t+O(b^2/t),
    rho({X<t} triangle {X<ell_b+bZ})~b f(t)~b m/t.        (4.1)

This is an exact mass match, not an asymptotic one: only the displacement and disagreement estimates are asymptotic comparisons.

Let R=R(m), and take

    mu=(1-m)delta_0+m delta_(-R e_1),
    nu=(1-m)delta_0+m delta_(R(-e_1+b e_2)/sqrt(1+b^2)).  (4.2)

Their Phi moments equal m Phi(R)=1 exactly. Their maps are gradients of the global convex hinges

    R(t-x_1)_+,
    R/sqrt(1+b^2)(ell_b-x_1+b x_2)_+.

The same-label target coupling costs at most E(m)b, and the map discrepancy squared is at least

    c R(m)^2 b m/t = c b E(m)^2/t.

Choose b=epsilon min{t,w/E(m)}, with one fixed epsilon<=1. This gives W_2<=w and squared map discrepancy >=c Psi_Phi(w,m). It uses two distinct positive-mass atoms, at exactly the prescribed masses, throughout.

The w term in (1.3) follows from translating two short distinct atoms by w e_2. For w<=1/4 all atom norms can remain <=1/2, so their Phi moments are below one; the map and Wasserstein distances both equal w. Combining this example with the hinge example proves (1.3).

For the variable-mass classes, optimize over m in [eta,1/2], or (0,1/2]. Under m=F(t), equality of the two terms of Psi_Phi is exactly w=tJ(t)=B(t). On t<=h_w, the smaller term is J(t)^2, nondecreasing in t. On t>=h_w, it is wJ(t)/t. Hence the following is an EXACT scalar identity:

    sup_(eta<=m<=1/2) Psi_Phi(w,m)
       =w max_(max{h_w,q(eta)}<=t<=T) J(t)/t.             (4.3)

The unrestricted identity omits q(eta). Compactness makes the displayed maximum attainable. Using that maximizing mass in (4.2) respects the minimum-weight condition: m>=eta and 1-m>=1/2>=eta. Equations (3.2)-(4.3) prove (1.4)-(1.5).

Thus every value contributing to the scalar maximum has a genuine two-atom convex-gradient realization. No arbitrary energy step profile is declared transport-realizable.

## 5. Exact uniform-continuity threshold on binary targets

Under (M),

    Omega_(Phi,2)(w)->0 as w->0
       if and only if Phi(r)/r^2->infinity as r->infinity. (5.1)

Proof. This growth condition is equivalent to E(m)->0 as m->0. If it holds, for any delta>0 split the supremum of Psi_Phi into m<=delta, bounded by E(delta)^2, and m>=delta, bounded by w times a fixed compact maximum. First let w->0 and then delta->0. The upper bound tends to zero.

If instead E(m)->e_0>0, then for each small w choose m with q(m)E(m)<=w. The fixed-mass lower construction saturates and has map distance >=c E(m)>=c e_0. Thus even two atoms prevent uniform continuity, although each individual pair still has the usual qualitative Brenier continuity when targets converge in W_2 with their second moments. The offending family has no uniform integrability of second-moment tails.

This is the standard moment-growth / uniform-integrability threshold expressed as a sharp binary transport statement. No novelty is claimed for the general de la Vallee Poussin principle itself. The new quantitative content is the complete source-CDF / response-function envelope and its matching realizations.

## 6. A general asymptotic-index phase principle

Suppose additionally that E is C^1 for small m and

    m E'(m)/E(m) -> kappa in [0,1/2].

Then logarithmic differentiation and t f(t)/F(t)->alpha give

    t J'(t)/J(t) -> r=alpha kappa.

Integrating these derivative bounds proves all fixed-ratio and Potter comparisons needed below directly. In particular J is regularly varying with index r. If Phi is C^1 for large radii and r Phi'(r)/Phi(r)->p in [2,infinity], inverse differentiation gives kappa=1/2-1/p, with 1/infinity=0. Thus the product alpha kappa compares a source boundary index with a target-moment growth index.

- If r<1, J(t)/t has negative index. Fixed-exponent Potter bounds show its running maximum over [h,T] is comparable to J(h)/h. Thus

      Omega_(Phi,2)(w) ~ J(h_w)=w/h_w.

  This includes r=0 and may give a non-Hölder modulus.
- If r>1, J(t)/t tends to zero and has a finite positive global maximum, so Omega_(Phi,2)(w)~w^(1/2).
- If r=1, the quotient is slowly varying and the running maximum in (1.5) is the sharp correction. Its endpoint value alone need not suffice.

For Phi(r)=r^p, p>2, E(m)=m^(1/2-1/p); hence kappa=(p-2)/(2p)=1/(2s), recovering exactly the alpha=2s binary phase theorem. The power law is one specialization of this source–target index product.

## 7. Two substantive endpoint applications

### 7.1 Barely superquadratic budgets

Let Phi(r) be comparable for large r to

    r^2 [log(e+r)]^gamma,       gamma>0,

with an innocuous convex normalized extension satisfying (M). Then

    R(m)~m^(-1/2)[log(e/m)]^(-gamma/2),
    E(m)~[log(e/m)]^(-gamma/2).

For ANY of the fixed sources above with alpha>1 and any admissible source factor L, log(1/F(t))~alpha log(1/t). Therefore

    Omega_(Phi,2)(w) ~ [log(e/w)]^(-gamma/2).              (7.1)

Proof. Write a=gamma/2>0 and tau(t)=log(e/t). The assumed two-sided comparison for Phi, followed by inversion, gives E(m)~[log(e/m)]^(-a). Since the fixed source has positive boundary index alpha, log(e/F(t))/log(e/t) tends to alpha. Therefore

    J(t)~tau(t)^(-a)

for all sufficiently small t. This uses comparison only; it asserts neither differentiability of Phi or E nor the logarithmic-derivative limit required in Section 6.

Choose 0<t_0<T small enough that the explicit comparison function k(t)=t^(-1)tau(t)^(-a) is decreasing on (0,t_0]. Indeed

    d log k(t)/d log t=-1+a/tau(t)<0.

For h<=t_0, the comparison with k and its divergence at zero absorb the finite maximum over the compact remainder [t_0,T]. Hence

    H(h)~h^(-1)tau(h)^(-a)~J(h)/h.

Use the main envelope (1.5) and the EXACT identity w=h_w J(h_w), not the extra index hypotheses of Section 6. They give Omega_(Phi,2)(w)~J(h_w). Also w~h_w tau(h_w)^(-a), so taking logarithms yields

    log(e/w)=log(e/h_w)+a log log(e/h_w)+O(1).

Consequently log(e/h_w)/log(e/w) tends to one, and Omega_(Phi,2)(w)~[log(e/w)]^(-gamma/2). This proves (7.1) under the original comparison hypotheses, without adding regularity assumptions on Phi.

Thus the optimal modulus can be non-Hölder even on a two-atom class for a single fixed strongly log-concave source. Every positive mass floor restores a one-half small-w law, with its sharp vanishing-floor crossover still given by (1.4). This is a target-tail obstruction, separate from source irregularity or infinite target cardinality.

### 7.2 Stretched-exponential budgets

Let Phi(r) be comparable for large r to exp(r^q), q>0, with a convex normalized extension satisfying (M). Then

    E(m)~sqrt(m)[log(e/m)]^(1/q).

If the source has L(t)=[log(e/t)]^gamma, then

    J(t)~t^(alpha/2)[log(e/t)]^(gamma/2+1/q).

The sharp binary law is therefore

    Omega_(Phi,2)(w) ~
       w^(alpha/(alpha+2))
           [log(e/w)]^((gamma+2/q)/(alpha+2)),       1<alpha<2;
       w^(1/2)[log(e/w)]^(max(gamma+2/q,0)/4),       alpha=2;
       w^(1/2),                                    alpha>2.   (7.2)

Proof. In this proof write theta>0 for the stretched-exponential exponent, to distinguish it from the source quantile function q(·); theta is the exponent denoted q in statement (7.2). Comparison of Phi(r) with exp(r^theta), followed by inversion, gives

    R(m)~[log(e/m)]^(1/theta),
    E(m)~sqrt(m)[log(e/m)]^(1/theta).

Set A=alpha/2, b=gamma/2+1/theta, and tau(t)=log(e/t). The source CDF estimate then yields

    J(t)~t^A tau(t)^b.

Apply the main envelope (1.5) directly to these comparison functions. No differentiability or logarithmic-derivative limit for Phi or E is inferred, and Section 6 is not invoked.

If A<1, the explicit function t^(A-1)tau(t)^b is eventually decreasing as t increases and diverges at zero: its logarithmic derivative is A-1-b/tau(t), which is eventually negative. The compact-range contribution is absorbed, so

    H(h)~h^(A-1)tau(h)^b~J(h)/h,
    Omega_(Phi,2)(w)~J(h_w).

The exact equation w=h_w J(h_w) gives w~h_w^(A+1)tau(h_w)^b. Taking logarithms first shows tau(h_w)~log(e/w); substituting this comparison back gives the two-sided inverse estimate

    h_w~w^(1/(A+1))[log(e/w)]^(-b/(A+1)).

Therefore

    Omega_(Phi,2)(w)~w^(A/(A+1))[log(e/w)]^(b/(A+1)).

If A>1, the comparison implies J(t)/t tends to zero at the boundary. This quotient is bounded on (0,T] and is positive somewhere. Thus H(h) is bounded above and below by positive constants for all sufficiently small h, giving Omega_(Phi,2)(w)~sqrt(w).

If A=1, comparison with tau(t)^b and the positive compact-range contribution gives

    H(h)~tau(h)^(max(b,0)).

Here w=h_w J(h_w)~h_w^2 tau(h_w)^b, so tau(h_w)~log(e/w). The main envelope consequently gives

    Omega_(Phi,2)(w)~sqrt(w)[log(e/w)]^(max(b,0)/2).

Substitute A=alpha/2 and b=gamma/2+1/theta, then write theta as q to recover exactly (7.2), including every real gamma and the boundary A=1. The binary critical source exponent is alpha=2, independent of the stretched-exponential exponent. All conclusions hold for the originally stated comparison class of Phi, with no additional C^1 or logarithmic-derivative assumption.

These endpoint applications illustrate qualitatively different continuity and threshold behavior; they are not asserted to be historically novel independently of the general envelope.

## 8. Fixed support-radius variant

For binary targets supported in the unit ball, repeat the same proof with

    R(m)=1,     E(m)=sqrt(m).

Every upper step only needs the corresponding gap bound, and the hinge lower targets have norm exactly one. The moment-function assumptions are unnecessary for this variant. The conclusions (1.3)-(1.5) remain valid with this response.

For the pure power source f(t)~t^(alpha-1), alpha>1, this yields

    Omega_(bounded,2)(w) ~ w^(min{alpha/(alpha+2),1/2}).    (8.1)

At alpha=2 a nontrivial source factor is again treated by the running maximum. In contrast, the completed three-atom interior-strip construction supplies a one-third lower obstruction even with all locations bounded. The distinction between source-tail degeneration, moment tails, and a third atom is thus visible within one source family.

## 9. Scope, assumptions, and literature

- The all-directions halfspace estimate (H) is the only analytic interface reused from the preceding binary manuscript. It and the main envelopes were accepted in the batch analytic review. The replacement endpoint proofs in this revision await a limited recheck; that status does not imply formal verification or an audit of any upstream theorem (P).
- The upper/lower transport realization, general moment replacement, exact mass maximization, and endpoint evaluations are fully given here. There is no use of (P).
- No general N>=3 minimum-weight theorem is claimed. Moving/colliding supports require a further argument not supplied by fixed-support semi-discrete stability alone.
- The condition Phi(r)/r^2 nondecreasing ensures a monotone L^2 rare-atom response. Removing it would require an appropriate scalar envelope; it is not dropped by inference.
- The source requires alpha>1 so the weighted-score trace proof has no boundary jump and its quantile integral is finite.

Primary context: Bansil--Kitagawa, https://arxiv.org/html/2002.02022 ; Delalande--Merigot, https://arxiv.org/html/2103.05934 ; Letrouit, https://arxiv.org/html/2510.13265v1 . Letrouit already uses rotating equal-weight binary targets for sources with density blow-up. The present candidate concerns matching source–moment laws on the displayed fixed vanishing-boundary sources; neither the rotation mechanism nor generic Lorentz / uniform-integrability principles are claimed new.

The two earlier manuscripts are preserved byte-for-byte. The original reviewed version of this manuscript and its README are retained in original_reviewed_snapshot/. The review and its counterexample to inferring derivative limits from comparability are recorded in ../transport_batch_independent_review_20261008/REVIEW.md, Sections 5-6. Historical priority and publication suitability remain separate from the present mathematical repair.
