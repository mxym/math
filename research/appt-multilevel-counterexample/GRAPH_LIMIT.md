# A uniform graph limit and the four-level APPT mechanism

> Subsequent sharp result: [SHARP_ASYMPTOTIC.md](SHARP_ASYMPTOTIC.md) closes the remaining leading-constant gaps for every aspect ratio, and gives an equivalent uniform over all dimension pairs as total dimension grows. The proofs below remain valid; descriptions of then-open asymptotic gaps record intermediate progress. Exact finite maxima and absolute separability remain unresolved.


Research working proof, 10 October 2026. This note strengthens the lower bound on the unrestricted maximum, and determines a sharp asymptotic only within the stated nested four-level sector. No new preprint, Release, Lean certificate or external-review claim.

## 1. A deterministic extremal graph lemma

Let M tend to infinity, and let integers r satisfy M/r->0 and r/M^2->0. Let c>=0 and d>=0 depend on M, with

    r*c^2 -> v,    M*d -> u,    0<=u,v<infinity.

For a simple graph G with M vertices and r edges write A_G for its adjacency matrix and A_complete for the complete-graph adjacency matrix. Then

    max_G lambda_max(c A_G+d A_complete)
      -> max{sqrt(2v), (u+sqrt(u^2+4v))/2}.                       (G1)

In particular this is a bound uniform over ALL graph arrangements, not just over the two examples used to attain its limit.

### Upper bound: odd moments and a rank-one resolvent

Put H=c A_G and e=M^(-1/2)(1,...,1). The Frobenius identity gives

    Tr H^2=2r c^2,     ||H||<=sqrt(2r c^2).

For every vertex, the sum of the degrees of its neighbors is at most 2r. Entrywise,

    A_G^2 1 <=2r 1.

Iterating and using nonnegative entries gives, for each fixed integer j>=0,

    0<=e^T H^(2j+1)e
      <=c^(2j+1) (2r)^(j+1)/M ->0,                              (G2)

because r c^2 is bounded and sqrt(r)/M->0.

For an arbitrary sequence of graphs, take a weakly convergent subsequence of the spectral probability measures mu_M of H at e. All supports lie in a fixed compact interval. Equation (G2) says that every odd moment of the limit mu is zero. Polynomial approximation on a compact interval then implies that mu is symmetric.

In fact mu is supported on [-sqrt(v),sqrt(v)]. Otherwise it gives positive mass to an interval strictly above sqrt(v), and by symmetry to its reflected negative interval. For all sufficiently large M there is an eigenvalue in each interval. Their two squares alone exceed 2v, contradicting Tr H^2->2v. This also handles possible graph eigenvalues invisible to e: they may lie outside this smaller interval but never outside [-sqrt(2v)+o(1),sqrt(2v)+o(1)]. If v=0, the Frobenius bound already proves the statement.

Now

    c A_G+d A_complete = H+(Md)ee^T-dI.

Suppose along a subsequence its largest eigenvalue had limit lambda strictly larger than sqrt(2v) and than the right-hand root in (G1). The vanishing shift dI can be omitted. For large M this eigenvalue lies above the spectrum of H, so the rank-one eigenvalue equation is

    1=(Md) integral (lambda_M-x)^(-1) d mu_M(x).

If u=0, such an eigenvalue is impossible by the operator norm of the rank-one perturbation. If u>0, take the limit; the resolvent functions converge uniformly on the spectral interval because lambda>sqrt(2v). Symmetry and the smaller support of mu give

    1=u integral lambda/(lambda^2-x^2) d mu(x)
      <=u lambda/(lambda^2-v).

This forces lambda^2-u lambda-v<=0, a contradiction. Since the argument began with an arbitrary sequence of graphs, the upper bound is uniform over the graph maximum. It applies unchanged to graphs with at most r edges, with a limsup bound.

### Lower bound: two different graph arrangements

A clique on the largest integer t with t(t-1)/2<=r fits in M vertices. Complete its edge set arbitrarily to exactly r edges. Its Rayleigh quotient gives c(t-1)->sqrt(2v).

For the other term put h=floor(r/M). Then h->infinity, h/M->0 and h(M-h)<=r, with h(M-h)/r->1. Start with the complete bipartite graph with part sizes h and M-h and add edges to reach r. On the unit vectors constant on each part, the original graph plus d A_complete has quotient matrix tending to

    [ 0       sqrt(v) ]
    [ sqrt(v)    u    ].

Its top eigenvalue is the second expression in (G1). Adding nonnegative edges cannot decrease the top Rayleigh quotient. This proves both lower bounds and (G1).

## 2. A separate high eigenvalue decouples at this scale

Let a>=0 also vary with M, with a->a0<infinity. Require one distinguished edge e0 to belong to G, and add a E_e0. Then

    max_{G,e0 in G} lambda_max(d A_complete+c A_G+a E_e0)
      -> max{a0, sqrt(2v), (u+sqrt(u^2+4v))/2}.                  (G3)

For the upper bound split off the two endpoints of e0. Their 2-by-2 block has top eigenvalue a+c+d->a0. The cross block has norm at most (c+d)sqrt(2M)->0, since r/M->infinity. The remaining principal block is bounded by the upper part of (G1), with M-2 vertices and at most r edges. For the lower bound use the distinguished edge itself, or put either graph construction of Section 1 on the remaining M-2 vertices with r-1 edges. These constructions give the same limits and include e0. Thus (G3) is uniform as well.

This is precisely why a bounded-rank spike can coexist with an intermediate-rank plateau. It does not justify decoupling two arbitrary intermediate-rank plateaus.

## 3. Application to genuine APPT spectra

Use m as M, n/m->gamma in [1,infinity), D=mn, and any r_m with

    m<<r_m<<m^2.

Let nested projections Q<=P have ranks r and k, where

    m(m-1)/2<=k<=D-m(m+1)/2,

and let v0 be a unit vector in the range of Q. Normalize

    B=I+dP+cQ+a|v0><v0|,    a,c,d>=0.                            (G4)

The exact physical reduction (M4) in MESOSCOPIC.md says that this is APPT exactly when the graph maximum in (G3) is at most 2. Consequently, along parameter sequences a->a0, m*d->u, r*c^2->v, the necessary limiting inequalities are

    0<=a0<=2,  0<=v<=2,  0<=u<=2,  v<=4-2u.                    (G5)

Conversely, if all three quantities in the maximum in (G3) are strictly below 2, the states in (G4) are APPT for every sufficiently large m. This is an eventual all-unitary statement proved by the uniform graph bound; it is not a numerical feasibility assertion at a particular finite dimension.

The intermediate jump c is of order r^(-1/2), whereas the broad plateau jump d is of order m^(-1). These are distinct scales.

Write k/D->theta along a subsequence. Let

    T=dk+cr+a,
    S=d^2 k+c^2 r+a^2+2dc r+2a(d+c).

The four eigenvalues are 1+d+c+a once, 1+d+c with multiplicity r-1, 1+d with multiplicity k-r, and 1 with multiplicity D-k. Direct trace calculation gives

    D^2[Tr((B/Tr B)^2)-1/D]=(S-T^2/D)/(1+T/D)^2
      ->a0^2+v+gamma*u^2*theta(1-theta).                         (G6)

Here r/D->0, sqrt(r)/m->0, and all cross terms discarded in the limit vanish explicitly. In particular the limit is at most 4+v+gamma*u^2/4.

## 4. Sharp maximum within this four-level sector

Maximizing the last expression subject to (G5) gives

    L(gamma)=max{6+gamma/4, 4+gamma}.                             (G7)

Indeed v<=min(2,4-2u). On 0<=u<=1 choose v=2, giving maximum at u=1. On 1<=u<=2 the function 4+(4-2u)+gamma*u^2/4 is convex, so its maximum is at u=1 or u=2. The high spike has a0=2.

The bound applies to the whole sector, not only to convergent parameters. APPT gives a<=2 from an edge Rayleigh quotient, d(m-1)<=2 from the all-ones test, and bounded c sqrt(r) from the clique test. Thus every maximizing sequence has a subsequence with convergent a,md,rc^2 and k/D, to which (G3)-(G6) apply.

For achievability of the first candidate fix any rational epsilon in (0,1), use

    r=m ceil(sqrt(m)), k=ceil((m-1)n/2),
    a=2(1-epsilon), d=(1-epsilon)/m,
    c=2(1-epsilon)/ceil(sqrt(2r)).                               (G8)

All coefficients are rational, the nested ranks are valid eventually, and the graph maximum tends to 2(1-epsilon)<2. Hence these actual states are APPT eventually and have limiting coefficient (1-epsilon)^2(6+gamma/4). No explicit threshold in m is asserted for (G8). This is distinct from the finite-parameter-certified family in MESOSCOPIC.md.

The second candidate is obtained with c=0, a=2(1-epsilon), d=2(1-epsilon)/m and the same k; again (G3) ensures eventual APPT and gives (1-epsilon)^2(4+gamma). First let dimensions grow, and then let epsilon decrease to zero. These two limits prove the sharp sector maximum (G7). They also give the unrestricted lower bound

    liminf D^2[Pmax(m,n)-1/D]>=L(gamma).                          (G9)

The small slack is essential: a limiting graph norm equal to 2 does not imply exact finite-dimensional APPT. No finite boundary member is accepted on that invalid inference.

## 5. Current unrestricted interval

Together with UNRESTRICTED_BOUND.md,

    L(gamma) <= liminf D^2[Pmax-1/D]
               <= limsup D^2[Pmax-1/D] <= U(gamma),

where L(gamma)=max(6+gamma/4,4+gamma) and

    U(gamma)=min(4+4gamma,8+max(1,gamma-1)).

For square systems this is

    25/4 <= liminf m^4[Pmax(m,m)-1/m^2]
             <= limsup m^4[Pmax(m,m)-1/m^2] <=8.                 (G10)

This proves the exact order, a stronger lower constant, and an unrestricted upper constant. It does NOT prove that the limiting constant exists or equals 25/4, and does not classify unrestricted maximizers. Additional spectral levels and multiple intermediate scales remain a genuine mathematical obstruction. The graph lemma itself is a complete proved limit for the specified one-intermediate-scale input; it is not automatically applicable to a sum of several such graphs with shared vertex space.

The proof uses elementary finite-dimensional spectral theory, compactness of probability measures on a compact interval and polynomial approximation to identify a symmetric measure. It uses no random-graph law. Supporting exact checks are ancillary; no numerical optimizer, finite enumeration, or Lean certificate proves the unbounded result.

## Subsequent sharp balanced result

MULTISCALE.md proves a stronger unrestricted lower bound max(8,4+gamma) by using a lacunary hierarchy. Together with UNRESTRICTED_BOUND.md this settles the balanced constant at 8. The four-level sector value (G7) remains sharp for that sector; its earlier unrestricted interval is historical progress, not the current best lower bound.
