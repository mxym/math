# Complete scalar mixed-phase geometry in the APPT linear-order window

Author: Yongxian Zhang (张永贤), South China University of Technology.
Contact: mxymmxym1@gmail.com. ORCID: 0009-0000-3864-3536.
Date: 2026-10-15. Author manuscript with an exact integer interval certificate.
Independent ordinary review remains pending. No Lean claim, submission or
new-major claim. No funding. OpenAI assisted the investigation and writing.
Original text: all rights reserved; third-party attribution and rights remain.

## Scope, dependencies and attribution

This note completes, at author level, the scalar phase classification in the
linear-order finite-peak APPT window. The original objects are complex density
matrices that remain PPT after every global unitary. The credited main-line
value theorem L and nearoptimizer theorem S apply with m<=n, m tending to
infinity, alpha>1, alpha/m tending to c>0 and 3^alpha/(mn) tending to finite
r>=0. The exact credited source bytes are in CREDITED_SOURCES.json. This
does not change the density/APPT definitions or replace their quantifiers
by a special candidate family.

The new mathematical input is a whole-domain proof that the interior
stationary-value curve has exactly two turns. The h elimination is credited
to L20 and independently rederived below. The lower-bulk and upper-pole
envelope descriptions were also developed in parallel in the APPT main-line
investigation; we rederive them for the logical completeness of this note,
without claiming them as an independent new discovery.

The exact frozen author dependencies are:

    NO_ISLANDS.md
    f7509ff124d76f12855a55705f317c51133c8e1a93fcadc7f230bebd91b8ad16

    LAST_MIXED_BOUNDARY.md
    6e4f77e2bbecbc5e71f426925d444e8e1a9b69d2ffebcbef88badc1f4e87f0a0

    CRITICAL_UNIQUENESS_CERTIFICATE.md
    be76b90de9277fab91c1f676f8de7619c2d58a5b79cf65cf06839d7ce8e7637e

The third input includes its frozen exact integer engine and certificate,
as bound in CRITICAL_V1_MANIFEST.json. It proves, conditional on the earlier
scalar inputs, one last mixed parameter with 0.2595<c_star<0.26 and a unique
nondegenerate interior triple tie. All these new inputs require independent
ordinary review; none is silently treated as an already reviewed theorem.

This fourth note adds a separate exact certificate and replay. It does not
alter the earlier frozen texts or broaden their review scopes. Its interval
base is the unchanged critical_exact_intervals.py (SHA-256
78ab0341d6079ceedb7be01abc9eba8608d50df0ad2136fa53b554a547c6ce1c).
The exact source, certificate, replay and final paper hashes for this note
are bound together in GLOBAL_MIXED_V1_MANIFEST.json.

No exact finite-dimensional entropy or purity formula, all-order spectral
classification, new Lean coverage, or external priority claim is made.

## 1. Scalar definitions

For c>0,r>=0,0<=L<=2 and 0<=h<=1, put

    G(L)=2L^2/[3(2-L)]                              (L<2),
    B=exp(-cLh)[1+h(exp(cL)-1)],
    P=exp[-c(Lh+G(L))]                              (L<2),
    P(c,2,h)=0,        F=B+rP,         V(c,r)=max F.

At L=0 the value is 1+r independently of h. Write

    q(t)=t/(exp(t)-1),      d(t)=1-q(t),
    w(t)=-log q(t),         g(t)=w(t)-d(t)=log b(t),
    b(t)=(exp(t)-1)/t * exp[-1+q(t)],
    s(t)=w'(t)=1-d(t)/t,
    h_b(c)=1/(2c)-1/(exp(2c)-1),
    r_0(c)=b(2c)-1.

The unique pure bulk point is (L,h)=(2,h_b(c)) with value b(2c).
The pole class is {0}x[0,1] with value 1+r. Its h coordinate is redundant.
We count this class as one phase throughout.

Set K=2c,k=cL=Kx,x=L/2 in (0,1), and

    a(k)=2k^2/[3(K-k)],
    y(k)=s(k)+a'(k)>0,
    R_stat(K,k)=g'(k)exp(a(k))/[q(k)y(k)].          (1.1)

Primes in (1.1) refer to k with K fixed. The derivatives g',g'' are positive,
as shown in NO_ISLANDS.

## 2. The complete phase theorem

For each 0<c<c_star there exist exactly two numbers

    0<r_B(c)<r_0(c)<r_P(c)<infinity.

The following is the complete scalar argmax classification for all r>=0:

* If r<r_B(c), the argmax is the unique pure bulk point.
* At r=r_B(c), it consists exactly of the bulk point and one interior point.
* If r_B(c)<r<r_P(c), it consists of exactly one interior point.
* At r=r_P(c), it consists exactly of one interior point and the pole class.
* If r>r_P(c), it consists exactly of the pole class.

Every interior point appearing here is nondegenerate with negative definite
scalar Hessian. The two functions r_B and r_P are real analytic on
(0,c_star). The unique interior mixed maximizer is real analytic in (c,r)
throughout the open mixed region and extends locally analytically across
either coexistence curve. It is determined without a competing-root choice:
its k is the unique solution of r=R_stat(K,k) on the strictly decreasing
middle arc of R_stat, and its h is given by (3.1) below.

At c=c_star the complete value is max{b(2c),1+r}; only the bulk occurs below
r_0, only the pole above r_0, and at r_0 there are exactly three phase
classes: bulk, pole and one nondegenerate interior point. At c>c_star the
value is again the pure envelope, and the crossing r_0 has exactly the two
pure classes and no interior tie. The threshold satisfies

    519/2000<c_star<13/50.

The analytic coexistence curves extend to the triple point, with the linear
closing and slopes proved in CRITICAL_UNIQUENESS_CERTIFICATE.md. Thus no
additional mixed components in c, multiple mixed maximizers, hidden interior
coexistence sets, or missing boundary ties remain in this scalar problem.

All assertions in this note are author results pending independent ordinary
review of the entire dependency chain and the new exact certificate. This
scope does not convert the entire physical entropy problem at all orders
and all finite dimensions into a solved problem.

## 3. Exact h elimination and the stationary equation

Fix K>0,0<k<K. The unique maximizing h of F is

    h_opt=max{0,[d(k)-r q(k)exp(-a(k))]/k}.        (3.1)

This is always less than one, since d(k)<k. To verify it, write

    F=exp(-kh)[1+h(exp(k)-1)+r exp(-a)].

After removal of its positive exponential factor, F_h is an affine strictly
decreasing function of h. Its zero is (3.1) without the maximum with zero.
The derivative at a zero has F_hh=-k(exp(k)-1)exp(-kh)<0. A nonpositive
zero leaves the maximum at h=0; an interior zero is the unique maximum.

For r>0 define C(k)=d(k)exp(a(k))/q(k). The factors d,exp(a),1/q increase
strictly, so C increases strictly from zero to infinity on (0,K). Thus a
unique k_a in (0,K) satisfies C(k_a)=r. The h optimum is zero for k<=k_a
and is strictly interior for k>k_a. On the h=0 part the value is
1+r exp(-a)<1+r for k>0, so no such point is a global maximizer. On the
interior part the exact optimized logarithmic value is

    f(k)=log max_h F=g(k)+r q(k)exp(-a(k)).       (3.2)

Its derivative is

    f'(k)=q(k)exp(-a(k))y(k)[R_stat(K,k)-r].      (3.3)

Every root R_stat(K,k)=r is automatically in the h-interior domain, because

    R_stat(K,k)/C(k)=s(k)/[s(k)+a'(k)]<1.

At k=k_a the interior derivative is -d(k_a)a'(k_a)<0, agreeing with the
derivative from the h=0 part. There is no missed local maximum at the
change between these formulas. For r=0, the unique global maximum is
already the pure bulk maximum of B.

## 4. Two-turn theorem for every 0<K<=13/25

There are exactly two numbers 0<alpha(K)<beta(K)<1 such that R_stat, viewed
as a function of x=k/K, increases on (0,alpha), decreases on (alpha,beta)
and increases on (beta,1). Their bounds are

    3/10<alpha(K)<2/5,
    1-(2/5)K<beta(K)<1-(3/10)K.                 (4.1)

Both turns are simple, and the curves are analytic for K>0. The proof below
includes the entire interval down to K=0 through removable continuations;
no lower cutoff on K is introduced.

Put R(t)=t g''(t)/g'(t), extended by R(0)=1, and delta=1-x. A direct
logarithmic derivative of (1.1) gives

    k y (log R_stat)'=R(k)y+k y^2-k s'(k)-4x/[3delta^3].

Define Y=2+delta^2(3s(k)-2) and

    M(K,x)=3R(k)Y delta^2+kY^2-9k s'(k)delta^4-12x delta.   (4.2)

Since y=Y/(3delta^2), M is nine delta^4 times the preceding numerator.
Therefore M has exactly the sign of (log R_stat)' whenever K>0,0<x<1.

The right boundary layer is regularized by z=delta/K and x=1-Kz. Put

    Z=2/3+K^2 z^2(s(k)-2/3),        k=K(1-Kz),
    T(K,z)=K R(k)Z z^2+xZ^2-K^4 x s'(k)z^4-(4/3)xz.       (4.3)

Exact substitution gives M(K,1-Kz)=9K T(K,z). Thus T has the same sign
for positive K. It is regular at K=0, where T(0,z)=4/9-4z/3.

For the middle region use delta in [0,3/5],v=K/delta in [0,5/2]. The
expression M/delta has the removable continuation

    3R(k)Y delta+v xY^2-9v x s'(k)delta^4-12x,
    x=1-delta, K=v delta, k=Kx.                 (4.4)

Only K<=13/25 is relevant in this chart. The certificate discards boxes
lying entirely above that cap and intersects K intervals with the cap
on boxes that cross it. Such an intersection is a safe enclosure for
every admissible point in the box; the explicit v terms are retained.

The new integer certificate establishes the following whole-box signs:

1. M>0 for 0<=K<=13/25,0<=x<=3/10.
2. M_x<0 for 0<=K<=13/25,3/10<=x<=2/5.
3. The expression (4.4) is strictly negative on delta in [0,3/5],
   v in [0,5/2],v delta<=13/25.
4. T>0 for 0<=K<=13/25,0<=z<=3/10.
5. T_z<0 for 0<=K<=13/25,3/10<=z<=2/5.
6. T(K,2/5)<0 for 0<=K<=13/25.

These signs imply the two-turn theorem directly. The first two signs and
the third sign at x=2/5 give exactly one zero alpha in (3/10,2/5), with
strictly negative M_x there. The third sign also gives M<0 throughout
2/5<=x<=1-(2/5)K: indeed delta<=3/5 and K/delta<=5/2 there. The fourth
through sixth signs give exactly one zero z_b in (3/10,2/5), hence beta
=1-K z_b, with a change from negative M to positive M as x increases.
The far right is positive by sign 4. There are no uncovered gaps between
these regions, since 1-(2/5)K>=99/125>2/5 on the stated K interval.

At alpha, M_x<0; at beta, M_x=-9T_z>0. These make the two turns simple
and give analytic dependence by the implicit-function theorem. The proof
does not merely count numerical roots.

## 5. Regular analytic enclosures at K=0

The new code uses no formulas with division by t at t=0. For p=1,2 let

    E_p(t)=sum_(j>=0) t^j/(j+p)!.

These are entire, with E_1(0)=1,E_2(0)=1/2. Define

    H=E_2/E_1=d(t)/t,     s=1-H,
    A=H(1-H)=g'(t)/t,
    R=1+t A'/A,
    R'=A'/A+t[A''/A-(A'/A)^2].                  (5.1)

The equalities for positive t follow from E_1-1=t E_2 and the scalar
derivatives, and the formulas give their removable continuations at zero.
The derivatives used in the code are exactly

    H'=(E_2'-H E_1')/E_1,
    H''=(E_2''-2H'E_1'-H E_1'')/E_1,
    A'=H'(1-2H),        A''=H''(1-2H)-2(H')^2,
    s'=-H',            s''=-H''.

The derivatives M_x and T_z in the source are obtained by the ordinary
chain and product rules, using k_x=K and k_z=-K^2 respectively. All
five identities for the derivative and chart transformations were also
checked symbolically in the optional author control
GLOBAL_TURN_ALGEBRA_CONTROL.json. The identities and the formulas above,
rather than that optional control, are the mathematical dependencies.

For r=0,1,2 the nonnegative series

    E_p^(r)(t)=sum_(j>=0) [(j+r)!/(j!(j+r+p)!)] t^j

has coefficients at most 1/j!. On 0<=t<=1, truncating at degree N=64
therefore leaves a tail between zero and 3/(65!). This follows by comparison
with the tail of exp(t) and its Lagrange remainder, using exp(1)<3. Each
coefficient, each Horner operation and the rational tail are enclosed with
the exact outward integer arithmetic at scale 2^160 from the frozen base
engine. Series monotonicity gives endpoint enclosures for each E_p^(r) on
an interval. Equations (5.1) and the formulas (4.2)-(4.4) then give enclosures
by ordinary interval operations, including at K=0. Denominators are checked
to exclude zero on each accepted leaf. All scalar inputs t are checked to
lie in [0,1]; in fact the cap gives t<=13/25.

There is no floating-point arithmetic and no transcendental library call
in these new function enclosures. The regular charts explicitly cover the
small-K width layer beta=1-O(K), rather than assuming uniformity there.

## 6. Exact finite cover and its complete replay

The certificate GLOBAL_MIXED_TURN_CERTIFICATE.json binds its source
global_mixed_turn_certificate.py and the unchanged integer base engine by
SHA-256. Its six covers contain respectively

    35, 1, 28, 5, 1, 4 leaves; total 74.

Each leaf records both exact rational coordinate intervals and its exact
outward integer sign enclosure. Some middle-chart leaves are wholly above
the K cap and are explicitly labeled `outside_K_cap`; all other leaves
have the required strict sign. A leaf means the sign holds on the entire
box, not at a chosen point.

The replayer replay_global_turn_certificate.py recomputes every integer
bound exactly, checks every strict sign and cap exclusion, and checks full
coverage. For a two-dimensional cover it sorts all first-coordinate edges,
then verifies on each rational open slab that the active second-coordinate
intervals tile the entire required second interval with exact adjacency
and no overlaps. As there is no box edge inside such a slab, the active
closed boxes cover its closure. The finitely many slabs therefore cover
the full closed rectangle, including all edges. The one-dimensional last
cover is checked by exact endpoint adjacency. This is stronger than only
checking total area and precludes compensating gaps and overlaps.

The code's recursive bisections and the independently replayed partition
conditions provide exhaustive domain coverage. No finite sampled grid,
unjustified numerical root count, random test, or missing end region is
used. All author replay results remain author evidence, pending ordinary
independent mathematical and code review of the exact frozen bytes.

## 7. Unique nondegenerate interior maximum for arbitrary r

For each 0<K<=13/25, R_stat tends to zero as k tends to zero, and tends
to infinity as k tends to K. The first limit uses g'(k)~k/4,q->1,y->1/2.
The second uses exp(a) dominating the algebraic growth of y, with g'(K),
q(K)>0. By Section 4, R_stat has exactly one local maximum and then one
local minimum. Let their values be r_hi>r_lo>0.

For r_lo<r<r_hi, the equation R_stat=r has exactly three roots, one on
each strict monotonic arc. By (3.3) these are respectively a local minimum,
a local maximum and a local minimum of the h-optimized logarithmic value.
Only the middle root is an interior local maximum. For r outside this
open interval there is only the corresponding outer minimum, except
that r=r_hi or r=r_lo also gives a horizontal point at a turn. A simple
turn does not change the sign of R_stat-r at the point of contact, so
that horizontal point is not an extremum. Thus there is at most one
interior local maximum for every r>0, and it is present exactly on the
open interval (r_lo,r_hi).

Every stationary root is in the h-interior region by R_stat<C, as already
shown. No root is created or removed by the constrained h boundary. Any
global maximizer other than the two pure classes is interior in k and h:
h faces have B=1,P<1 and lie strictly below the pole for r>0. Hence it
must be this unique middle-arc local maximum.

At its root, (3.3) gives

    f''=q exp(-a)y * partial_k R_stat < 0.

Also F_hh<0. The second derivative f'' is the Schur complement of the h
entry in the Hessian of log F after maximizing h. It is strictly negative,
so the full Hessian of log F is negative definite. At a stationary point,
Hess F=F Hess(log F), which is also negative definite. Analytic dependence
of the interior maximum on (K,r) follows from the implicit-function theorem
or directly from the strict derivative on the middle arc. This also proves
nondegeneracy at every global mixed point and every interior coexistence
point, not merely at the final triple point.

## 8. Exact lower and upper phase thresholds

Fix 0<c<c_star. The frozen no-islands theorem says the pure crossing
r_0(c) has strict mixed improvement. In particular K=2c<13/25 by the
critical-parameter enclosure, so all conclusions of Sections 4-7 apply.

For L<2 define

    U(c,L,h)=[b(2c)-B]/P,
    r_B(c)=min_(L<2,0<=h<=1) U.

The minimum is attained and positive. Indeed B<=b(cL)<b(2c) for L<2,
so U>0. At L=0 it equals r_0. As L tends to 2, uniformly in h,

    U >= [b(2c)-b(cL)] exp(cG(L)) -> infinity.

For the divergence use b'(t)>0 on a compact neighborhood of 2c, so the
first factor is bounded below by a positive multiple of 2-L, while the
exponential grows as exp(C/(2-L)). Thus the minimum lies in a compact
subinterval of L<2 and is strictly positive. The same coercivity is locally
uniform in positive c.

For 0<L<=2 define Q=(B-1)/(1-P), extended by Q=0 at L=0. This extension
is continuous uniformly in h: a centered Bernoulli remainder bound gives
B-1<=k^2 exp(K)h(1-h)/2, while 1-P>=kh exp(-K) for h>0. Thus Q<=Ck
uniformly; at h=0 its numerator is exactly zero. At L=2 the original
definition has P=0 and no singularity. Set

    r_P(c)=max_(0<=L<=2,0<=h<=1) Q.

It is a finite attained maximum. These definitions give exactly

    V(c,r)>b(2c) iff r>r_B(c),
    V(c,r)>1+r   iff r<r_P(c).                   (8.1)

For the first equivalence, use F-b=P(r-U) at L<2 and the fixed pure bulk
point at L=2. For the second, use F-(1+r)=(1-P)(Q-r) for L>0, together
with the pole value at L=0. Therefore strict mixed value occurs exactly
on (r_B,r_P). Since it occurs at r=r_0,

    0<r_B<r_0<r_P<infinity.

At r_B, a U minimizing point cannot have L=0, whose U is r_0, cannot
approach L=2 by coercivity, and cannot have h=0 or h=1: those give
U=r_0/P>r_0 at positive width. Hence a minimizing point is interior
and ties the bulk. Pole has strictly lower value because r_B<r_0.
Section 7 makes the interior point unique and nondegenerate.

At r_P, a Q maximizing point cannot have L=0 or h=0,1, where Q=0,
or L=2, where Q=B-1<=r_0<r_P. It is interior and ties the pole;
bulk has strictly lower value. Again its uniqueness and nondegeneracy
follow from Section 7.

For r<r_B, every point is at most the bulk value by (8.1). Affine
interpolation between r=0 and r=r_B shows equality requires B=b(2c),
which forces the unique pure bulk point. For r>r_P, subtracting the pole
and comparing with r_P shows equality requires P=1, hence L=0. On the
strict interval, any global maximizer is interior and is unique by Section
7. These arguments prove all asserted tie sets and eliminate possible
hidden ties outside the strict mixed interval.

## 9. Analytic coexistence curves throughout 0<c<c_star

The unique interior maximum is analytic wherever it exists on its middle
stationary arc. Let M(c,r) denote its value there. At any such point the
envelope identity gives

    partial_r M=P in (0,1).

At the lower coexistence point, the equation M(c,r)=b(2c) has strictly
positive r derivative P. At the upper coexistence point, M(c,r)=1+r
has strictly negative r derivative P-1. Their unique roots therefore
give locally real analytic coexistence curves by the implicit-function
theorem. The thresholds defined in Section 8 are continuous in c:
r_P is a maximum of the compact continuous Q family with its locally
uniform extension; r_B is a minimum with locally uniform coercivity.
Thus the local analytic roots are precisely those thresholds for nearby
c, rather than unrelated stationary equalities. Uniqueness patches them
into the two analytic functions on the whole interval (0,c_star).

Similarly, the unique global interior maximum patches into one analytic
function z(c,r) on the entire open mixed region. Across either coexistence
curve it has a local analytic continuation as a possible nonglobal local
maximum. For fixed c, its gap from the bulk increases strictly with r,
and its gap from the pole decreases strictly with r. Consequently there
are exactly the two coexistence boundaries found above, with no further
switches or mixed/mixed coexistence points.

At the last boundary, CRITICAL_UNIQUENESS_CERTIFICATE supplies the unique
nondegenerate triple point and the analytic local continuation of both
curves. It proves their linear closing explicitly. For c>=c_star the
previous no-islands and critical uniqueness theorems supply the pure
argmax statements. This completes the classification for every c>0,r>=0.

## 10. Original APPT spectra and the precise completed scope

For each fixed limiting pair (c,r) in the physical linear-order window,
the credited value theorem and S identify actual APPT nearoptimizers by
distance to the complete scalar argmax, J->0, and vanishing actual peak
loss. Since the scalar argmax is now classified, the possible limiting
empirical body laws are also classified:

    pole: delta_0;
    bulk: (1-h_b)delta_{-2h_b}+h_b delta_{2(1-h_b)};
    mixed: (1-h)delta_{-Lh}+h delta_{L(1-h)}
           at the unique interior point z(c,r).

The appropriate one or two of these laws occur in the regions and on
the coexistence curves listed in Section 2; exactly three occur at the
triple point. Every scalar argmax is attained by actual APPT sequences
through the credited construction. At a tie, nearoptimal sequences may
alternate between the corresponding laws. These are statements about
the original complex matrices APPT under every global unitary, with
all spread and actual peak-loss conditions preserved. They are not
assertions only about the scalar candidate model.

For dimension-dependent parameters approaching a coexistence point,
selection of one phase requires error control relative to the vanishing
gap; no unconditional one-sided selection is claimed. The theorem concerns
this linear-order finite-r window. Other order windows, exact finite
dimensions, effective thresholds, and the entire entropy problem are
not closed by it. The original Lean audit scope is unchanged.

## Reproduction and review status

Copy the frozen files listed in GLOBAL_MIXED_V1_MANIFEST.json to a private
scratch directory and run replay_global_turn_certificate.py there. It uses
only the Python standard library and the bound integer interval source.
The generator records a fresh UTC, so do not regenerate the original
frozen certificate in place. The optional SymPy algebra control and
floating-point discovery files are not proof substitutes.

The author replay must recompute all 74 exact bounds, all six complete
partitions and all cap exclusions. Ordinary independent review must also
read the analytic derivative reduction, removable charts, tail estimates,
constrained h boundary, Hessian argument, threshold attainment, all ties,
and original APPT transfer. Until that happens, this complete author-level
phase classification remains author-only and must not be indexed as a
reviewed or Lean-verified result.
