# Bounded cluster avoidance for uncountable selector families

7 October 2026. Research proof draft. No publication or novelty claim is made.

## Result and relation to the existing entries

This draft proves an uncountable-family extension of the routing argument in
mxym/math entries 004 and 006. Instead of making one candidate at a scale hit a
small open set, it makes an entire bounded finite cluster hit. Every pointwise
selector from those clusters is then excluded by the same large closed set.
The proof does not enumerate selectors or approximate them by a countable
family of leading profiles.

Entry 003 concerns a different invariant: upper box dimension zero and Assouad
dimension two of a Banach-space nonembedding obstruction. Its covering proof
suggests keeping branching cardinality separate from scale count, but its
nonembedding theorem is not an analytic dependency here. In the example below
the *space of profiles* has Assouad and upper box dimension one, whereas every
individual null configuration has upper box dimension zero. Neither of these
statements identifies those dimensions with the logarithmic upper Banach
density used in 004. The critical-covering refinement of 003 is recorded
separately in CRITICAL_COVERING_GAUGE.md.

### Theorem A

Let S be a subset of the positive integers with d*(S)>0. For every j in S let
F_j be a nonempty finite set satisfying

  F_j subset [2^(-j-1),2^(-j)],       |F_j| <= K,

where K is a fixed positive integer. Let (omega_r) be a nonempty countable
family of nondecreasing finite null moduli, meaning omega_r(a) tends to zero as
a tends to zero.

For every 0<epsilon<1 there is a closed nowhere-dense one-periodic set E such
that |E intersect [x,x+1]|>1-epsilon for every real x and the following holds.
For every r, y in R, c nonzero, M finite and nonnegative, and every collection
of errors e_{j,a} satisfying

  |e_{j,a}| <= M a omega_r(a)

on all sufficiently late clusters, there are arbitrarily large j in S for
which

  {y+c a+e_{j,a}: a in F_j} subset R\E.                 (A.1)

Consequently, every pointwise selector a_j in F_j and every perturbed sequence
v_j=y+c a_j+e_j with |e_j|<=M a_j omega_r(a_j) has infinitely many distinct
values outside E on every tail.

The same E works for any prescribed countable family of such cluster systems;
each system may have its own finite bound K and positive density.

The closed annulus convention is harmless. It permits the useful example
F_j={2^(-j-1),(3/2)2^(-j-1)} directly. There is no assertion for unbounded
cluster cardinalities or for a continuous interval of candidates at each
scale. The null moduli remain prescribed and countable.

## Density template placement

We recall and prove precisely the input from 004/006. Put
F_S(L)=sup_m |S intersect {m+1,...,m+L}| and delta=d*(S).
The limit F_S(L)/L exists by subadditivity and equals its infimum. For every
xi>0 there is a constant C_xi such that every integer interval I obeys

  |S intersect I| <= (delta+xi)|I|+C_xi.                (1)

Indeed choose L0 with F_S(L0)<=(delta+xi)L0 and partition I into blocks of
length L0 and a remainder; C_xi=L0 suffices. Every tail of S has the same upper
Banach density, and every length T has a maximizing interval containing at
least delta T points, arbitrarily far out. The supremum is attained since the
possible counts are integers in a finite set.

Fix 0<eta<delta. Suppose an interval template has total span T_L<=C0 L and
contains finitely many windows, each of length at least L. Put the template
on a maximizing interval J of length T_L beyond any requested initial index.
For every window W, its complement in J consists of at most two intervals.
Applying (1) there gives

  |S intersect W| >= delta|W|-xi C0 L-2C_xi.

Choose xi C0<(delta-eta)/2 and then L sufficiently large. Every window
contains at least eta|W| selected indices. The threshold for L is independent
of the requested initial index. This independence is needed for buffering.

One parity of S has positive upper Banach density; otherwise subadditivity
would force d*(S)=0. Replace S by that parity. Blocking these clusters is
enough for Theorem A, and discarding any finite initial segment is harmless.
Hereafter delta and eta refer to this chosen parity.

## Finite routing with entire clusters

Fix 0<p<1/12 and define

  theta=(p/2)^K.

Choose an integer M>=2 with theta eta(M-1)>4. Choose a depth d with
(1-2^(1-M))^d<p. Let Q be the number of edges in a complete ordered M-ary
rooted tree of depth d. Choose an integer gap g>=1 with Q 2^(3-g)<p.

Order edges in preorder. Edges leaving a vertex of height h have common
window length ell_h. Put g unused integer indices between consecutive
windows. For a base length L>=g set

  ell_1=L,              sigma_1=M L+(M-1)g,
  ell_h=g+sigma_(h-1),
  sigma_h=M(ell_h+g+sigma_(h-1))+(M-1)g   (h>=2).

The total span T=sigma_d is at most C0 L for fixed M,d,g. If an edge window
is [u_e,v_e] and v_e* is the final endpoint of it and its child subtree, then
v_e*-u_e+1<=2 ell_h. Apply the density template lemma to place it beyond
any initial index, with at least eta ell_h selected indices per window.
Require the initial index to be at least four.

Use one-periodic nested grids with N_b=2^(b+3) cells and key
J_b(z)=floor(N_b {z}). For every nondefault edge e=(P,i), i<M, assign an
independent fair-bit selector table at grid v_e. The Mth child is default.
Every leaf has an independent Bernoulli-p terminal table at its incoming
edge's grid. All entries in all tables are independent.

Route z to the first nondefault child whose addressed selector is one,
or to the default when all are zero, and continue to a leaf. Let B be the
set of z whose addressed terminal bit is one. Conditioning on all selectors
shows E density(B)=p. Every outcome is constant on a finest periodic grid
with N=2^(u+T+2), where u is the template start.

A center x is stable if for each predecessor endpoint b' and next window
start u'=b'+g+1, the interval (x,x+2^(1-u')] contains no point of the grid
N_b'^(-1) Z. The unstable centers have density at most Q 2^(3-g)<p.
For a stable x and any candidate a in F_j with j in a window, every
x+t a, 1<=t<=2, agrees with x at all grids of earlier edges. This follows
from t a<=2^(1-u_e), the stability condition and nesting.

Candidates from *different* selected indices in one window have distinct
keys at that window's grid, and avoid the center key. To check this, if
j<k and k>=j+2, then

  min F_j-max F_k >= 2^(-j-1)-2^(-k)
                    >= 2^(-j-2) >= 2^(-v_e-2),

which is twice the cell width. Also every candidate is at distance at
least 2^(-v_e-1) from the center. All displacements lie in an interval of
length at most 1/8, so circular wraparound creates no collision. The
separation persists at every finer grid. Candidates *within* one cluster
may share keys, and we allow this explicitly.

Fix a stable x and expose its addressed selector entry in every selector
table, but expose no terminal entries. This determines x's route. Its
probability of having no default is (1-2^(1-M))^d<p. On an exposure atom
whose first default is at U of height h, test every selected j in each
of U's first M-1 outgoing windows. For an edge e_i=(U,i), route each
z=x+t a locally from its child U_i. If every own-edge selector at that
cluster is one and every resulting local terminal entry is one, the
entire cluster x+t F_j belongs to B. Earlier routing decisions agree
with x; therefore all its candidates really enter U_i.

### The new probability estimate

There are m>=eta(M-1)ell_h tested clusters. For each cluster, let A_j be
the event that all its own-edge selector entries are one. It consults at
most K distinct entries, so P(A_j | center exposure)>=2^(-K). Different
clusters consult disjoint own-edge entries, by the separation just proved
(or use different tables). Thus their A_j events are independent under the
center exposure.

Now condition on *all* selectors. Let d_j be the number of distinct local
terminal addresses within cluster j; 1<=d_j<=K. Addresses belonging to
different clusters are distinct: different children have disjoint subtrees;
different leaves have different tables; at the same leaf, different
index-clusters retain distinct keys at the finer grid. Conditional on the
selectors, the terminal-success events for different clusters are therefore
independent, and the success probability of cluster j on A_j is p^(d_j).
The conditional probability that all tested clusters fail is

  product_j [1-1_(A_j) p^(d_j)]
    <= product_j [1-1_(A_j) p^K].

Averaging over selectors and using the independent A_j events gives

  P(all clusters fail | center exposure)
      <= (1-(p/2)^K)^m <= exp(-theta m).               (2)

This estimate is an inequality, not the singleton engine's exact identity.
Collisions within a cluster can only improve its success probability.
Shared auxiliary selectors do not invalidate the calculation: they were
conditioned on first, and d_j was bounded before averaging.

### Uniformity over every normalized dilation

A candidate in a tested cluster on edge e_i consults only grids up to v_e_i*.
As t traverses [1,2], its entire local outcome changes at at most
1+2^(2 ell_h+3) deterministic boundary values. There are at most
K(M-1)ell_h candidates. Represent every boundary, both endpoints, and
one point of every intervening open interval. At most

  D_(K,M)(ell)=4+2K(M-1)ell(1+2^(2ell+3))

representatives suffice. The whole test vector is constant between the
represented boundaries for every table outcome. Thus the probability
that some t has no entire successful cluster is at most

  D_(K,M)(ell) exp[-theta eta(M-1)ell].               (3)

Since theta eta(M-1)>4>2 log 2, choose L large enough that (3) is less
than p for every integer ell>=L. The parameters M,d,g,L,T are all chosen
before the actual template location. Combining the no-default cost with
(3) gives probability less than 2p at every stable center. Boundaries are
represented individually; failures supported only at a boundary are retained.

## Robust normalized blocker

Given a null modulus omega, let T be the finite span just constructed. For
a possible start u put

  eta_u=omega(2^(-u))+2^(-u),       r_u=2^(-u) eta_u>0.

Choose a lower bound on u so late that

  4N r_u = 2^(T+4) eta_u < p,
  N=2^(u+T+2).

This holds at every later start. The density-template lemma still supplies
a filled template there. Every test candidate a<=2^(-u) has
|e_{j,a}|<=a omega(a)<=r_u.

For each random B let B1=B+(-r_u,r_u) and B2=B+(-2r_u,2r_u) on the circle.
If B has N grid cells, enlarging them gives

  density(B2)<=density(B)+4N r_u,

so E density(B2)<2p. Define the exceptional-center set

  R={x: there is t in [1,2] such that for every tested j,
         at least one candidate in x+t F_j lies outside B1}.

It is closed and periodic: the failure condition is a finite intersection
of finite unions of closed conditions on the compact rectangle. Its
projection onto the circle is closed. By the finite estimate and unstable
center cost, E density(R)<=3p. Choose a table outcome with

  density(B2)+density(R)<5p.

By outer regularity choose an open periodic V containing R with
 density(V)<density(R)+p. Put H=B2 union V; density(H)<6p.

If x is not in R, one tested cluster lies entirely in B1. Any collection
of errors of size at most r_u puts the entire cluster in B2: the first
buffer gives a strict margin and the second absorbs endpoint equality.
If x is in R, it lies in V. As j tends to infinity in S, every candidate
in F_j and every allowed error tends uniformly to zero. Therefore all
sufficiently late perturbed clusters lie in V. This repairs every center,
not merely almost every center.

We have proved: for every x, every t in [1,2], and every allowed independent
error array, at least one entire cluster x+tF_j+errors lies in H. The
statement may be applied to any specified tail and any integer dilation
of the cluster system.

## All coefficients and infinitely many hits

For every r, integer k, integer q>=1 and tail cutoff h, apply the normalized
blocker to clusters 2^k F_j for j>=h, deleting any finitely many nonpositive
annular indices. Their annular indices are shifted by -k and retain positive
upper Banach density. Use the transformed null modulus

  Omega_(r,k,q)(b)=q 2^(-k) omega_r(2^(-k)b).

Choose positive budgets p_(r,k,q,h)<1/12 with
12 sum_(r,k,q,h) p_(r,k,q,h)<epsilon. Let U be the union of all blockers
and their reflections, and E=R\U. This is closed and one-periodic, and its
complement has density less than epsilon.

For c>0 write c=2^k t with 1<=t<=2, and choose q>=M. At b=2^k a the error
bound M a omega_r(a) is at most b Omega_(r,k,q)(b). For every sufficiently
late h, the component with that tail supplies an entire cluster as in (A.1).
Thus the good cluster indices are unbounded. For c<0 use the reflected
blocker and negate the errors.

Every selected v_j obeys, on sufficiently late clusters,

  (|c|/2)a_j <= |v_j-y| <= (3|c|/2)a_j.

Consequently hit values tend to y but never equal it there, which guarantees
infinitely many distinct hit values on every tail. Countably many cluster
systems can be added as an extra index to the summable budget.

Finally E has empty interior. Choose once and for all one selector a_j
from a bounded tail of the first cluster system. If an interval lay in E,
a sufficiently small translated affine copy of this bounded selector would
fit in that interval. The already proved assertion with zero errors forbids
this. A closed set with empty interior is nowhere dense. Theorem A is proved.

## An explicit uncountable log-bi-Lipschitz family

Let A={2^(-n):n>=1}, and for every binary sequence sigma with
sigma_n in {1,3/2}, prescribe

  phi_sigma(2^(-n))=sigma_n 2^(-n).

Define Psi_sigma on [1,infinity) by linear interpolation of
Psi_sigma(n)=n-log_2(sigma_n), and set
phi_sigma(a)=2^(-Psi_sigma(-log_2 a)) for 0<a<=1/2, with phi_sigma(0)=0.
Every segment slope belongs to

  [1-log_2(3/2), 1+log_2(3/2)].

Both endpoints are positive. Hence every phi_sigma is a strictly increasing
log-bi-Lipschitz null profile with these common constants. Theorem A applied
to F_(n-1)={2^(-n),(3/2)2^(-n)}, n>=2, produces one E excluding every
image y+c phi_sigma(A), simultaneously for every sigma, every c nonzero,
and every y. It also permits the displayed prescribed null perturbations.

This is an uncountable upgrade: sigma may change independently at every
scale. A selector with infinitely many changes has no fixed constant
multiple of the identity as its leading profile. More generally, a
countable family of arbitrary fixed profiles cannot cover all these
selectors by relative o(1) approximation, even allowing separate scalar
coefficients. If two selectors were asymptotic to scalar multiples of the
same profile, their quotient on A would converge. That quotient belongs to
{2/3,1,3/2}, so it is eventually constant. Apart from the two constant-tail
classes, this means the two selectors eventually agree. Each eventual-
equality class is countable, while there are continuum many such classes.
This is why countable union bookkeeping in 006 alone does not supply the
new simultaneous quantifiers.

Equip the binary parameter space with d(sigma,tau)=2^(-m), where m is the
first differing index. It has Assouad dimension and upper box dimension
exactly one, by counting binary cylinders. Under the uniform function norm
on [0,1/2], the map sigma -> phi_sigma is bi-Lipschitz:

  (1/2)2^(-m) <= ||phi_sigma-phi_tau||_infinity <= 3 2^(-m).

The lower bound is the difference at a=2^(-m). Before z=m-1 the profiles
agree; afterwards both have size at most 3 2^(-m), which gives the upper
bound. Thus the profile family itself has both dimensions one. Its
individual image sequences have upper box dimension zero, since they
decrease geometrically. The density of their logarithmic bins is positive.
Those are three separate statements about three separate objects.

These profiles are also uniformly bi-Lipschitz in the ordinary variable
away from zero, and extend continuously to zero; on an interpolation
segment their derivatives are the logarithmic slope times phi_sigma(a)/a,
which lies in [1,3/2]. This does not assert all such profiles are C1 at zero.
For non-eventually-constant sigma, phi_sigma(2^(-n))/2^(-n) does not
converge, so differentiability at zero already fails.

The theorem therefore does not contradict the known positive embedding
results for arbitrary bi-Lipschitz maps or the C1 endpoint in entry 006.
It excludes this explicit finite-alphabet family, not all maps with the
same distortion constants, all real power exponents, or flat germs.

## Exact finite certificates

A certificate lists finitely many rational clusters, one nonnegative
rational error radius r_a per candidate, finitely many rational OPEN
intervals repeated with period one, and a rational density budget. It asserts

  for every x in [0,1] and t in [1,2], some listed cluster F satisfies
  [x+t a-r_a, x+t a+r_a] subset H for every a in F.       (C.1)

Failure means choosing one failed candidate from every cluster, and then a
closed complementary gap [l,u] reachable by an allowed error. For each
such finite choice the constraints are

  0<=x<=1,  1<=t<=2,
  l-r_a<=x+t a<=u+r_a.

Exact half-plane clipping in two rational variables decides feasibility.
Segments and singletons are retained, so endpoint-only failures remain.
If feasible, the checker chooses a rational x,t and independently verifies
one legal escaping error in every cluster. If no choice is feasible, (C.1)
holds. The density is computed by merging genuinely overlapping open
intervals; merely touching intervals retain a singleton gap.

The implementation check_cluster_cover.py uses Fraction arithmetic only.
Seven regression cases pass. The supplied computed certificate is

  F_n={2^(-n),(3/2)2^(-n)}, n=1,2,3,4;
  r_a=a/100;
  H=(0,4/5)+Z;     density budget 4/5.

It returns valid after nine feasible-polygon states. The first three
clusters alone fail, and an exact counterexample is x=7/15, t=1591/900,
with legal escaping candidates 3/4, 1/4 and 3/16. The four-cluster
certificate is nontrivial and tests the stronger all-candidates assertion.
It is not a computed small-density witness for every epsilon.

For computably listed rational clusters and computable rational radii
with r_a/a uniformly tending to zero by cluster index, there is also a
terminating exact search for normalized certificates of any rational
positive density budget. The robust normalized proof provides an open H
of strictly smaller density. Entire closed uncertainty intervals are
contained in H for a successful cluster, and this is an open condition
on x,t. Compactness supplies a finite subcover by successful clusters.
Shrink to finitely many rational open intervals inside H still covering
those compact uncertainty intervals, and choose rational endpoints so the
strict density budget survives. Enumerate finite rational interval lists
and cluster prefixes and run the exact verifier. Existence proves the
search terminates. No feasible runtime or complexity bound is claimed.

## Primary source comparison and scope

1. OpenAI, The geometric case of the Erdos similarity conjecture, family 084,
   pinned commit adc7f1241b42e322a6451854ab7e4b4c146bf78a. Its theorem is
   for each fixed geometric ratio. Sections 04-routing and 05-scales are the
   source of center exposure, conditioning on all selectors, finite
   dilation entropy, and exceptional-center repair. The bounded-cluster
   probability estimate (2) is the added step here.
   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-geometric-case-of-the-Erdos-similarity-conjecture-October-5-2026/build/sections/04-routing.tex
   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-geometric-case-of-the-Erdos-similarity-conjecture-October-5-2026/build/sections/05-scales.tex
2. mxym/math entry 004 v1.1 supplies the positive-logarithmic-upper-Banach-
   density template extension; entry 006 v1 supplies translation-uniform
   placement and the two-buffer error argument; entry 006 v2 treats a
   prescribed countable family of log-bi-Lipschitz profiles. The sources
   read for this draft are the exact local release statements, including
   006 v2's explicit uncountable-family disclaimer.
3. Feng, Lai, Xiong, Erdos similarity problem via bi-Lipschitz embedding,
   arXiv:2312.01319v1, Theorem 1.1: a geometrically decaying null sequence
   has a bi-Lipschitz image in every positive-measure set, even with
   derivative one at zero. This is consistent with the restricted family
   here, and warns against claiming all bi-Lipschitz or all C1 images.
   https://arxiv.org/html/2312.01319v1
4. Bellissard and Julien, Bi-Lipschitz Embedding of Ultrametric Cantor Sets
   into Euclidean Spaces, arXiv:1202.4330v2, gives geometric context for
   counting weighted binary-tree cylinders and finite Assouad dimension.
   The elementary dimension calculation above is proved here directly.
   https://arxiv.org/abs/1202.4330v2

This is a written proof draft with exact finite regression checks, not
independent peer review, formal verification, or a literature-priority
assertion. The main argument has no numerical optimization dependency.

## Extension through the countable log-bi-Lipschitz profiles of 006 v2

The theorem also applies to clusters in a fixed-width logarithmic annulus.
More precisely, replace its annulus condition by

  F_j subset [lambda 2^(-j),Lambda 2^(-j)],
  0<lambda<=Lambda<infinity,

with lambda and Lambda fixed for the cluster system. First divide all
candidates by Lambda. Choose an integer q>=1 with 2^(-q)<=lambda/Lambda.
One residue class of S modulo q+1 has positive upper Banach density; keep
it. Use grids N_b=2^(b+q+3), rather than 2^(b+3). Distinct selected index
clusters are separated by at least 2^(-j-q-1); this is at least four grid
cells at an edge endpoint b>=j, and each candidate avoids the center key.
All other arguments are unchanged with the following explicit replacements:

  unstable density bound: Q 2^(q+3-g);
  entropy bound:
    4+2K(M-1)ell(1+2^(2ell+q+3));
  finest grid: N=2^(u+T+q+2);
  buffer cost: 4Nr_u=2^(T+q+4)eta_u.

Choose g so Q 2^(q+3-g)<p. The entropy exponential rate is still 2 log 2,
so theta eta(M-1)>4 suffices. Positive lambda and finite q keep all choices
finite; no dependence on the eventual translation or tail location is
introduced. The preliminary division by Lambda is absorbed into the free
coefficient and into the pulled-back null modulus. This proves the wide-
annulus version of Theorem A with exactly the same conclusion.

### Corollary B

Let (A_l) be a nonempty countable family of configurations with positive
logarithmic upper Banach density. Let (phi_r) be a prescribed nonempty
countable family of log-bi-Lipschitz null profiles as in 006 v2. Let (D_v)
be a nonempty countable family of finite nonempty subsets of (0,infinity),
and let (omega_w) be a prescribed nonempty countable family of null moduli.
For every epsilon>0 one closed nowhere-dense one-periodic set E of measure
more than 1-epsilon in every unit interval has the following property.

For every choice of l,r,v,w, y in R, c nonzero and M finite, every function
f on a sufficiently small tail of A_l satisfying

  f(a)=y+c d(a) phi_r(a)+e(a),
  d(a) in D_v,
  |e(a)|<=M phi_r(a) omega_w(a),                       (B.1)

has infinitely many distinct values outside E on every sufficiently small
tail. The multiplier d(a) may switch arbitrarily at every input scale;
no regularity or enumeration of these switching functions is assumed.

Proof. By 006 v2 Lemma 2.1, B=phi_r(A_l) has positive logarithmic upper
Banach density. Choose one b_j=phi_r(a_j) from every occupied dyadic bin,
then use the cluster D_v b_j. Its cardinality is at most |D_v|, and it lies
in [min(D_v)2^(-j-1),max(D_v)2^(-j)], so the wide-annulus theorem applies.
Pull omega_w back to the b-coordinate by
Omega(b)=omega_w(phi_r^(-1)(b)), extending constantly beyond a small
interval when necessary. It is a null modulus. Put d0=min(D_v)>0 and define the candidate-coordinate null modulus
Omega_new(u)=Omega(u/d0). Since d>=d0, an error bounded by M b Omega(b)
is at most (M/d0)(d b)Omega_new(d b), exactly the per-candidate bound
required by the cluster theorem. Prescribe this same error at every
candidate d b in a cluster; whole-cluster success then covers the actual
choice d(a_j).

The countable indices l,r,v,w are absorbed into the summable density budget.
Unbounded successful cluster indices imply b_j->0, hence a_j->0 because
phi_r is increasing and tends to zero. On sufficiently small inputs,
|f(a)-y| is between positive constant multiples of phi_r(a), since D_v is
finite and bounded away from zero and omega_w(a)->0. Thus the outside hit
values tend to y without equalling y, giving infinitely many distinct
values on every tail. This proves the corollary.

Taking D={1} recovers the relevant profile statement of 006. Taking
D={1,3/2} permits genuinely arbitrary switching with no fixed leading
profile and gives the stronger uncountable simultaneous conclusion.
Countability still applies to the prescribed profiles, alphabets and error
moduli. No simultaneous claim for all positive real exponents follows.

Additional finite check: using the same candidate formula and relative error
radius a/100, the first six clusters certify H=(0,3/4)+Z, with exact density
3/4, in fourteen polygon states. This is saved separately as
 toy_cluster_certificate_3_4.json and toy_cluster_result_3_4.json. This smaller
finite example also remains a normalized regression certificate, not a
computed certificate for the arbitrarily-small-density theorem.
