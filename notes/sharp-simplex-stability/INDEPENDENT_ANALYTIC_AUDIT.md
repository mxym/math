# Independent analytic audit: sharp simplex stability

7 October 2026. Public editorial version of the completed analytic audit.

Verdict: PASS. No mathematical correction was required. The audit covers
all convex bodies in every fixed integer dimension d >= 3, every initially
prescribed maximum-volume inscribed simplex and its original centroid,
the explicit constants, local threshold, zero-defect and global cases,
and the matching one-vertex truncation obstruction. The exponent 1/(d-1)
is sharp in this stated theorem class.

This is an independent analytic model audit, supported by separately
implemented finite checks. It is not human peer review or proof-assistant
formalization and establishes no priority or literature-wide novelty claim.
The public proof changes only author, review status and source provenance.
Its mathematical sections are byte-for-byte unchanged from the audited proof.

The historical audit report SHA-256 is
c4ccaacb5b3ce313795764ba80cfb28f8fe5c2513186edb00235a34a1ad38d55.
The received proof SHA-256 is
afa4e8494e48a7245bcd4de0addf532a433b49f8ae286da33471a9cbeb65b5ea.
These are historical provenance pins, not hashes of the edited public files.
The current hashes are in MANIFEST.json.

## Complete analytic chain

### 1. Normalization and cone-law identity

Fixing S first is essential. Its affine normalization to a regular simplex
Delta of inradius one and centroid zero preserves E and a. Maximum volume
implies |alpha_i(x)| <= 1 for every barycentric coordinate of every x in K,
by replacing that vertex. Thus |x| <= d(d+1)=R_0, and
B <= Delta <= K <= R_0 B is valid.

The cone-law pushforward is centered and supported on the polar boundary
inside the unit ball. Its Cauchy identity has the necessary factor 2:

E|u.X| = 2 pi_K(u)/(d |K|).

The lower projected cube gives exactly
(2/d)^(d-1)/[d(2R_0)^d] = 2b. Centering yields the stated one-sided
dispersion and the covariance lower bound. The pinned v3 determinant
representation gives a=B/[(d+1)A], hence
D=B-A=(d+1)A e <= (d+1)e. A is positive by dispersion and at most one by
Hadamard. Its arbitrary-body passage uses a common compact support and
weak continuity, so no strict equality-classification statement is being
inferred from approximation.

### 2. Integrated witnesses and nonatomic anchor selection

The cancellation identity remains valid on singular base tuples. Every
two-sample witness has conditional mean at most twice the minimum of the
two sign expectations, which gives the integrated bound by D. In each
anchor-witness summand, the base and the tested points really are d+2
independent samples before conditioning.

The affine determinant second moment is (d+1)! det Sigma; V <= 2^d gives
the displayed event probability q_0. H is continuous on the compact
support product. Its minimum on the closed positive-probability event
attains a value at most the conditional average. This step does not
assign mass to a chosen point and is valid for nonatomic laws.

The first barycentric witness is exactly
V min(1,(-alpha_i)_+). For positive alpha_i and alpha_j, the pair witness
is V min(alpha_i,alpha_j), and other signs only add nonnegative terms.
Choosing the largest positive coordinate is measurable with the stated
tie rule. The diameter estimate and coefficient truncation give
h <= 2 L_0 Phi <= Q D. The unsimplified coefficient is exactly
(d+1)(d+2)8^d b^(-4d). The Lipschitz positive-part argument then gives
b B <= T when QD <= b. There is no lost square root here.

### 3. The new weight correction and Cauchy projection step

The polar simplex P=T^polar encloses K. Its vertices q_i satisfy
q_i.w_j=1 for j != i. With positive zero-barycentric weights lambda_i,
q_i.w_i=1-1/lambda_i. Therefore the displayed affine formula
alpha_i(x)=lambda_i(1-q_i.x) holds on the whole ambient space, not just
inside T.

The assigned mean c satisfies |c| <= h by centering of the original law.
Applying the affine formula to c gives the exact identity
p_i-lambda_i=-lambda_i q_i.c. Since sum lambda_i=1 and |q_i| <= M,
sum |p_i-lambda_i| <= M h. There is no assumption of uniform lambda_i
or positive original mass at w_i. The cone law of P has exactly these
lambda_i weights, because it is centered on the d+1 polar facet images.

The absolute directional linear function is one-Lipschitz on the support
and bounded by one on the anchors. The original-to-assigned-law error is
at most h, and the assigned-to-P-law error is at most M h. Cauchy's factor
d/2 then gives the normalized-projections equation, with the stated coefficient. This is an
actual uniform comparison of normalized brightness in every direction.

### 4. Restoring scale

Normalized projection comparison alone would not suffice. The proof
separately uses z=E[h_P(X)-1], which is nonnegative because K <= P and
h_K(X)=1 on the polar support. Its Lipschitz estimate is z <= M h <= 1.
First variation identifies z with V(K[d-1],P)/|K|-1. Differentiating
Brunn--Minkowski gives the correct direction of Minkowski's first
inequality, and therefore |P|/|K| <= (1+z)^d.

The elementary bound (1+z)^d-1 <= d 2^(d-1) z is valid on [0,1]. Also
pi_P/|P| <= d/2, because the cone law of P lies in the unit ball. The
exact decomposition on lines 332--338 gives a uniform absolute deficit
at most J h. No sign is assumed for the normalized difference;
nonnegativity of the absolute projection deficit follows from K <= P.
The displayed J equals the resulting coefficient after the valid bound
|K| <= (2R_0)^d.

### 5. Projected cap geometry

For a farthest q in P and its metric projection k on K, n=(q-k)/s is a
supporting normal and n.q-h_K(n)=s. Choosing a projection direction u
perpendicular to n preserves that gap exactly in u-perp. The projected
bodies still contain the unit ball and have outer radius M.

The ball (1-tau) qbar + tau B^(d-1), with tau=s/[2(M+1)], lies inside
the projected P by convexity. Since n.q <= M, its lowest n-coordinate
is at least h_Kbar(n)+s/2. Thus it is wholly outside the projected K.
The cube of side 2 tau/(d-1) fits in that ball, and its volume proves
the claimed constant L=(d-1)(M+1). This really is a cap of dimension
d-1. No simplex assumption, smoothness, or inverse Minkowski theorem
enters this cap lemma.

Nesting is crucial: the argument is not a general inverse theorem for
brightness of arbitrary nonnested bodies. Combining it with the preceding
enclosing-simplex comparison legitimately gives s <= L(Jh)^(1/(d-1)).

### 6. Every originally chosen maximum simplex and constants

The small-error gate gives s <= 1/(8Md), h <= b, and M h <= 1.
The support-function argument yields (1-s)P <= K, so maximality of the
original Delta gives |Delta|/|P| >= 1-ds. For the column-stochastic
barycentric matrix, Hadamard forces one entry at least 1-2delta in each
column. A collision of two dominant rows has probability at least
(1-2delta)^2, giving the permanent contradiction for delta=ds <= 1/8.

The matched-vertex error is at most 4Md s. It controls P by Delta plus
that ball, and B <= Delta converts it to the required dilation about
the original centroid. The resulting A_d^sharp is exactly the stated
one. Its threshold value is at most 1/2. The global branch is covered
by (R_0-1)e_sharp^(-1/(d-1)), since K <= R_0 Delta. The D=0 case is
handled directly, including the matrix argument with delta=0.

Every constant gate is logically used under its stated hypotheses.
The local and global conclusions hold in all integer dimensions d >= 3;
finite dimension checks supplement, rather than prove, that analytic fact.

### 7. Sharpness and the scalar obstruction

For the truncated coordinate simplex K_t, a nondegenerate vertex simplex
must use every coordinate ray and double exactly one. Its determinant is
(1-t)t^k. Separate affine linearity and the triangle inequality extend
the vertex bound to arbitrary inscribed vertices. Thus the displayed S_t
is globally maximum.

Its barycentric minimum is exactly -t at t e_2, yielding
E(K_t,S_t)=(d+1)t about its own centroid. The area-vector/lifted-minor
formula gives the displayed defect with leading coefficient
d(d-1)/(d+1)^2 times t^(d-1). One such maximum S_t suffices to disprove
any larger exponent for a bound required for every maximum simplex.

The scalar mixed-volume deficit is t^d/(1-t^d), whereas the Hausdorff
gap is t/sqrt(d). A fixed translation and scale can provide common
inner and outer balls for all sufficiently small t, so this remains
an obstruction to powers greater than 1/d in the scalar-only route.
The projection in direction (e_1-e_2)/sqrt(2) has deficit
t^(d-1)/[sqrt(2)(d-1)!], exactly as stated. The new proof therefore uses
information the scalar route had discarded.

## Executed checks and counterexample search

The supplied standard-library checker and inherited truncation checker
were inspected and replayed normally and with Python -O. Every condition
uses an explicit runtime check; optimization does not remove checks.
Both pairs of certificates and logs agree byte-for-byte.

Supplied endpoint counts reproduced:

- 8 constant dimensions
- 380 barycentric affine-basis values
- 1,560 weight-correction values; 240 weight-bound cases
- 24 centered truncation cone laws; 204 projection directions
- 6 finite centered laws, including interior atoms
- 12,887 integrated-witness sample tuples; 222 barycentric witness values
- 120 every-maximum stochastic-matrix cases

The endpoint certificate SHA-256 is
cac4575e072bc9be04ed45c44f928e44711a5bd45dec86c9186611562c7e613f.
The inherited truncation certificate reproduces the source hash pinned in
PROVENANCE.json.
Its grid covers dimensions 2--9 for geometry and 2--6 for vertex-simplex
enumeration, with 5,385 subsets and five rational cut parameters.

I also replayed the independently implemented permutation-determinant
checker from the published 1/d proof, in a separate directory and both
Python modes. It passes 155 barycentric points, 585 first identities,
830 complete pair identities, 371 cancellation bases including 313
horizontally singular bases, and 2,535 lifted-moment tuples. It imports
no producer code.

A new independent checker imports no received code. It exercises 120
skew, translated rational anchor simplexes in dimensions 2--6, including
nonuniform positive zero-barycentric weights. It also constructs 35
rational single/multiple-cut 3D polytopes by halfspace intersection. Their
face area vectors, cone laws, volumes, and directional Cauchy values are
computed independently. Exact rational KKT solutions give their metric
projections and Hausdorff gaps; gap-preserving directions test the cap
inequality. No counterexample was found.

New independent counts:

- 3,240 affine-basis identities
- 6,000 nonuniform correction identities; 1,200 norm-bound cases
- 7,200 centered brightness comparisons
- 280 polytope projection cases
- 35 scale-control cases and 35 projected-cap cases

The normal and -O runs produce identical log and certificate bytes.
Independent checker SHA-256:
7894912020935c7b7dc64caf1292d8edfc8d0f00f4330b3310e7afde0c8f1117.
Independent certificate SHA-256:
bf32f40af6ea1467723d90e12777df143beb0657954fd37af233796a5887d4a0.

The face cyclic-ordering step uses atan2 on approximate coordinates;
the resulting vertices, area vectors, volumes, identities, and all
inequality comparisons use exact Fraction arithmetic. This limitation is
explicit in the checker and is not represented as formal certification.
Neither the supplied checks nor these tests enumerate all convex bodies,
all laws, or all stochastic matrices. The written analytic argument
supplies those quantifiers.


## Public package reproduction

The supplied, independent and inherited checkers are included. The new
independent checker and its certificate retain the audited bytes and hashes.
The prior independent checker is included under check_prior_independent.py.
The public verification script rebuilds the proof and replays each checker
normally and with Python -O in separate writable replay directories.
All mathematical source dependencies are readable local files. A configured
TeX installation is required; build.sh includes a writable-cache fallback
for installed Debian TeX trees. No source download or package installation
is part of replay. See README.md and results/verification.json.
