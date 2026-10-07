# Independent adversarial audit: bounded-cluster avoidance

Audit date: 7 October 2026. Public report adapted from the frozen independent audit.

## Verdict

**No core mathematical gap found in Theorem A.** The finite-cluster extension
of the routing engine is valid under the stated fixed-cardinality,
positive-upper-Banach-density, and prescribed countable-modulus hypotheses.
Its key new estimate is an inequality, and the proof does not require
independence of the full cluster-routing events.

There is one literally incorrect density-placement sentence and several
clarifications worth making before further use. An original-set maximizing
window need not recur arbitrarily far out. A window maximizing for the
translated tail supplies exactly the lower bound the proof needs, with the
same global upper-count constants. The separate clarified copy repairs this
sentence, makes the deterministic finite test set explicit, disambiguates
the error constant, and states the stronger robust quantifier order already
proved. It also clarifies an ambiguous derivative sentence and the hypotheses
of the effective-search paragraph. The checker algorithm requires no change;
its inaccurate singleton-hit docstring has a separate proposed correction.

The exact checker agrees with a separately implemented rational
Fourier--Motzkin/arrangement oracle on **1,006 cases: 159 covers and 847
failures**. Of these, **773** reached geometric feasibility; 233 correctly
failed the density budget. All seven original regressions pass in normal and
optimized Python with byte-identical output. The supplied four-cluster
certificate is valid with density **4/5**, after nine subject-checker states.
Deleting its last cluster produces the advertised exact counterexample.
These computations concern finite certificate checking only. They do not
construct blockers of arbitrarily small density and do not verify the
infinite theorem computationally.

This is another model-conducted written mathematical audit, not human
refereeing or proof-assistant formalization. No novelty or priority finding is
made. The reviewed subject includes the fixed-width-annulus extension and Corollary B, reviewed in Section 11. The frozen subject and source hashes are bundled.

## 1. Exact subject and primary-source boundary

The frozen subject is bundled as `../avoidance-covering-provenance/audited-subjects/bounded-cluster-audited-subject.md`, SHA-256 `00a30c349e3cde98faf5b1df361d94cd69320f6598c561921964387b32fd53a2`. The public note applies only the listed mathematical clarifications plus source attribution and notation exposition. The checker changes only its inaccurate module docstring.

Comparison sources are pinned at mxym/math commit `1c67b4146f9e54291c8a5ca1f42a028bf307629f`. Their URLs, Git blob hashes, SHA-256 hashes, and byte sizes are recorded in `../avoidance-covering-provenance/PROVENANCE.json`. Bundled exact copies include 004 v1.1, 006 v1, and 006 v2.

004 proves singleton avoidance using finite routing, logarithmic-density
template placement, a local dilation entropy estimate, and exceptional-center
repair. 006 v1 supplies the location-independent template threshold and the
two-buffer robust normalized blocker. Actual 006 v2 proves preservation of
positive logarithmic density under a log-bi-Lipschitz profile, then transfers
006 v1 to a **countable family of fixed leading profiles**. Its Section 6
explicitly disclaims an arbitrary uncountable profile family.

The added substance here is simultaneous success of every candidate in a
bounded cluster. No dimension statement from entry 003 is needed by that
proof. This audit did not independently establish literature priority or
re-audit all external papers cited by the draft.

## 2. Density flattening and parameter order

For `F_S(L)=sup_m |S intersect [m+1,m+L]|`, subadditivity gives
`delta=inf_L F_S(L)/L`. For each positive xi a global block partition yields
`|S intersect I| <= (delta+xi)|I|+C_xi` for every integer interval I.
Deleting or translating a finite prefix does not change delta.

For any cutoff H, the translated tail has `F_tail(T)>=delta T`; its
integer-valued supremum is attained. Translating its maximizing T-window
back gives a window **beyond H** with at least delta T points. Subtracting
the two complementary intervals of a template window W gives

`|S intersect W| >= delta|W| - xi C0 L - 2C_xi`.

Crucially, C_xi is the bound for the original S and is independent of H.
Thus xi and a sufficiently large L can be chosen before the absolute
template location, as required for the later finest-grid buffer.

### Literal sentence requiring correction

The sentence claiming a maximizing interval arbitrarily far out is false if
"maximizing" refers to the original S. For example, let
`S={1,...,20} union {even integers >=22}`. It has delta=1/2 and original
length-four maximal count four, but every sufficiently late length-four
window has count two. The proof only needs the latter lower bound delta T.
The separate clarification replaces the sentence with the translated-tail
statement, leaving every subsequent bound intact.

At least one parity part of S has positive upper Banach density by finite
subadditivity. Restricting to it suffices for the conclusion on the original
S. For fixed routing arity, depth, and gap, the tree-window recurrences give
finite span T<=C0 L and edge-plus-child span at most twice its window length.

Valid choice order:

1. Fix one cluster system, its bound K, a positive-density parity, and eta.
2. Fix p; set theta=(p/2)^K.
3. Choose routing arity M with theta eta(M-1)>4.
4. Choose depth d to make the no-default cost less than p.
5. Determine the finite number Q of edges and choose the gap g.
6. Choose L for density flattening and the entropy/probability estimate.
7. T is now fixed. Choose a lower bound for the template location from the
   null modulus and buffer cost.
8. Place the filled template after that bound, then choose a table outcome.

There is no circular dependence of T on the late location. The resulting
parameters can be extremely large; no numerical practicality is implied.

## 3. Address separation, routes, and collisions

For j<k in the selected parity, k>=j+2. For a in F_j and b in F_k,

`a-b >= 2^(-j-1)-2^(-k) >= 2^(-j-2)`.

At a window endpoint v this is at least `2^(-v-2)`, twice its grid-cell
width `2^(-v-3)`; the bound is deliberately weaker than necessary. The
candidate-center distance is at least `2^(-v-1)`. Multiplication by
t in [1,2] preserves separation. With all indices at least four, all
displacements lie in an interval of length at most 1/8. Circular distance
therefore agrees with ordinary distance between displayed points, so
periodic wraparound does not produce same-cell collisions. Distinct keys
remain distinct at all finer nested grids.

Within one F_j, candidates can share keys, including at terminal grids.
Nothing in the proof assumes otherwise. Such sharing lowers the number of
independent successes needed and thus improves the lower bound.

Stability excludes crossings of the immediate predecessor grid; nesting
then excludes every earlier-edge grid crossing. At a first-default vertex
U, a tested candidate on outgoing edge i follows x through all strict
ancestors and rejects all children before i. Those decisions precede its
own window in preorder. If its own-edge selector is one, it really enters
child i, and its local terminal result is its actual result.

Center exposure includes the addressed center entry in **every selector
table** and no terminal entries. Tested own-edge addresses avoid these
center entries. Exposing selectors in later or off-route tables therefore
does not change their fair laws. Auxiliary selector collisions across tests
are permitted and must not be mistaken for independence of whole routes.

## 4. The new conditional-independence inequality

Fix a stable x, a normalized t, and a center-exposure atom with a first
default. Let A_j assert that every distinct own-edge selector addressed by
cluster j equals one. If s_j is the number of such distinct entries, then
`1<=s_j<=K` and

`P(A_j | center exposure)=2^(-s_j)>=2^(-K)`.

Different clusters' own-edge entries are disjoint: at the same edge this is
the parity/grid separation, and different edges use different tables.
Consequently the A_j are independent under center exposure.

Next condition on **all** selectors. All local leaves and terminal addresses
are now deterministic. Terminal addresses of different tested clusters are
disjoint for exactly three reasons:

- Tests in different outgoing windows of U use disjoint child subtrees
- Different leaves have different terminal tables
- At the same leaf, its incoming terminal grid is no coarser than the
  tested own-edge grid, so distinct index-clusters retain distinct keys

For cluster j let d_j be the number of distinct terminal table/address pairs.
Then `1<=d_j<=K`. Conditional on all selectors, its terminal success has
probability p^d_j, and these terminal-success events are independent across
clusters. Thus the conditional failure probability for the sufficient
entire-cluster tests is

`product_j (1 - 1_Aj p^d_j) <= product_j (1 - 1_Aj p^K)`.

After this inequality, the d_j have disappeared. Averaging the right side
requires only independence of the A_j, not of the shared auxiliary routes:

`E product_j (1 - 1_Aj p^K)`
` = product_j (1 - p^K P(A_j | center exposure))`
` <= (1-(p/2)^K)^m <= exp(-theta m)`.

This proves the claimed bound. For K=1 it recovers the singleton engine's
exact identity. For K>1, treating it as an exact identity would generally be
incorrect, and the draft correctly does not do so. Failure of every actual
entire cluster implies failure of these sufficient local tests, so the
bound applies in the needed direction.

## 5. Compact dilation cover and endpoint cases

Each local candidate's complete test is determined by the finest grid in its
edge-plus-child subtree. For fixed x the possible crossing parameter values
are deterministic, independent of every unexposed table bit. Its crossing
count is at most `1+2^(2ell+3)` and there are at most K(M-1)ell candidates.

The representative set includes both normalized endpoints, every grid
crossing itself, and one point in every complementary open interval. On
each such interval the whole test vector is constant for every table
outcome. Boundary-only failures cannot be lost through the half-open grid
convention. The claimed representative bound is conservative.

The decay rate theta eta(M-1)>4 beats the entropy rate 2 log 2. Hence a
location-independent L makes the union-bound error less than p for every
window length ell>=L. The route never defaulting has probability
`(1-2^(1-M))^d<p`; all first-default atoms have the same uniform bound.
After adding unstable centers of density below p, the expected residual
center density is at most 3p.

One presentation clarification is necessary for complete readability:
the exceptional-center set should range over the deterministic finite set
`I=S intersect union_e W_e`, not an atom-dependent first-default subset.
The local subset estimates imply the all-I failure estimate. The separate
clarified copy now names I explicitly.

## 6. Robust errors and universal centers

With T fixed, the finest number of cells is `N=2^(u+T+2)`. Set
`eta_u=omega(2^(-u))+2^(-u)` and `r_u=2^(-u) eta_u>0`. Monotonicity gives
`a omega(a)<=r_u` for every finite tested candidate. The exact buffer cost is

`4N r_u=2^(T+4) eta_u -> 0`.

Because the location threshold is chosen after T but before placement,
the cost can be made less than p at every later possible start. Adding the
positive `2^(-u)` handles an identically zero modulus as well.

For B1=B+(-r_u,r_u), B2=B+(-2r_u,2r_u),

`B1+[-r_u,r_u] subset B2`.

This is strict-open containment even when an allowed error equals r_u.
The enlargement bound sums over at most N occupied cells and is valid
despite periodic wrap or overlapping enlargements. Therefore expected
density(B2)<2p.

The failure set in the compact circle-times-[1,2] parameter space is a finite
intersection of finite unions of closed sets, since B1 is open and the
clusters are finite. Its projection R is closed. Choose a table outcome
with density(B2)+density(R)<5p, then an open V containing R with at most
p extra density; H=B2 union V has density below 6p.

- If x is outside R, for every t one finite cluster is entirely in B1.
  That same cluster survives every allowed independent error array in B2.
- If x is in R, x lies in open V. The candidates and their allowable error
  radii tend uniformly to zero with j; all sufficiently late whole
  clusters lie in V, uniformly for t in [1,2] and for all allowed errors.

Thus the proof actually yields the stronger normalized quantifier order

`for every x,t, there exists j, for every independent error array:`
`the entire perturbed cluster j is contained in H`.

The successful cluster is chosen before the error array. No measurability,
continuity, or coherence of the array is needed. The weaker order stated in
Theorem A consequently follows. Repair is pointwise for every center, not
merely almost everywhere.

## 7. Global indices and infinitely many distinct misses

The global construction has only countably many components:
modulus r, dyadic coefficient k, integer error bound q, tail cutoff h,
and optionally the prescribed cluster-system index. Transformed candidates
`b=2^k a` occupy annuli shifted by -k; deleting finitely many nonpositive
indices preserves positive density and the cluster-cardinality bound.

The transformed modulus
`Omega(b)=q 2^(-k) omega_r(2^(-k)b)` satisfies
`b Omega(b)=q a omega_r(a)`. Its scale factor is correct. Choose q at least
the finite error constant in the theorem, not the independently chosen
local routing arity also denoted M. Both can vary between components.

Write c=2^k t for c>0, t in [1,2]. All sufficiently late cutoffs h are past
the error array's validity threshold, so their components give whole-cluster
misses at unbounded indices. For c<0, reflected blockers apply after
negating y and the errors. Summable budgets with
`12 sum p_component < epsilon` account for both signs. The complement E
is closed and periodic, and has the asserted measure in every unit interval.

On sufficiently late selected candidates,
`(|c|/2)a_j <= |v_j-y| <= (3|c|/2)a_j`, since the relative errors vanish.
Thus hit values converge to y and never equal y there. A finite set of
distinct non-y values cannot have that property, so every tail contains
infinitely many distinct misses. Whole-cluster success excludes every
pointwise selector simultaneously, without enumerating selectors.

Finally a fixed bounded selector tail can be scaled and translated into
any proposed open interval of E, contradicting the already proved affine
avoidance. E has empty interior and is nowhere dense.

## 8. The binary family and the countability barrier

Let sigma_n be 1 or 3/2 and interpolate the logarithmic knots
`Psi_sigma(n)=n-log_2 sigma_n`. Adjacent slopes are in
`[alpha,beta]=[1-log_2(3/2),1+log_2(3/2)]`, with alpha>0. This supplies
common logarithmic bi-Lipschitz constants, strict monotonicity, and the null
limit for every infinite binary sequence. The prescribed knot values are
exactly candidates of the two-point annular clusters in the example.

Different binary sequences give different knot values, hence different
profiles. There are continuum many profiles. For first difference m,

`(1/2)2^(-m) <= ||phi_sigma-phi_tau||_infinity <= 3 2^(-m)`.

The lower bound is the knot difference. The profiles agree before m-1 in
logarithmic coordinates; after that both have size at most 3*2^(-m).
This also handles m=1. Thus the profile map is bi-Lipschitz from the binary
ultrametric with distance 2^(-m). Binary-cylinder counts give upper box
dimension one and Assouad dimension one; bi-Lipschitz invariance transfers
both dimensions to the compact profile family in the uniform norm.

Individual image sequences have ratios among 1/3, 1/2, and 3/4, so only
O(log(1/r)) terms precede a scale r and their remaining tail fits in one
O(r)-interval. Their upper box dimension is zero. Their occupied logarithmic
bins still have positive density. These statements concern different
objects and should not be combined into an unsupported dimension criterion.

### Why countably many fixed asymptotic profiles do not already cover it

If two binary selectors were relative-o(1) scalar approximations to the same
fixed positive profile, their quotient on A would converge to the quotient
of those two scalars. But that quotient takes only values 2/3, 1, and 3/2.
Convergence in this discrete set forces eventual constancy.

- Eventual quotient one means eventual equality of the binary sequences.
- Eventual quotient 2/3 or 3/2 means both sequences have constant tails.

Every eventual-equality class is countable: only a finite prefix can vary.
Each constant-tail class is also countable. Thus one arbitrary fixed
asymptotic profile, even permitting an individual scalar for each selector,
covers at most countably many selectors. A countable family of such profiles
cannot cover continuum many selectors. In fact the quotient by eventual
equality has continuum many classes. Actual 006 v2's countable fixed-profile
bookkeeping therefore does not supply this theorem's new quantifiers.

On segment interiors, `phi_sigma(a)/a` lies in [1,3/2], while the derivative
is that ratio multiplied by a slope in [alpha,beta]. The derivative bounds
are [alpha,(3/2)beta], **not** [1,3/2]. The original sentence is ambiguous;
the clarified copy identifies the ratio and gives the correct common
derivative bounds. They imply ordinary bi-Lipschitz estimates extending to
zero by continuity, without a C1 claim. Non-eventually-constant sequences
have a nonconvergent ratio phi_sigma(2^(-n))/2^(-n), so are not differentiable
at zero. This restricted family is compatible with 006 v1's positive C1 and
flat-smooth embedding endpoint results.

## 9. Exact checker and independent computation

The certificate assertion is

`for every x,t, there is one listed cluster, for every candidate a:`
`[x+t a-r_a, x+t a+r_a] is contained in open H`.

Its failure is `exists x,t; for each cluster choose one candidate and one
legal escaping error`. A closed complementary gap [l,u] is reachable
precisely when `l-r_a <= x+t a <= u+r_a`. Enumerating all such candidate/gap
choices and clipping a closed rational rectangle implements the correct
logical negation. Segments and singleton intersections are retained.

The global search bounds `lo=min(a-r_a)` and
`hi=max(1+2a+r_a)` contain every possible escaped point. Open periodic
intervals are merged only under strict overlap, preserving touching-endpoint
singleton gaps. The exact periodic membership predicate is equivalent to
the existence of an integer in the strict interval `(z-b,z-a)`. Witness
errors are independently checked against both the radius and open H.

The independent oracle in `verification/independent_checker_audit.py` does not import the
subject density, gap, clipping, or membership routines. It builds a rational
endpoint arrangement, determines covered intervals by midpoint membership,
and retains uncovered endpoints separately. To decide a selected collection
of strips it eliminates x: every affine lower bound for x must lie below
every affine upper bound, yielding a closed rational interval for t.
This Fourier--Motzkin approach independently checks degeneracies.

The 1,006 cases consist of the two toys, the three-cluster deletion, three special
boundary/wrap/error tests, 400 general random rational cases, and 600
geometry-focused annular-cluster cases varying radius, scale, shifted
intervals, touching splits, and genuine split gaps. The latter all use budget
one, so do not terminate at a density-budget mismatch. Results are in
`verification/independent_checker_results.json`.

Original regression output SHA-256:
`7b81d77fd1bc0f27072ac5a30adbb9e45500fc7aed3aba61b6e4af35c5d203c9`.

The four-cluster toy has H=(0,4/5)+Z and r_a=a/100. Its valid density is 4/5.
With only its first three clusters, the subject witness is
`x=7/15, t=1591/900`; escaping candidates/errors/values are:

- `3/4`, error `3/400`, value `9/5`
- `1/4`, error zero, value `3271/3600`
- `3/16`, error `3/1600`, value `4/5`

Endpoint equality is essential for the first and third escaped values. A
different rational witness obtained by the independent oracle is also
recorded. The subject docstring incorrectly says “at least one” perturbed
candidate; the algorithm and result claim implement the stronger entire
cluster assertion. Only the docstring needs correction.

## 10. Effective finite search

The final search paragraph is correct **under the theorem's bounded K and
positive-annular-density hypotheses**. It should state these explicitly,
since computability and vanishing relative radii alone do not imply
arbitrarily small blocker existence.

For rational radii with r_a/a uniformly tending to zero by the annular
cluster index, take a monotone envelope over candidates at scales no larger
than a given a. The finite prefix and convergent tail make this envelope
finite, nondecreasing, and null. It bounds all relative radii. A computable
rate of convergence is unnecessary for the existential proof or the eventual
success of exhaustive enumeration.

The robust proof supplies an open H of strictly smaller density. At each
parameter pair, the chosen whole finite cluster has compact closed
uncertainty intervals contained in H. Their distance from the complement is
positive, so the same success is valid in a neighborhood of the parameters.
Choose finitely many rational open intervals inside H covering those compact
uncertainty sets. Success still holds in a neighborhood; compactness of
[0,1] times [1,2] gives finitely many neighborhoods/clusters/intervals.
Their union remains inside H, so its density stays strictly below budget.

Any finite collection of listed clusters occurs in a finite enumeration
prefix. Dovetailing enumeration of rational interval lists and cluster
prefixes, with the exact terminating verifier, eventually finds a valid
certificate. There is no feasible-time, complexity, or computed
arbitrarily-small-density claim.

## 11. Added fixed-width annuli and finite profile alphabets

The frozen subject includes the fixed-width-annulus extension, Corollary B, and the six-cluster certificate. Its SHA-256 is `00a30c349e3cde98faf5b1df361d94cd69320f6598c561921964387b32fd53a2`.

The fixed-width annulus statement is sound. After dividing candidates by
Lambda, choose q>=1 with `2^(-q)<=lambda/Lambda`. One residue class modulo
q+1 has positive density. For selected j<k, k>=j+q+1, so

`min F_j-max F_k >= 2^(-j-q)-2^(-k) >= 2^(-j-q-1)`.

At endpoint b>=j and grid `N_b=2^(b+q+3)`, this is at least four cells;
the candidate-center distance is at least eight cells. The changed constants
in the appendix are correct:

- Instability bound `Q 2^(q+3-g)`
- Entropy factor `4+2K(M-1)ell(1+2^(2ell+q+3))`
- Finest grid `N=2^(u+T+q+2)`
- Buffer cost `4N r_u=2^(T+q+4)eta_u`

The entropy's exponential rate remains 2 log 2. All choices precede the
absolute location as before. Dividing original candidates a by Lambda gives
b=a/Lambda, coefficient c Lambda, and error modulus
`Lambda omega(Lambda b)`, which is finite, nondecreasing, and null. Thus the
normalization sentence needs no additional hypothesis.

Corollary B correctly combines 006 v2's logarithmic-density preservation
with the cluster theorem. For a finite positive alphabet D and chosen
`b_j=phi_r(a_j)`, the cluster D b_j lies in a fixed-width annulus and has
bounded cardinality. Let d0=min D>0 and
`Omega(b)=omega_w(phi_r^(-1)(b))`. For candidate u=d b, define
`Omega_new(u)=Omega(u/d0)`. Then

`M b Omega(b) <= (M/d0) u Omega_new(u)`.

The inequality uses both d>=d0 and monotonicity. Assigning the same error
e(a_j) at every candidate in that cluster is allowed; whole-cluster success
then covers any arbitrary switching choice d(a_j). The profile, alphabet,
configuration, and modulus indices stay countable, while the switching
functions themselves are uncountable and are not enumerated. Distinct miss
values follow from d0>0 and vanishing relative error. This is a genuine
generalization beyond the binary identity-profile example, with no new
countability or error-scaling gap found.

The added six-cluster certificate for `(0,3/4)+Z`, with the same r_a=a/100,
replays valid in fourteen subject-checker states and is also checked by the
independent oracle. It remains a finite normalized certificate, not evidence
of a computed arbitrarily-small-density construction.

## 12. Public evidence and scope

The public package contains the corrected complete note, the frozen audited subject, the mathematical clarification patch, the docstring-corrected checker, all supplied certificates and regression outputs, and the independently implemented oracle with its 1,006-case result.

The theorem remains a written probabilistic argument with finite checker evidence. Unbounded cluster sizes, intervals of candidates, all real exponents, all null moduli, arbitrary C1 maps, and all flat smooth germs do not follow from it.
