# Forced-label normalization and why one fixed default cannot close SC0

15 October 2026. Yongxian Zhang (张永贤), South China University of
Technology. No external funding. OpenAI AI assistants assisted. Original
material all rights reserved; third-party rights retained.

**Status:** an author-only route analysis for the original strong labeled
sample compression problem. New major solved results: zero. No novelty
priority, independent mathematical review or Lean proof is claimed.

## 1. Forced-label normalization preserves the original existence question

For a realizable message T let V(T)={c in C: c extends T}, which is
nonempty. If every c in V(T) has the same label b at coordinate x, then
a decoder output rho(T)(x) can always be replaced by b. Indeed any
realizable sample S containing T and x has its label at x equal to b.
This replacement cannot spoil consistency with any such S; samples which
do not contain x are unaffected. Applying this independently at every
forced coordinate therefore preserves every successful old message.

Thus general compression may, without loss, use one total hypothesis per
message which agrees with every label forced by its version space. This
includes agreement with T itself. Its remaining values at ambiguous
coordinates still have to be chosen simultaneously for every T, and may
depend on T. There is no properness restriction in this normalization.

## 2. The fixed-default proposal

Choose one total reference hypothesis r, allowed to be outside C. Define

    rho_r(T)(x) = the common label of V(T), if that label is forced;
                 r(x), otherwise.                         (FD-1)

For VC-one classes, closely related tree-order/unanimity constructions
are known; see Ben-David, [*Notes on Classes with Vapnik-Chervonenkis
Dimension 1* (2015)](https://arxiv.org/html/1507.05307v1), and the
tree-order summary in Attias, Hanneke and Ramaswami,
[*Sample Compression Scheme Reductions*, Lemma 34](https://raw.githubusercontent.com/mlresearch/v272/main/assets/attias25a/attias25a.pdf). The exact
primary scopes read for this research packet are recorded separately.
The following argument tests whether the simple fixed-default extension
could suffice for arbitrary VC dimension.

For any finite C on finite X, if (FD-1) is a size-k compression decoder,
then C has at least one concept with teaching dimension at most k.

To prove this, choose c in C maximizing its Hamming distance from r.
Let D(c,r) be the coordinates where they disagree. If rho_r(T)=c on ALL
of X, every x in D(c,r) must be forced to c(x), since the unforced
prediction r(x) would be wrong. Hence every c' in V(T) agrees with c on
D(c,r). Equivalently D(c,r) is a subset of D(c',r). By maximality of the
Hamming distance, this inclusion is equality, and then c'=c everywhere.
Thus V(T)={c}: T teaches c. The full sample c must have a successful
message T of size at most k, so c has teaching dimension at most k.

This proof allows arbitrary labeled T, arbitrary improper r and improper
outputs rho_r(T). It does not impose an ordering on decoder outputs.

## 3. Failure at the actual parameter k=VC=2

Use the familiar ten-concept Warmuth class on five coordinates, in the
bit-mask convention of the other finite controls:

    C={3,6,11,12,13,17,21,22,24,26}.

It has VC dimension two, and EVERY concept has teaching dimension three.
These facts are checked directly in the archived controls and its
single-shift note describes the pair and triple traces explicitly.
Section 2 shows that NO choice of fixed r, including all 32 improper
possibilities, makes (FD-1) a size-two decoder for this C. At least a
maximal-distance complete row has no successful eligible message.

Nevertheless C has a genuine general size-two decoder, as witnessed by
the universal five-coordinate construction in the continued notes. The
failure therefore identifies an actual restriction of the proposed rule,
not a counterexample to the strong compression conjecture. The distinction
is especially relevant here: even after all forced labels have been set
without loss, the remaining ambiguous predictions cannot in general be
chosen from one common default hypothesis.

## 4. A second closure shortcut is also too restrictive

Another proposal is to flip labels relative to a reference, then reconstruct
a message of positive examples by intersecting all concept supports which
contain them. A basis for every realizable positive set would suffice for
compression. In general its basis size is not controlled by VC dimension.

For instance C={empty} union {X\{i}: i in X} has VC dimension two for
|X|>=3. With the empty reference, P=X\{i} requires ALL |X|-1 positive
points as an intersection-generating basis: for every proper Q subset P
and every x in P\Q, the concept X\{x} contains Q but omits x. Thus the
intersection closure of Q cannot recover all of P. This particular class
still has a size-one improper scheme: empty -> all zero, positive
singleton -> all one, negative singleton at i -> X\{i}. Samples with a
positive and a negative have only one negative, so these cases cover all
realizable samples.

Allowing a better reference can repair this particular closure example;
the Warmuth argument above excludes the full fixed-default proposal for
EVERY reference. More general message-dependent choices and cyclic
rerouting remain available in SC0. Neither sufficient construction has
been promoted to an assumed property of arbitrary VC-d total classes.

## 5. Two arbitrary fixed references also fail on a larger listed VC-two class

A broader attempted construction supplies two fixed total references r,s
and permits EACH message T to select either one as its ambiguous-coordinate
default. Selection is part of the preconfigured decoder, so it introduces
no transmitted side bit. This construction is still more restrictive than
SC0. An exact finite route control excludes it even at k=VC=2.

For the 105-concept class on sixteen coordinates in
CEGIS_N16_D2_SEED149_CNF.json (archived as deterministic gzip), put

    U_T(c) = union_{c' in V(c restricted to T)} D(c',c),
    F_r = {c in C: some |T|<=2 has U_T(c) intersect D(r,c)=empty}.

A fixed-reference forced-label decoder recovers the complete row c from
that T precisely when its ambiguous coordinates U_T(c) agree with r.
Thus F_r is its exact set of locally recoverable complete concepts, before
the choices at shared messages have even been coupled. Any two-reference
decoder can cover at most F_r union F_s.

The complete integer control computes F_r for ALL 65536 total references,
including improper references. There are 18372 distinct profiles and 437
inclusion-maximal profiles. Replacing a profile by a containing maximal
one cannot decrease a union, so it suffices to compare every unordered
pair of the 437 maximal profiles, including a repeated profile. The exact
maximum union cardinality is 104, strictly less than |C|=105. Consequently
every pair r,s misses at least one complete concept, regardless of its
per-message selection rule. It cannot be a compression decoder for C.

The profile formula above is the full verification specification. The
control source two_default_certificate.py computes profiles by direct
bit operations for all references, without an SMT solver. The separate
default_family_probe.py instead first minimizes the uncertainty sets and
obtains the same profile counts and absence of a covering pair.
TWO_DEFAULT_FULL_PROFILES.json.gz stores all 65536 profiles and the complete
listed C; TWO_DEFAULT_CONTROL.json binds the input, source and archive
hashes. These are same-author exhaustive finite controls, with no claim of
independent mathematical review or a universal lower bound for arbitrary
compression schemes.

For comparison, the ORIGINAL class has an actual general size-two decoder
and a checked 19211-node deletion-DAG certificate. Its VC dimension two is
also checked separately. Thus the original SC0 conclusion is true on this
very class. The calculation only excludes the proposed two-reference
version of a sufficient construction; it is not a negative original-target
instance and is not a new major solved problem.
