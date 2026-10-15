# Global decoder compatibility: continued full-target research

15 October 2026, Asia/Shanghai. Yongxian Zhang (张永贤), South China
University of Technology. No external funding. OpenAI AI assistants assisted.
Original material all rights reserved; third-party attributions retained.

**Status.** SC0 is not proved or refuted. The statements in this note are
elementary equivalences, special cases and restrictions on attempted routes.
They are not counted as new major results or claimed to be new. This note
does not replace the exact size-VC, no-side-information target by one of its
stronger or restricted variants. No Lean or independent review is asserted.

## 1. The conflict graph with the actual lists

Fix a finite domain X and binary class C of VC dimension d. Let K(C) be
its entire realizable partial-sample complex, including the empty sample.
Join two faces S,S' when their labels disagree on at least one coordinate
of their common domain. Give S the list

    L(S) = {T: T is a labeled subset of S and |T|<=d}.

Then SC1 for this C is exactly proper list coloring of this conflict graph
using these lists. In one direction color S by its compressed message.
Two incompatible samples cannot have the same message because its single
total decoder would have to extend both. In the other direction, all samples
of one color T are pairwise consistent. Their union is therefore a partial
Boolean function, contains T if the color is used, and extends to a total
h_T. A color never used may be assigned any extension of T. Choosing the
color of S as kappa(S) proves the original no-side-information condition.

This equivalence does not discard partial samples. It does not assert that
one-to-one representatives for the complete rows solve the coloring problem.
The admissible color set depends on the whole labeled subset T, so it also
does not replace the problem by an unlabeled coloring.

Clique Hall conditions are necessary: every pairwise incompatible family
F must satisfy |F|<=|union_{S in F} L(S)|. A construction satisfying all
these necessary inequalities still needs a proof of the global coloring.
There is no perfect-graph shortcut from low VC dimension alone. For example,
take C to be the five singleton concepts on coordinates modulo five, with
VC(C)=1, and take

    S_i = {(i-1,1),(i,0)},  i in Z/5Z.

These five realizable samples induce precisely C_5 in the conflict graph:
only neighboring samples share a coordinate with opposite labels. This
shows nonperfectness even for VC one. It does NOT show that the actual lists
of this example are uncolorable; that class has a size-one scheme.

## 2. Why a uniformly sampled proper decoder need not even cover in mean

One possible fractional route chooses each h_T uniformly among the concepts
of the original C extending T. If V_S denotes the version space of S, the
expected number of successful messages for S is

    sum_{T subset S, |T|<=d} |V_S|/|V_T|.                 (GC-1)

This expectation need not be at least one, even at VC two. This defeats that
particular distribution, not arbitrary fractional choices and not SC0.

Use the following ten five-bit rows, with the leftmost displayed position
interpreted as coordinate zero:

    11000, 01100, 00110, 00011, 10001,
    01011, 01101, 10110, 10101, 11010.                   (GC-2)

These are the Warmuth class from Example 2 of Darnstaedt, Doliwa, Simon and
Zilles, *Order Compression Schemes* (ALT 2013). Its VC dimension is two,
and every complete row needs three labels to teach it against the other
nine rows. Both finite facts are checked by exhaustive coordinate subsets
in the accompanying control file; the exact table is the primary input.

Fix its first row c_0. Keep c_0 once, with all new coordinates zero. For
each of the other nine core rows make M copies, each with its own private
coordinate equal to one and all other new coordinates zero. Call the total
class C_M on 5+9M coordinates. Its core projection has VC dimension two.
A private coordinate equals one in just one concept, so no shattered set
of size at least two can contain it: on that private coordinate's positive
fiber, every other coordinate has only one label. Consequently VC(C_M)=2.

Take S to specify all five core labels of c_0 and no private coordinates.
Then |V_S|=1. Every T subset S of size at most two also matches another
core row, by the teaching fact, and therefore at least M+1 concepts of C_M.
There are exactly 1+5+10=16 eligible T. Thus (GC-1)<=16/(M+1), which
tends to zero. For M=17 the exact computed value is 75329/159390.

Independent choices of the h_T are not required to derive this expectation;
the same formula holds for any coupling with these particular marginals.
Expectation below one means these marginals cannot be a distribution
supported entirely on successful global schemes for this S. It does not
exclude one successful assignment in their support, nor a different prior,
an improper decoder, or a general fractional solution.

There is also a deterministic majority control. Instead give the nine
non-target core rows respectively 2,4,8,...,512 private-coordinate copies,
and keep the target row once. VC remains two by the same private-coordinate
argument. For every eligible T subset S of size at most two, at least one
other core row matches. Its largest matching multiplicity strictly exceeds
the sum of all smaller matching multiplicities together with the target's
weight one. Thus the coordinatewise uniform-version-space majority on the
five core coordinates equals that largest row and disagrees with S.
There are no ties in these core disagreements. Hence arbitrary tie breaking
cannot repair this particular majority decoder. The resulting class has
1023 concepts on 1027 coordinates. It remains no counterexample to SC0:
the decoder rule has been explicitly restricted to conditional majorities.

## 3. Labeled schemes can be smaller than VC dimension

A related false shortcut would use VC dimension as a universal lower bound
for unrestricted labeled compression. It is a lower bound for unlabeled
schemes, and for the acyclic order model in the cited primary, but not for
the full labeled improper model here.

For any integer k>=2 and any finite domain |X|<=2k+1, every Boolean partial
sample, whether or not restricted by a concept class, has the following
fixed size-k scheme. Decode an empty message as the all-one hypothesis.
Decode a nonempty message with only positive labels as exactly that positive
set. Decode a singleton negative as the all-zero hypothesis. Decode any
other all-negative message, or any mixed message, using default one outside
the message. Always retain the supplied labels on the message itself.

To compress S, let a and b be its numbers of positive and negative labels.
If b=0, send empty. If a=0 and b>0, send one negative example. If 1<=a<=k,
send all a positive examples. Otherwise a>=k+1, so b<=k. If b>=2, send all
negative examples; if b=1, send that negative and any positive, using the
assumption k>=2. In every case the decoder is consistent with S and depends
only on the message. These cases include every sample of every size.

Thus the full cube on 2k+1 coordinates, whose VC dimension is 2k+1, admits
size-k labeled compression. The control enumerates all 3^n partial samples
for (n,k)=(5,2),(7,3),(9,4),(11,5). The same elementary proof covers all k.
This special case gives SC1 whenever d>=2 and n<=2d+1. It gives no theorem
for arbitrary n at a fixed small d, which is the central full-target gate.

## 4. Acyclicity is an actual extra condition, even allowing improper output

The same table (GC-2) gives a complete known counterexample to the route
"always choose a globally ordered decoder of size d". For completeness,
suppose there were a total order of a finite hypothesis image H containing
C for which decoding selects the last hypothesis consistent with its message.
Let c be the earliest member of C in that order. Its full sample must decode
to c. Its successful message must distinguish c from every other member of
C, all of which are later. Hence that message has size at least three.
Adding improper hypotheses to H does not affect this argument.

Every general scheme on this finite domain has a finite image. The cited
primary proves that acyclicity of its compression graph is equivalent to
an order scheme, with a harmless normalization of the chosen messages.
The primary also supplies a cyclic size-two decoder for (GC-2). The universal
decoder in Section 3 supplies one as well and is directly checked on every
realizable partial sample. Therefore the acyclic size-d route is false,
while SC0 on this class is true. No restricted-route impossibility is
reported as a refutation of the original conjecture.

## 5. A projection/reduction induction must retain ambiguous partial samples

Split one coordinate of C and write C_0,C_1 for the two remaining-coordinate
classes. The full-row reduction I=C_0 intersect C_1 has VC dimension at most
d-1. But the ambiguous sample complex is

    P = K(C_0) intersect K(C_1),

and in general P strictly contains K(I). For example take C_0={00,11} and
C_1={01,10}. Their intersection is empty, yet every one-coordinate labeled
sample on the remaining two coordinates is ambiguous. The original class
of three-bit rows obtained by adding the split label has VC dimension two.
Discarding these faces would leave part of the original compression target
uncovered.

P, regarded as a partial class closed under restriction, has VC dimension
at most d-1: if it shattered a set of d remaining coordinates, then both
split labels together would shatter d+1 coordinates in the original class.
It need not be the sample complex of any total class, since its maximal
faces need not have full remaining domain.

Crucially, a proof based ONLY on the VC dimension of an arbitrary partial
class is unavailable. Alon, Hanneke, Holzman and Moran's primary paper
*A Theory of PAC Learnability of Partial Concept Classes*, Theorem 7,
constructs a partial VC-one class requiring unbounded sample compression
size, even allowing side information. This theorem concerns partial classes
and does not refute SC0 for total binary classes. Whether the additional
two-total-parent structure of P supplies a useful size-(d-1) theorem has
not been established here. A failed reduction to K(I) does not settle it.

## 6. Sample-complex topology is not bounded by VC dimension

For n>=2, again let C be the n singleton concepts. All realizable partial
samples have at most one positive label. An all-negative sample is
realizable precisely when it omits at least one coordinate. Let f_{j-1}
count its faces with j literals. The face enumerator is exactly

    F(z)=(1+z)^n-z^n+n*z*(1+z)^(n-1).

The first two terms count proper all-negative samples, and the last term
chooses the positive coordinate and any subset of the other negative ones.
Since all maximal faces are full rows, their cardinality is n and the usual
pure-complex h-polynomial is

    (1-t)^n F(t/(1-t)) = 1+n*t-t^n.                 (GC-3)

In particular its top coefficient is negative. This has a direct elementary
consequence: K(C) cannot be partitioned into Boolean intervals [T,c] with
upper faces c complete concept rows, for ANY bound on |T|. Indeed each such
interval contributes z^|T|*(1+z)^(n-|T|) to F(z), and hence t^|T| to (GC-3).
A disjoint interval partition would make every h coefficient nonnegative,
contradicting the coefficient -1 of t^n.

This does not obstruct overlapping covers, which are what the decoder
problem actually needs. Nor does it obstruct improper upper graphs, whose
intersection with K(C) need not be an interval with a realizable upper face.
For example h_empty=all-zero and h_{(i,1)}=the i-th singleton already give
a size-one improper scheme: all-negative samples use empty, others use the
unique positive literal. So even this elementary negative coefficient must
not be promoted to a no-compression conclusion.

The same sample complex has homotopy type S^(n-2). Its n maximal simplices
have a simplex as every proper nonempty intersection: for a proper set of
singleton concepts, the common negative coordinates are exactly those not
in that set. The intersection of all n facets is empty. The nerve is thus
the boundary of an (n-1)-simplex, and the standard finite nerve theorem
applies to this simplicial good cover. This illustrates why the complex of
all signed samples is different from the cubical one-inclusion complex of
the concept rows. The statement is a route control, not a new major result.

## 7. The remaining global gate

These deductions preserve the original target. A proof would have to choose
compatible colors/hypotheses for all partial samples at once, without
assuming acyclicity, disjoint proper intervals, a universal uniformly sampled
proper decoder, or bounded-dimensional topology of K(C). The exact finite
coloring and decoder constraints still have no universal construction or
legal unsatisfiable instance here. Full SC1/SC2 remain open. The compactness
bridge SC3 remains conditional on SC1. New major solved results: zero.

Primary sources, with actual bounded read scopes, are recorded separately.
