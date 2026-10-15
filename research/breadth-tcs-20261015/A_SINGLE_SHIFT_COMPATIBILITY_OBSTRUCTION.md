# A single shift can decrease labeled compression number

15 October 2026, Asia/Shanghai. Author-only route control, not a solution of
SC0 and not a new major result or novelty claim. The underlying ten-row
class is the Warmuth example in Darnstaedt, Doliwa, Simon and Zilles,
*Order Compression Schemes*, ALT 2013, Example 2. The exact finite lower
bound and shift calculation below are supplied in full so they do not
depend on an SMT unsatisfiability report. Yongxian Zhang (张永贤), South
China University of Technology. No external funding. OpenAI AI assistants
assisted. Original material all rights reserved; third-party rights retained.

Identify a Boolean row on coordinates 0,1,2,3,4 with the integer whose i-th
binary digit is its label at i. Define

    C={3,6,11,12,13,17,21,22,24,26}.

This is the set of the five edges of the cycle 0--1--2--3--4--0, regarded
as their characteristic vectors, together with the complements of its five
nonedges. In particular it has ten concepts and VC dimension two. For each
three-coordinate set B, exactly one of the eight binary patterns is missing.
If the complementary two-set is a cycle edge, the missing pattern on B is
all one; otherwise the missing pattern is all zero. All six mixed patterns
occur. Thus every pair is shattered and no triple is shattered.

The same exclusions characterize C among all 32 Boolean rows. Rows of
weight zero or one violate a forbidden all-zero triple, and rows of weight
four or five violate a forbidden all-one triple. A weight-two nonedge
violates the all-zero exclusion on its complementary triple; a weight-three
row whose complement is an edge violates the all-one exclusion on that
triple. The remaining rows are exactly the listed C. Consequently every
h outside C has a forbidden triple witness B with h|B absent from C|B.

For each four-set A, |C|A|=9. One direct way to check this is that the only
pairs of C differing in exactly one coordinate are

    (12,13) at 0; (24,26) at 1; (17,21) at 2;
    (3,11) at 3;  (6,22) at 4.

Deleting coordinate i collapses exactly its displayed pair, and no other
pair, so ten rows yield nine distinct projected patterns.

## 1. No general labeled improper size-one scheme exists for C

Suppose such a scheme existed. On any fixed four-coordinate set A there
are nine realizable full patterns, and only nine available messages of
size at most one: empty and both labels at each of the four coordinates.
Each message has a single total output and therefore covers at most one
of these nine full patterns. Since all nine must be covered, the nine
message outputs restricted to A are distinct and all belong to C|A.

Consider any of the eleven global messages T, including the empty message.
If its output h_T were outside C, take a forbidden triple B for h_T. There
is a four-set A containing B and the at most one coordinate in T. The
previous paragraph forces h_T|A into C|A, contradicting its forbidden
restriction to B. Thus every h_T actually lies in C, even though the
putative scheme was allowed arbitrary improper outputs.

Moreover any two different messages T,T' are both eligible on some four-set
A containing their at most two support coordinates. Their outputs restricted
to A are distinct by the tight counting above, so h_T and h_T' are different
global concepts. There would be eleven distinct elements of the ten-element
set C, a contradiction. This is a complete unrestricted size-one lower bound.

The universal size-two decoder on every five-point domain given in the
continued notes is an upper bound. Hence the minimum labeled compression
number of C is exactly two, equal to its VC dimension. SC0 is true for C.

This also gives a precise failure of projection MESSAGE-COUNT sufficiency
at a general proposed compression size k=1. On every domain A the number
of projected patterns is at most the number 1+2|A| of size-one labeled
messages, but no simultaneous decoder exists. This is not a failure of
Sauer's VC-one inequalities: C has VC two and does not satisfy those
stronger unlabeled counts at parameter one.

## 2. One ordinary downward coordinate shift gives a size-one class

Shift coordinate zero: if c has a one at zero and c with that bit cleared
is absent, replace c by the cleared row; retain a pair when both rows are
present. The resulting class is

    D={2,6,10,12,13,16,20,22,24,26}.

The general labeled size-one decoder below is specified entirely by its
message. There are no hidden message bits, orders, sample domains or sizes.
All outputs happen to belong to D.

| Message | Output integer |
|---|---:|
| empty | 12 |
| (0,0) | 26 |
| (0,1) | 13 |
| (1,0) | 24 |
| (1,1) | 22 |
| (2,0) | 2 |
| (2,1) | 20 |
| (3,0) | 16 |
| (3,1) | 10 |
| (4,0) | 6 |
| (4,1) | 26 |

Every decoder output agrees with its input literal. To check ALL partial
samples, not just the ten complete rows, use the following deletion-chain
certificate. In the row for c, start with all five coordinates. At every
listed coordinate j, the message (j,c(j)) has an output agreeing with c on
every still retained coordinate; then delete j. At the final residual
domain, the empty decoder agrees with c. The integer residual mask is
provided so every step is a direct comparison with the decoder table.

| Complete row c | Successive deleted coordinates | Final residual mask |
|---:|---|---:|
| 2 | 2,4,1,3 | 1 |
| 6 | 4,1,2,3 | 1 |
| 10 | 3,2,4,0,1 | 0 |
| 12 | none | 31 |
| 13 | 0 | 30 |
| 16 | 3,1,0,4,2 | 0 |
| 20 | 2,3,1,0,4 | 0 |
| 22 | 1,2,3,0,4 | 0 |
| 24 | 1,0,4,3,2 | 0 |
| 26 | 0,4,3,2,1 | 0 |

For clarity, why do these ten finite chains suffice? For any sample R
below a complete row, inspect the first deleted coordinate j. If j lies
in R, its displayed message decodes correctly on the current entire domain
and hence on R. If j is absent, continue to the next smaller domain.
Eventually a present deleted coordinate supplies a valid message, or R is
contained in the final residual domain and the empty message works. Thus
every realizable R is covered by this one shared decoder. The accompanying
plain-integer check also enumerates all 156 realizable partial samples.

D has VC dimension two: shifting does not increase VC dimension, and the
pair of coordinates 1,2 is shattered, as witnessed by rows 16,2,12,6 for
patterns 00,10,01,11. It cannot have size-zero compression because it has
more than one distinct complete row. Therefore its exact labeled compression
number is one.

## 3. Consequence and exact limit of this obstruction

A theorem claiming that EVERY size-k scheme for a coordinate-shifted class
can always be lifted to the original class with the SAME k would be false:
the displayed shift has k=1 on D, while the original C requires two. This
rules out that unrestricted lifting lemma, even with improper reconstruction
and no computational restriction.

Both classes have VC dimension two. The failed lifting size one is below
that dimension. Consequently this example does NOT refute a more specialized
lifting theorem at k=VC(C), and does NOT refute SC0. It records exactly
where a generic arbitrary-k shifting shortcut breaks; it neither closes
the original universal upper-bound gate nor establishes novelty priority.
