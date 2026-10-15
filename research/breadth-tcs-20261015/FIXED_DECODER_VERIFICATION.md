# Verifying a fixed decoder: an exact graph case and a complexity barrier

15 October 2026, Asia/Shanghai. Yongxian Zhang (张永贤), South China
University of Technology. No external funding. OpenAI AI assistants assisted.
Original material all rights reserved; third-party rights retained.

**Status:** an auxiliary written route analysis, with author-only checking.
SC0 is unchanged and unresolved. These statements concern testing a GIVEN
decoder, not whether some size-VC decoder exists. They are not counted as
a new major result, are not asserted to have novelty priority, and have no
independent review or Lean proof. A bounded primary search did not locate
the exact testing statement below; that search is not a priority certificate.

## 1. Exact failure condition for one complete concept row

Fix a finite domain X and one concept c. For each small coordinate set T,
the message labels are c restricted to T, and define its error set

    B_T(c) = {x in X: rho(c restricted to T)(x) != c(x)}.

For a candidate sample c restricted to A, the decoder fails to have ANY
successful size-k message if and only if

    for EVERY T subset A, |T|<=k,  A intersect B_T(c) is nonempty.
                                                        (FV-1)

This is exactly the original whole-sample consistency condition, expressed
with the same single total decoder per message. If the decoder is normalized
to extend its own messages, B_T(c) is disjoint from T. No sample domain is
sent to the decoder in this reformulation.

For k=1, build a directed graph E_c on X with an edge x->y exactly when
y belongs to B_{ {x} }(c). Then a failed domain A exists if and only if
a vertex of B_empty(c) can reach a directed cycle in E_c. Self loops are
allowed if the original candidate decoder is not normalized.

Indeed a failed A meets B_empty(c), and every vertex x in A has an outgoing
neighbor in A, by (FV-1). Following edges from a point in A intersect
B_empty(c) must eventually reach a cycle inside finite A. Conversely the
vertices along such a path and cycle form an A meeting B_empty(c) with an
outgoing neighbor in A at each vertex, so every singleton message and the
empty message fail there. This proves both directions.

One can therefore verify a fixed size-one decoder on EVERY partial sample
of a finite listed class C in polynomial time: build this graph for each
c, find cycle-reaching vertices by strongly connected components or by
repeatedly deleting vertices of outdegree zero, and check their intersection
with B_empty(c). The direct input-table implementation costs O(|C|*|X|^2).
This is a testing algorithm, not a construction of size-one schemes for
arbitrary VC dimension.

## 2. Bounded partial-sample checks can miss arbitrarily long failures

Let n>=3 and let C consist of all n singleton concepts, with VC dimension one. For a
function f:X->X with f(i)!=i, set

    rho(empty)=all one,
    rho({(i,1)})=the i-th singleton,
    rho({(i,0)})=the f(i)-th singleton.

This decoder is normalized and proper on nonempty messages. Every sample
containing a positive label is covered by its positive singleton message,
including every complete concept row. An all-negative nonempty sample on
A is covered if and only if some i in A has f(i) outside A. Thus a failure
is exactly a nonempty proper f-invariant set A.

Choose f to be one directed cycle of length n-1, with the remaining vertex
mapped into that cycle. The smallest nonempty invariant set is its cycle,
of size n-1, and it is a realizable all-negative sample since it omits the
remaining concept's positive point. Every realizable partial sample of
size at most n-2 is nevertheless covered, as are all complete rows. This
gives hidden failures of unbounded sample size already at VC one.

Replacing f by a single n-cycle, and taking the empty decoder to be any
singleton concept, gives a proper size-one scheme: its only
nonempty invariant set is all of X, whose all-negative labeling is not
C-realizable. This familiar cyclic singleton construction is already
given in *Order Compression Schemes* (Darnstaedt et al., ALT 2013,
Example 1); the long-failure version here is just a route control.

## 3. Size-two fixed-decoder testing is coNP-complete, even on a trivial VC-two class

Use explicit tables for the total output on every realizable message of
size at most two. Consider only classes on a core of coordinates plus two
distinguished tag coordinates which are zero on the entire core and take
all four tag patterns. Each such class has exactly four concepts and VC
dimension exactly two. Even on this fixed family of simple classes,
deciding whether a given NORMALIZED decoder with arbitrary improper outputs
allowed covers every realizable sample
is coNP-complete, under the usual explicit finite input encoding.

The complement lies in NP: an uncovered realizable labeled sample is a
polynomial-size witness, and one can check its consistency with the four
rows and test all O(n^2) permitted messages by direct table comparisons.
The following full reduction proves hardness.

Let phi be a 3-CNF formula with v>=1 variables and m>=1 clauses. The core
coordinates consist of

    r;
    anchors a_1,...,a_L, where L=v+m;
    two literal points p_i,q_i for each variable i=1,...,v.

There are N=1+3v+m core coordinates. Interpret p_i in a selected domain
as truth of variable i and q_i as its negation. All realizable core labels
are zero. We specify a normalized decoder for every all-zero core message
T with |T|<=2 by making its one-labeled output coordinates equal to B_T;
all other output coordinates, including both tags, are zero.

* For T=empty, put B_T={r}.
* For singleton T={r}, put B_T={a_1}.
* For singleton T={a_j}, put B_T={a_{j+1}} when j<L, and B_T={r}
  when j=L.
* For a singleton literal point, put B_T={r}.
* For pair T={r,a_i}, 1<=i<=v, put B_T={p_i,q_i}.
* For pair T={r,a_{v+j}}, put B_T equal to the literal points in clause j,
  using p_i for a positive occurrence and q_i for a negative occurrence.
* For pair T={p_i,q_i}, put B_T=empty.
* For any other pair not containing r, put B_T={r}.
* For any remaining pair containing r (so it is {r,p_i} or {r,q_i}),
  put B_T={a_1}.

These cases cover all core messages and are unambiguous. Each specified
B_T is disjoint from T, so its output agrees with the supplied zero labels.
The fixed decoder receives T alone; r, the formula and the anchor identities
are part of the constructed, preconfigured finite table, not side information
sent with a compressed sample.

For a message containing at least one tag literal, define its output to
be zero on the whole core, to agree with every tag literal in the message,
and to be zero on any unsupplied tag coordinate. This also extends its
message. A realizable sample containing one or both tags is always covered
by the message consisting of precisely its tag literals, of size at most
two. Hence every possible failure is a pure-core all-zero sample.

Let A be its core domain. The error set of the empty message forces r in A. The singleton
error sets then force all anchors into A in sequence. Since all pairs
{r,a_i} are active, (FV-1) forces at least one of p_i,q_i into A. Their
own pair has empty B_T, which forbids both being in A. Exactly one is
therefore selected for each variable. The active clause pair
{r,a_{v+j}} forces one of its literal points into A, so this choice is
a satisfying assignment of phi.

Conversely, any satisfying assignment gives a failed domain A by taking
r, every anchor, and exactly its true literal point for each variable.
The empty and singleton constraints hold, each variable and clause pair
has an error point in A, and the forbidden double-literal pair is never
contained in A. All other pairs either have r as an error point or,
when they contain r, have a_1 as an error point. Thus (FV-1) holds for
EVERY eligible message, and the decoder fails. This proves an exact
bijection between satisfying assignments and failed sample domains.

The constructed input has n=N+2=3v+m+3 coordinates and only four concept
rows. There are O(n^2) messages and n output bits per message, so the table
is constructed with polynomial size and time. Its compression bound two
equals the class's actual VC dimension. There is an uncovered sample if
and only if phi is satisfiable, proving NP-hardness of counterexample
existence and coNP-hardness of universal fixed-decoder validity.

The empty decoder of this constructed candidate is deliberately complicated
only by a single core error r. The class itself has an immediate valid
size-two scheme: transmit its tag literals and reconstruct zero on the
core, including for an empty message. Thus testing a bad candidate is hard
while existence for every class in this reduction is easy. The reduction
does NOT establish computational hardness of the existence problem and
does NOT refute or solve SC0. No P-versus-NP separation is claimed.

## 4. Consequence for the finite research controls

The domain-deletion DAG verifier is a correct exact certificate format.
Its certificate need not be polynomial in every possible input decoder.
Indeed if every valid decoder in the preceding explicit-table family had
a polynomial-size such certificate, their coNP-complete validity problem
would belong to NP, implying NP=coNP. This is a conditional implication,
not an assertion of the unresolved separation NP!=coNP.

The mathematical full target has no computational-efficiency condition,
so this barrier cannot be a reason to mark SC0 impossible or abandon it
before the allocated stage. It does explain why whole partial-sample
coverage, explicit certificates and honest solver limits are necessary
when assessing finite research candidates. New major solved results: zero.
