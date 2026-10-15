# Finite coverage certificates and the unchanged universal gate

15 October 2026, Asia/Shanghai. Yongxian Zhang (张永贤), South China
University of Technology. No external funding. OpenAI AI assistants assisted.
Original material all rights reserved; third-party rights retained.

**Status:** exploratory written mathematics. No proof or refutation of SC0,
no new major solved result, no Lean or independent review. The finite
decoder probes below never replace the full target by a restricted model.

## 1. A finite domain-deletion certificate is exact

Fix a listed finite class C on X=[n], a size bound k, and a single fixed
decoder h_T on every realizable labeled T of size at most k. A certificate
node is a realizable sample S=(A,b), together with a message T subset S,
|T|<=k, for which h_T agrees with every label of S. It has one child

    S minus {(x,b(x))},  for EVERY x in dom(T).

These children have strictly smaller domains. If T is empty, the node has
no children and is a leaf. One root is required for every complete concept
row of C. A finite directed acyclic graph sharing identical sample nodes
is allowed, with all indicated children present.

Such a graph proves by induction that every labeled subsample of every
root is correctly compressed by the same decoder. To see this at one node,
let R be a labeled subset of S. If T subset R, h_T is correct on R. If not,
there is an x in dom(T) absent from R; then R is a subset of the indicated
child, and the induction hypothesis applies. This covers every R, not just
the roots. The decoder receives only the chosen T; it never receives the
path, the root, the original domain, a sample size or any extra bit.

Conversely, if h_T covers every partial sample, such a finite certificate
always exists: at each node choose any successful T and recurse on its
specified smaller children. Finite domain size guarantees termination.
Thus this certificate format is exact for a FIXED finite decoder. Its DAG
acyclicity is the automatic strict decrease of the sample domain; it puts
no acyclicity or order condition on the hypothesis compression graph.
Conflating these two graphs would reintroduce the false stronger route.

## 2. Counterexample-guided finite synthesis

The discovery code uses the full shared-decoder Boolean constraints from
the initial manuscript. It starts by constraining complete rows, obtains
a decoder candidate, and tries to build the certificate above. At a node
S it searches ALL eligible messages. If none succeeds on S, that precise
S is an actual failed realizable sample and is added to the shared SAT
constraints. The candidate decoder is then recomputed. No used sample is
deleted or made available as an auxiliary reconstruction message.

If this process reaches a valid certificate, a separate checker using only
plain integer masks checks every decoder message, every reachable node,
every indicated child and every root. The inductive argument in Section 1
then supplies every partial sample of the listed class. This avoids treating
a solver's internal satisfaction report as coverage of unenumerated samples.
For small cases a second direct enumeration checks every actual partial
sample and cross-checks the certificate verifier.

If a finite search times out, reaches a round cap, or returns unknown, the
instance stays open in that run. An UNSAT solver report is not a certified
counterexample without an independent refutation. Each iteration does
eliminate its particular bad decoder, but elimination of candidates gives
no uniform rate or theorem for all finite classes.

For every finite instance the unconstrained logical process terminates in
principle if an exact complete SAT procedure and unlimited resources are
available: either a valid decoder is found or an unsatisfiability proof can
eventually be sought after finitely many distinct partial-sample constraints.
This finite brute-force fact is not a proof of which result occurs and
does not close SC1.

## 3. A useful local span fact still has a sign gap

For a sample S on A, write chi_S(c)=1 if c extends S and zero otherwise.
VC(C)<=d implies that chi_S, as a real function on C, is a linear
combination of indicators chi_T with T subset S and |T|<=d. In particular,
the span statement retains the labels and supports of the original sample.

Here is a complete elementary proof. For i in A put

    y_i(c)=1 if c(i)=S(i), and 0 otherwise.

Then chi_S is the monomial product_{i in A} y_i. For any B subset A of
size d+1, there is a missing pattern epsilon in {0,1}^B, by the VC bound
after these coordinate label flips. Its indicator

    product_{epsilon_i=1} y_i * product_{epsilon_j=0} (1-y_j)

vanishes identically on C. Its expansion has coefficient +1 or -1 on
the full monomial y_B, and all other terms have smaller degree and support
within B. Solve for y_B. Multiplying by the other y variables and repeatedly
using this identity reduces every monomial of degree greater than d.
Each final monomial y_U is exactly chi_{S restricted to U}, proving the
assertion, including the constant term for an empty message.

This local span fact does NOT give a decoder. Coefficients may be negative.
They cannot in general be made all nonnegative. For example let C consist
of the co-singletons X minus {i}, with VC one, and let S give positive
labels on a proper set A with |A|>=2. Every chi_T for a singleton positive
T subset S is nonzero on concepts outside V_S, while chi_S is zero there.
A nonnegative sum of those indicators and the nonnegative constant cannot
cancel the outside support. At least one nonzero term would create an
outside positive value, a contradiction.

For two positive coordinates i,j the exact identity is simply

    chi_{i=1,j=1}=chi_{i=1}+chi_{j=1}-chi_empty,

because the co-singletons never realize two simultaneous zeros. The negative
coefficient is essential. A rank argument or a positive-mixture argument
that silently replaces this signed identity by a nonnegative cover would
not prove the original theorem.

Likewise the evaluation matrix of all low-degree sample indicators has full
row rank, but assigning each indicator column to the first or last concept
in a fixed order gives an order decoder. The verified VC-two Warmuth class
excludes a universal size-d conclusion for that construction. Linear rank
and row matching do not by themselves resolve the shared decoder gate.

## 4. Reduction to maximal classes keeps the full target, but does not solve it

For finite X, any VC-d class C is contained in an inclusion-maximal VC-d
class D, by successively adding allowable rows until none remain. A
size-d possibly improper scheme for D restricts to one for C. Consequently
it suffices to prove SC1 for all such maximal classes; this is a legitimate
reduction and makes no same-d maximum/extremal embedding assertion.

A maximal D is determined by its forbidden (d+1)-coordinate patterns.
Indeed if a missing row u had every (d+1)-coordinate restriction already
realized by D, adding u could not shatter any (d+1)-set and would preserve
VC dimension at most d, contradicting maximality. Thus u is excluded by
one forbidden local pattern. Conversely every row in D satisfies all of
these exclusions. These constraints may exclude more than one pattern on
the same (d+1)-set, and consistency of their conjunction is not a compression
scheme. The discovered greedy maximal finite classes are only probes of
this reduced full gate.

## 5. Universal short-sample coverage and an actual global barrier

The fixed default-label decoder from the continued notes works on ANY
domain X for every binary sample with at most 2k+1 examples, k>=2. The
proof only used the number of positives and negatives, not the size or
identity of X. In particular there cannot be an unsatisfiable size-k
decoder core consisting solely of samples of size at most 2k+1.
This does not cover longer samples of a VC-k class.

There is a sharp domain-uniform obstruction to extending this particular
universal short-sample statement by one example. For any k>=1, no single
size-k no-side-information decoder on an infinite domain can cover EVERY
binary sample of size 2k+2. This is a statement about the unrestricted
bounded-sample task, not a counterexample to SC0 for a fixed total VC-k
class. It also explains why one finite small-domain decoder cannot simply
be copied to arbitrary projections sharing the same messages.

It suffices to work on N. For each t=0,...,k, color every increasing
(t+1)-set by the finite vector of decoder predictions at the omitted point,
over all choices of its position and all 2^t labelings of the remaining
t-point message. There are at most

    q_t = 2^((t+1)*2^t)

colors. Repeated applications of the infinite Ramsey theorem, once for
each t, give an infinite H on which all these colorings are homogeneous.
Thus for any labeled message T subset H with |T|=t, the prediction at a
point x in H outside T depends only on its ordered position relative to
T and the ordered labels of T. In particular all x in the same one of
the t+1 open order regions have the same predicted label. This is a
consequence of homogeneity of an arbitrary decoder, not an assumed
restriction on its original behavior.

Now choose 2k+2 points of H with alternating labels. For any permitted
message T of size t<=k, at least 2k+2-t points remain in t+1 regions.
Since 2k+2-t>t+1, one region contains two consecutive remaining sample
points. There is no retained point between them, so one can choose them
consecutive in the original sample, and their labels are opposite. The
decoder is constant on that region and must get one of them wrong.
This holds for every T, including the empty message, and gives the claimed
failure of the universal length-(2k+2) task. For k>=2 the length-(2k+1)
positive construction and this negative argument meet exactly. For k=1,
the full cube on three points already rules out universal size one by
the elementary eight-rows versus seven-messages count; size two samples
do have an order-threshold size-one scheme.

One can apply the SAME argument to a legal total-class lower bound. Let

    C_d = {1_A: A is a finite subset of N, |A|<=d}.

It has VC dimension d and admits a size-d scheme by transmitting all
positive examples and decoding zero elsewhere. If k<d, the alternating
sample above has k+1<=d positive labels and is C_d-realizable, so the
argument rules out size k. This recovers the known sharp worst-class
lower bound for labeled compression. Sharp worst-case lower bounds and
sufficiently-large maximum classes were already studied by Floyd and
Warmuth (1995); this argument is not claimed as a new major result.
It establishes the necessity of d in the worst case, and leaves the
universal upper bound at d entirely unresolved.

The conclusion can also be made finite by replacing successive infinite
Ramsey applications with finite Ramsey numbers and choosing a domain large
enough to leave a homogeneous set of size 2k+2. No practically useful bound,
new finite minimal threshold, or exhaustive class search is claimed here.

## 6. Remaining original question

None of the complete finite certificates, local span identities, maximal
class reductions, known worst-case lower bounds or restricted-route controls
chooses a working decoder for every total VC-d class on arbitrary finite
domains. SC1/SC2 remain open in this research packet; SC3 is the already
proved conditional compactness bridge. No finite failure of size d in the
general model has been certified. New major solved results remain zero.

## 7. An additional lifting gap in recursive induction

Suppose a size-d decoder has been obtained for U=C_0 union C_1 on the
remaining coordinates. If every reconstructed h_T belongs to U, one may
lift it by a split label for which it belongs to C_b. If this lift gets
the original split label wrong while agreeing with a sample S' on the
remaining coordinates, then S' is realized on both split sides and is an
ambiguous partial sample. This is a valid observation under the stated
properness assumption on the U decoder.

If h_T is improper for U, it need not belong to either child, so this
argument cannot be used. A sample it matches on the other coordinates
need not become ambiguous when a freely assigned lift label is wrong.
The general target permits improper schemes, and an induction that assumes
only their existence therefore has not supplied this properness premise.

One also cannot silently demand a proper size-(d-1) ambiguity decoder into
both children. A concrete obstruction occurs even at d=1. Take the parent
class to be all singletons on n+1 coordinates, n>=2, and split off one
coordinate. Then C_0 consists of all singletons on the remaining n points,
while C_1 contains just the all-zero row. The ambiguous samples are all
negative samples omitting at least one remaining point. Their VC dimension
is zero, and an improper size-zero decoder exists: the all-zero row.
However a size-zero decoder whose output must belong to C_0 is impossible.
Its sole output would be a singleton {j}, and the realizable ambiguous
sample {(j,0)} would contradict it. All these statements concern the
explicit stronger intermediate properness requirement; the parent class
itself has a valid general size-one scheme.

Thus even a positive universal size-(d-1) ambiguity theorem, if it only
promised improper outputs, would not complete that proper recursion without
another argument. The original global shared-decoder compatibility problem
has not been removed.
