# The complete partial-sample failure formula and the remaining augmentation gate

15 October 2026. Yongxian Zhang (张永贤), South China University of
Technology. No external funding. OpenAI AI assistants assisted. Original
material all rights reserved; third-party rights retained.

**Status:** author-only exploratory mathematics, not a proof or refutation
of SC0, not independently reviewed, and not counted as a new major result.
The formula below describes testing a fixed decoder. The unresolved final
gate still concerns constructing ONE decoder for every VC-d total class.

## 1. Exact finite SAT formula for every possible failure on one row

Fix a listed total concept c on finite X and a proposed decoder rho on
ALL messages of size at most k. For each coordinate x introduce a Boolean
variable z_x, meaning that x belongs to the domain A of a failed partial
sample c restricted to A. For each T subset X, |T|<=k, put

    B_T(c) = {y: rho(c restricted to T)(y) != c(y)}.

Construct the CNF formula

    F_c(z) = AND_{T subset X, |T|<=k}
                 ((OR_{x in T} not z_x) OR (OR_{y in B_T(c)} z_y)).
                                                            (FC-1)

Empty disjunction means false. In particular the T=empty clause demands
A intersect B_empty(c) nonempty. A satisfying assignment is EXACTLY a
failed sample domain: whenever T is contained in A its clause requires
an error coordinate in A, and otherwise the clause is automatically true.
Thus rho covers every realizable partial sample of C if and only if F_c
is unsatisfiable for EVERY c in C. Repeated sample representations by
different c do not change this equivalence. No domain A is given to rho.

The formula has sum_{i<=k} binomial(n,i) clauses and at most
O(n * sum_{i<=k} binomial(n,i)) literal occurrences. At fixed k this is
polynomial in the explicit fixed-decoder input. It does NOT imply polynomial
verification because deciding satisfiability of the resulting clauses can
be hard. For k=1 every clause has at most one negative literal, so the
formula is dual-Horn; its graph form is Section 1 of
FIXED_DECODER_VERIFICATION.md. For k=2 the full coNP-hard testing reduction
in that note supplies normalized clauses with at most two negative literals.

If rho is normalized to extend its messages, B_T(c) is disjoint from T.
Normalization is without loss for the existence question: replacing rho(T)
on T by its supplied labels cannot destroy agreement on any S containing
T. The failure formula therefore contains no hidden properness assumption.

## 2. Scope of a SAT-based finite research verifier

A SAT model of F_c supplies a polynomial-size A which can be checked by
plain integer comparisons against EVERY eligible T. It is a genuine
counterexample to that candidate decoder. An UNSAT solver status needs a
checked refutation to certify coverage on row c; it is not itself a new
mathematical proof of SC0 or a proof of solver correctness. The archived
positive finite controls retain a separately checked domain-deletion DAG,
and also directly enumerate their actual partial samples.

This formulation can accelerate counterexample-guided decoder synthesis
without weakening the original constraints. It does not assume that
checking all full rows, all size-(d+1) samples, or one solver's final status
covers the full partial-sample poset. The long VC-one cycle example in the
fixed-decoder note explicitly excludes any bound on a missed sample's size
which depends only on VC dimension and k.

## 3. A precise one-concept augmentation lemma

Let C' be a finite total class already possessing a size-k decoder rho,
and add one new concept c not in C'. A partial sample S from c is NEW if
it is not C'-realizable. Let E be the inclusion-minimal new samples. Suppose
EVERY T in E has size at most k. For every such T, its labels were not a
legal C' message. Define rho_new(T)=c for these T and leave the old outputs
unchanged on all C'-realizable messages; fill other new messages arbitrarily
while extending their own labels. Then this is a size-k scheme for C' union
{c}: every old sample retains an old successful message, and every new
sample contains a minimal new T in E.

This is a sufficient augmentation lemma, not a consequence of VC dimension.
Already C' equal to the n singletons and c equal to the all-zero concept
has VC one before and after adjoining c, but its unique minimal new sample
is the all-negative sample on all n coordinates. Its size is unbounded.
The enlarged class nevertheless has an immediate size-one scheme, by
empty -> all zero and positive singleton -> that singleton. Therefore a
large minimal new sample does NOT refute SC0; it only shows why a proof
must allow rerouting the old decoder messages, rather than use fresh
messages alone.

A full augmentation proof would have to alter old rho(T) while preserving
coverage of every old partial sample. Whenever an altered message was its
only successful message, that sample must be reassigned, possibly through
a cyclic sequence of changes. An assertion that such rerouting terminates
with size bound d requires an actual VC-based invariant. No such invariant
is proved here. Acyclic teaching orders and arbitrary-size downshift lifting
cannot be substituted: the explicit VC-two controls in the continued notes
already fail those stronger proposed routes.

## 4. What remains open

The finite SC1/SC2 gate remains the simultaneous existence of compatible
outputs for ALL messages of every finite VC-d total class. The conditional
finite-to-arbitrary-domain compactness bridge is available, but has no
universal finite premise yet. Fractional feasibility at k=d is also
unproved here, and the actual relaxation has nonintegral vertices even at
k=d=1. No examined finite positive decoder or testing-complexity barrier
settles those gates. New major solved results: zero.
