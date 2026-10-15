# The complete strong sample compression target: written attempt

15 October 2026, Asia/Shanghai. Yongxian Zhang (张永贤), South China
University of Technology. No external funding. OpenAI AI assistants assisted.
Original material all rights reserved; third-party rights retained.

**Status:** the complete conjecture is not proved or refuted. The lemmas below
are elementary reformulations and route controls, not a major solution and
not claimed to be new. No Lean or independent review is asserted.

## 1. The target is kept unchanged

SC0 is the strong no-side-information labeled compression statement in the
separate map. Reconstruction may be improper. For a finite domain [n], write
a sample as (A,b), where A is a coordinate subset and b:A->{0,1}. Let
K(C) be every restriction of every concept c in C to every A subset [n].
In particular, K contains every realizable partial sample, not just the
complete rows c. A message is a T in K with |T|<=d.

The question is whether one can assign one total Boolean vector h_T to
each small T, using no other data, so that

    every S in K contains some T with |T|<=d and h_T restricted to dom(S)=S.

The full target admits all binary classes of finite VC dimension. Maximum,
ample, oriented-matroid, ordered, stable, and other subclasses do not replace it.
The current primary screen found two superficially matching proof claims
that their current arXiv records explicitly withdraw with proof errors.

## 2. Exact shared-decoder constraints (elementary equivalence)

For every small realizable T and every coordinate x outside dom(T), introduce
one Boolean variable Z(T,x). On dom(T), define h_T to be the labels of T.
For every realizable S, impose the finite formula

    OR over T subset S, |T|<=d of [AND over x in dom(S)\dom(T)
                                  (Z(T,x)=S(x))].                 (SC-1)

The empty conjunction is true. No properness constraint, extra bit,
message order, or access to dom(S) by the reconstructor is present.

If these formulas have a satisfying assignment, define h_T from its variables
and compress S to any witnessing T. Conversely, any compression pair gives
such an assignment after harmlessly modifying h_T on dom(T) to agree with T:
whenever T is an actually used successful message for S, its original h_T
already agrees there. Modifying unused coordinates on unused messages cannot
destroy a successful message. This proves exact equivalence.

For finite [n], (SC-1) is a finite SAT problem. A positive solver output can
be independently checked by enumerating every S and its eligible messages.
An UNSAT report without a proof or a separate mathematical obstruction is
not by itself a publishable refutation. A timeout closes no gate.

## 3. Finite-to-arbitrary transfer, with the shared variables explicit

This is the standard compactness principle attributed in the primary
literature to Ben-David and Litman; the argument is supplied to prevent
silently changing the target.

Assume that every finite-domain binary class of VC dimension e has a
compression scheme of size at most e. Fix arbitrary X,C,d as in SC0 and
introduce the variables Z(T,x) above for every finite realizable |T|<=d and
every x outside dom(T), now allowing X to be infinite. Impose (SC-1) for
every finite realizable S. Each formula uses only finitely many variables.

Take an arbitrary finite batch of these formulas and let U be the union
of their sample domains. U is finite, and the finite class C restricted
to U has VC dimension e<=d. Its assumed finite scheme of size e<=d
satisfies every formula in the batch, by assigning its total-on-U decoder
labels to the variables that occur. Messages that are not used can be
completed arbitrarily. Thus every finite batch is satisfiable. Propositional
compactness supplies a simultaneous assignment for all formulas.

This defines a single total h_T on X for every message T. Choose a witnessing
T for each S, for example using a fixed well-order of all finite labeled
subsets of X. No measurable or effective choice is claimed or required by
SC0. The resulting pair proves SC0 conditional on the finite theorem.
The converse is immediate by specializing X to finite sets. Thus SC3 is a
valid bridge, while the universal finite gate SC1 remains the real problem.

## 4. Complete-row matching leaves the difficult gate untouched

If |C| <= sum_{i=0}^d binom(n,i), assign each full concept c a distinct
coordinate subset I_c of size <=d and use the labeled restriction c|I_c
as its message. Distinct supports guarantee distinct messages; set its
decoder to c. Complete all other message decoders arbitrarily, extending
their input labels. This compresses every full concept row to size d.
Sauer's lemma supplies the displayed cardinality bound when VC(C)<=d.

This argument does not control a partial S that lacks the support I_c.
The missing shared-decoder gate is concrete even for singletons on three
coordinates. Write vectors as their positive-coordinate subsets and take

    C={{0},{1},{2}},  d=1.

Choose h_empty={0}; h_{(i,1)}={i}; h_{(0,0)}={1}; and
h_{(1,0)}=h_{(2,0)}={0}. Every decoder extends its input; every full concept
has its positive singleton as a valid message. But the realizable partial
sample S={(0,0),(1,0)}, whose concept is {2}, has only three permitted
messages: empty, {(0,0)}, {(1,0)}. Their outputs respectively violate
the first, second, first label in S. Hence this full-row code is not a
compression scheme. The class itself is NOT a counterexample: other
decoders solve it, and the finite general model finds one.

A stronger omitted-sample negative control separates the two statements
without relying on a bad arbitrary choice. On seven coordinates, take the
eight concepts varying freely in the first three coordinates and zero in
the remaining four. All eight COMPLETE rows can be encoded by the eight
distinct supports empty,{0},...,{6}, hence by size-one labeled messages.
However no size-one general scheme exists for all partial samples: restrict
to the first three coordinates and their eight complete patterns. There
are only 1+2*3=7 possible labeled messages of size <=1. Each total decoder
can agree with at most one of these eight complete three-bit patterns.
The pigeonhole contradiction is exact. Its actual VC dimension is three,
so this is a test of a false stronger size-one assertion, NOT a refutation
of the size-d conjecture.

## 5. Interval-cover formulation

Regard K(C) as the simplicial complex of realizable signed coordinate sets;
no face contains both signs of a coordinate. An assignment of h_T covers
exactly the realizable faces S satisfying T subset S subset graph(h_T).
Thus SC1 is exactly the existence of a cover of K(C) by one such Boolean
interval per realizable lower face T of size <=d. The upper graph may be
improper. Requiring disjoint intervals, requiring upper graphs to belong
to C, or requiring a globally acyclic order would strengthen the problem.
None follows automatically from VC dimension, and none is assumed here.

One can choose schemes separately for every projection C|U, but shared
messages occurring on multiple U must define compatible total hypotheses.
Their independent existence alone does not construct that compatibility.
The compactness proof in Section 3 succeeds only after the full finite
SC1 theorem is established; it cannot manufacture that theorem from
complete-row cardinalities.

## 6. Current unclosed gates

The exact finite constraints and infinite compactness bridge are in hand.
There is no construction or nonconstructive proof satisfying all finite
instances of (SC-1), and no legal counterexample to size VC(C).
Any further finite search and restricted-route obstruction will be labeled
with its actual finite or conditional scope. New major results remain zero.
