# Full target fixed before own mathematical stage

15 October 2026, Asia/Shanghai. Author-only exploration; no solved result.

## SC0: original strong target, all objects and quantifiers

For every set X, every nonempty binary concept class C contained in {0,1}^X,
and every finite integer d=VC(C), there exist functions kappa and rho such that:

* Every finite C-realizable labeled sample S is a finite graph of a partial
  function X -> {0,1}, with S contained in the graph of some c in C.
* kappa(S) is a labeled subset of S and has cardinality at most d.
* rho takes only that labeled subset, with no side bits, order, multiplicity,
  sample size, sample domain, random seed, or further message. It returns one
  total Boolean hypothesis on X. Improper output, outside C, is allowed.
* rho(kappa(S)) agrees with every label in S, for EVERY such finite S.

No polynomial running-time or measurability requirement is imposed on these
set-theoretic functions. The empty class has no nonempty realizable target
and can be treated vacuously; for d=0 a single fixed concept suffices.

This is the strong **size d** formulation. Size O(d), size exponential in d,
bounded finite instances, unlabeled codes, extra bits, stable/order-restricted
schemes, maximum/extremal classes, or particular geometric families do not
prove SC0. A refutation must give a genuine C for which NO such general
labeled improper pair of size d exists. Merely defeating an explicit
candidate decoder, an ordering, an embedding, or a stronger proper variant
does not refute SC0.

## Gates kept separate

SC1 (finite core): all finite X and every C subset {0,1}^X admit the same
size-VC(C) no-sidebit scheme. A universal combinatorial construction or
nonconstructive existence proof must satisfy every partial sample, not just
complete concept rows.

SC2 (decoder compatibility): for all small messages T, choose a SINGLE total
hypothesis h_T so that every realizable S contains some T of size <=d with
h_T extending S. Individual injective row representatives, matching counts,
or separate schemes for every projection do not by themselves supply these
shared h_T.

SC3 (finite-to-arbitrary transfer): if SC1 is proved for all finite instances,
use a precise compactness argument to obtain SC0, without adding side bits
or demanding compatible choices from an unjustified inverse limit.

SC4 (legal refutation): a finite exact unsatisfiability certificate for the
general decoder constraints would refute SC1 and SC0; a restricted algorithm
or finite search without a counterexample closes no gate.

## Starting routes and their boundaries

Try a direct extension-compatible assignment of decoder hypotheses, using
the full partial-sample poset. Track exact finite constraints, possible
orientations/discrete Morse matchings, and the source of nonlocal conflicts.
The known exponential blow-up in extremal embedding means a universal
same-d extremal-superclass shortcut is unavailable. The complete target is
not replaced by proving a theorem about another class or another parameter.

Known published principles (finite compactness, Sauer counting, standard
subclass constructions) must be attributed and not counted as new major
results. Current bounded primary search is recorded separately; two matching
sample-compression preprints are explicitly withdrawn with proof errors.

The active complete stage receives approximately 7200 EFFECTIVE research
seconds, excluding real preservation, disconnected context recovery and
idle intervals. A single failed shortcut, finite control or no-result
search is insufficient grounds for an early switch. No other complete
target is silently activated. No Lean/audit expansion or external
publication action is part of this written-only stage.
