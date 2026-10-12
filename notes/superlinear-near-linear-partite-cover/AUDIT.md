# Verification scope and dependencies

`paper.md` gives the complete deduction. Its sole external theorem is
Kahn's small-codegree edge-colouring theorem, stated in Kang--Kelly--Kühn--
Methuku--Osthus, Theorem 3.1. Section 1.2 of that primary manuscript explicitly
permits parallel copies; degrees and pair codegrees count their identities.
The statement, fixed-rank quantifiers and convention were checked directly.
`results/source.txt` records the downloaded manuscript hash. No degree-three
preprint lemma or OpenAI/math theorem is used by this note.

Peeling, pair-excess deletion and the matching/star framework have explicit
precedents in Sivashankar Section 4. The new arbitrary-degree replication
aligns the weighted colour-class saving, copied degree and distinct-block
star. Its general scalar square yields unbounded fixed-parameter lower
coefficients, hence a superlinear edge conclusion for near-linear families.
This is one programme continuing the earlier finite and asymptotic notes;
their frozen packages remain unchanged.

Self-review covered auxiliary versus original edge deletion, original
repeated blocks, the upper bound on each lost weight, replication only
after obtaining a linear original-block graph, codegrees of copies,
distinct original vertices in each matching, selecting each original
star block once, weighted colour-class averaging, the small-degree case,
the degree-one incidence sign, all pairing ceilings, empty residuals,
negative target values, constants independent of rank, and the fixed-D
order of limits. Letting D vary with rank is not asserted by the proof.
The bounded-budget corollary instead fixes D=ceil(2(C+1)^2) for each
fixed C and rearranges the same inequality; its rounding and constants
are written explicitly.

Six Lean exports verify the denominator-cleared general square, its
implication under z²=2D and D>0, matching/star algebra, quadratic error
comparison, error scaling and final peeling algebra. The particular root
and the combinatorial reduction are justified in the text. The finite
hypergraphs, replication construction and published colouring theorem
are not formalized in these scalar exports. Only propext, Classical.choice
and Quot.sound occur in their recorded axiom lists.

The standard-library checker verifies 61 denominator-cleared polynomial
identities coefficientwise, damaged identities, earlier exact constants,
and 270 exhaustive small-family replication cases plus finite-field and
duplicate-block examples. It independently counts copy incidences and
checks their alignment with distinct-block stars; wrong multiplicity data
must be rejected. A constructed proper colouring checks weighted class
averaging without assuming Kahn's colour-count bound on finite examples.
All arithmetic is integer/rational; no numerical evidence is used as a
general theorem. These are diagnostics accompanying the written proof.

`verify.py --lean` checks the 17-file frozen payload, ordinary and Python -O
replay, Lean kernel replay and exact printed-axiom agreement. PDF builds
reject overfull material. Hashes verify integrity, not correctness. The
separate requested Luna agent performed a limited literature comparison;
it did not review the proof or establish priority. No external mathematician,
human peer review, full formalization, explicit superlinear rate or
unrestricted major-conjecture resolution is claimed.
