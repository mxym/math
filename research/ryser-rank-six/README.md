# Rank-six Ryser exploration: explicit scope and certificate interface

7 October 2026. This is an exploratory programme, **not a mathematical result or a claimed counterexample**.

The classical intersecting form of Ryser's question asks whether every intersecting r-partite r-uniform hypergraph has a vertex cover of size at most r-1. The pinned OpenAI large-prime construction does not settle rank six. Our target is an explicit six-partite intersecting witness with cover number six, or a structurally meaningful theorem about this rank.

## Current finite model

`search.py` searches hypergraphs with at most q available vertices in each of six parts, and at most N distinct edges; q defaults to six and is set by `--vertices-per-part`. An edge is a six-tuple of labels 0,...,q-1, one per part. N labeled edges are encoded; duplicates allow fewer distinct edges. Labels zero through five in each part are required to occur; remaining labels are optional. This is safe after relabeling: if fewer than six vertices occur in a part, that entire part is already a cover of size at most five.

This is a restriction. A rank-six counterexample could require more vertices per part or more edges. No completeness claim for the unrestricted problem is made.

The first edge is relabeled to all zeros. Two distinct edges in a possible counterexample intersect in some part. Relabeling the parts and unused labels lets us take that part to be zero for edge two, with every other coordinate of edge two either zero or one and at least one equal to one. This symmetry restriction preserves the finite target class.

## Why the lazy constraints are sound

For every edge and part, exactly one vertex label is selected. For every pair of edges, an auxiliary variable records equality in each part; at least one equality is required. Thus every decoded model is intersecting.

The exact recursive cover oracle branches on one uncovered edge. Every cover must select one of that edge's six vertices, so all six branches are explored, with memoization. A degree bound prunes only if the remaining budget times the maximum remaining degree is less than the number of uncovered edges. If a cover of size at most five is found, pad it to five distinct vertices. The added SAT clause requires some edge to avoid all five vertices. Every sought counterexample satisfies this clause, and the current model is excluded. Repeated cuts may be costly; no efficiency theorem is claimed.

If the oracle reports no five-cover, the search independently enumerates all five-vertex subsets of the 6q-vertex universe and checks pairwise intersection before saving an edge list. There are 376,992 subsets for q=6. For publication, the separate standard-library `verify_witness.py` must also accept that list. It does not import the SAT solver or the search oracle. Every cover of size less than five extends to a five-subset of that universe, so this enumeration excludes all covers of size at most five. Because the hypergraph is intersecting, the six vertices of any one edge give the matching upper bound, even when q exceeds six. The finite edge list, not the solver's status, is the candidate certificate.

## Run and validate

Python 3.11 or later:

    python3 -m venv /tmp/ryser-six-venv
    /tmp/ryser-six-venv/bin/pip install -r requirements.txt
    /tmp/ryser-six-venv/bin/python search.py --edges 24 --seconds 240 --output candidate.json
    python3 verify_witness.py candidate.json

Only run the last command if a candidate was produced. A time limit produces no certificate. SAT UNSAT output, without a proof trace and independent trace verification, is also not used as a mathematical nonexistence certificate.

The cover oracle has independent finite regression checks, which require no external Python package:

    python3 -B check_oracle.py
    python3 -B -O check_oracle.py

They compare 320 bounded cases with direct subset enumeration in both q=6 and q=7 universes, verify the order-five affine-plane baseline has cover number five, and check that the witness validator rejects that baseline and malformed or nonintersecting inputs. The independent enumerator also completes all 58,905 four-subsets for the baseline, testing its exhaustive-success path with a known cover-number-five example. The public witness CLI always uses five-subsets. These tests do not prove Ryser's conjecture or solver correctness.

## Recorded exploration

At the pinned python-sat version and q=6, runs with N=24 and N=48, each limited to 240 seconds, examined respectively 1,299 and 533 SAT models. Every model examined had an exact five-cover; no checked counterexample was obtained. These numbers are a dated experiment, not exhaustive counts and not a bounded nonexistence theorem. Timing-dependent model counts need not replay identically on another machine.

A q=7, N=36 run, also limited to 240 seconds, examined 759 models without a checked counterexample. Here q bounds the number of available vertices per part; the hypergraph rank remains six. A variable-shadowing defect in an initial extension was detected and corrected before these recorded runs. The corrected search and cover oracle were checked with both widths.

Next meaningful searches should exploit additional structure, vary the vertex bound, or incorporate certified exhaustive subfamilies. Merely extending an unsuccessful time limit is not evidence of a theorem.

## A concrete barrier to copying the large-prime template

The pinned source uses two split-line slots per direction, each with four designated points. Its compatibility condition says that no chosen split line contains a designated point of another slot. Consequently the 2(q+1) designated four-point sets are disjoint. There are only q² affine points, so necessarily

    8(q+1) <= q².

For integer q this forces q >= 9. In particular, its deterministic four-point, two-slot template cannot be instantiated at q=5 or q=7, even before the analytic threshold is considered.

The source additionally requires every pair of four-element generator-direction sets to intersect in at most one direction. No unordered pair of directions can then occur in two slots. Counting six direction-pairs per slot gives

    12(q+1) <= q(q+1)/2,

and hence q >= 24. This stronger condition is used in the source's selection machinery; the deterministic hypergraph implication expressly does not use it. Removing it still leaves the affine-point barrier above. These are necessary counting conditions for that specific template, not lower bounds on possible Ryser counterexample ranks. A rank-six attack needs a genuinely different configuration or mechanism.

## A different geometric scout

`geometry_search.py` works in the affine plane over F_5 and uses one of two templates in each direction. A triple template splits one line into three singleton blocks and merges two other parallel lines; a pair template splits two lines into two singleton blocks each and merges two of the remaining parallel lines. Both give six blocks per direction. Directions may mix templates. Retained points are allowed to belong to several split lines, but membership must be consistent on every such line. Points outside all split lines are included. Translation normalizes a chosen split in the horizontal and vertical directions to pass through the origin, without restricting the family.

Its explicit constraints preserve pairwise intersection: two retained points on a split line must share a merged pair in another direction. Every decoded model is reconstructed from its geometric choices, checked for intersection, and passed to the same independent cover checker. For the single-triple template in all directions, one run produced nine intersecting models and then solver UNSAT after nine cover cuts. **No proof trace was verified; this remains an exploratory solver outcome.**

Allowing the mixed template produced 18 intersecting models and then solver UNSAT after 18 cover cuts. The input used 33,199 variables and 639,247 clauses. This too is only a solver outcome, not a certified theorem excluding that larger family. No checked rank-six counterexample was produced in either run.

    /tmp/ryser-six-venv/bin/python geometry_search.py --family triple --seconds 240
    /tmp/ryser-six-venv/bin/python geometry_search.py --family mixed --seconds 240

There is a small rigorously excluded subfamily: all six split lines concurrent at one point, with three of their four other points retained on each line. After translation take the point to be zero. Each direction merges two of its four nonzero-intercept lines. There are exactly 6^6=46,656 choices. On a fixed split ray, a pair of retained points gains a common block precisely if some other direction's merged pair contains both points. Thus three retained points are possible only if those restored pairs contain a triangle. Different rays' points already share their unique unsplit affine line, so no missing cross-ray condition is hidden.

`check_pencil.py` exhausts all choices and compares an inverse-coordinate bitmask calculation with a separate forward-coordinate set calculation. In every choice at most five of the six rays admit a triangle; the full histogram is recorded by the checker. Hence this concurrent-line template cannot even produce the required intersecting family, independently of any SAT solver. This exclusion is restricted to that template and does not address unrestricted Ryser rank six.

    python3 -B check_pencil.py
    python3 -B -O check_pencil.py

Source interface: openai/math commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, [Balanced counterexamples to Ryser's conjecture at prime orders](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Balanced-Counterexamples-to-Rysers-Conjecture-at-Prime-Orders-September-27-2026). No correctness assumption on that manuscript is required by our finite search and witness checker.
