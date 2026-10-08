# Independent audit of the complete C17 Lean counterexample

Date: 2026-10-08 (UTC).

## Verdict

**PASS: the reviewed Lean statements and proofs cover the genuine cycle C17, its proper-coloring count for every natural number of colors, the uniquely determined chromatic polynomial, its absolute coefficients, the exact negative third log-concavity iterate, and the resulting disproof of the universal conjecture. No mathematical gap was found.**

**PASS: the supplied fresh-build and empty-kernel replay records are internally consistent, with independently recomputed manifests, declaration inventories, dependency closures, root counts, axiom sets, and source/reference bindings.**

This audit is a source-level semantic and static evidence review, plus independent integer arithmetic. It did **not** install Lean, execute Lean, rerun the supplied verifier, or independently reproduce the recorded fresh compilation/kernel replay. Those execution results belong to the supplied verification run. No repository or release was modified.

The verdict is restricted to **C17 with endpoint-retaining zero extension**. It does not upgrade C12, the family of all cycles with n >= 17, the complete cycle classification, or an endpoint-deleting variant to Lean-verified results. It also makes no novelty, publication-priority, peer-review, or author-acceptance claim.

## 1. Identified input and fixed mathematical reference

- Input: `chromatic_c17_lean_evidence_20261008_public.tar.gz`, 1,417,848 bytes.
- SHA256: `3abea26096508a6a12a87eea65785bb37e7656fd13d496d6900e2f2d7c699617`.
- The package-level manifest covers all 74 other files, without omissions, duplicate paths, absolute paths, or parent-directory traversal.
- The fresh-verification manifest covers its 33 evidence files. The reference manifest covers 12 files, and its nested independent-audit manifest covers four files.
- All 13 reference-file Git blob IDs and sizes were independently compared with the live tree at [the frozen mathematical commit](https://github.com/mxym/math/tree/2b73cde3ae77ab1227c7386e9e82d0e815f21e88/notes/chromatic-infinite-logconcavity-counterexample). Their SHA256 values also match the recorded download manifest. The main proof is byte-identical to the supplied earlier local mathematical proof.
- All three final source modules are byte-identical to their fresh-run snapshots and match `verify.json`, `input.json`, and `RESULT.json`.

The source identities are:

| Module | SHA256 |
| --- | --- |
| CycleColoring | 20eefbdea41e2536b880e4fa95c2a1b11f90b219c2290d48a23d242ebc8f55b0 |
| ChromaticPolynomial | ae0f2368f777b627b58a50dfa82a7e83c7b91689cc79abb38051708b530f781b |
| LogConcavityCounterexample | ca54e13b77d45246025af94da022e8455368a27f3c869ab59e9f83e911fee6d3 |

## 2. The graph and coloring objects are the standard ones

`ChromaticC17.C17` abbreviates `SimpleGraph.cycleGraph 17`; it is not an unrelated graph merely given a suggestive name. The pinned mathlib definition has vertex type `Fin 17` and adjacency precisely when either modular difference is one. Under the natural representatives 0,...,16, its unordered edge set is

    { {0,1}, {1,2}, ..., {15,16}, {16,0} }.

Consequently the graph has 17 distinct edges, no self-loops, exactly two neighbors at every vertex, and includes the closing edge. An independent finite check compared the modular relation with this conventional edge set. This is a direct equality of the customary labeled presentation, so an additional isomorphism to a second arbitrary representation is unnecessary. The Lean theorem `cycle_connected` separately obtains connectedness from the standard mathlib theorem.

`SimpleGraph.Coloring` is mathlib's homomorphism into `completeGraph`, whose validity condition is unequal colors on adjacent vertices. Its finite cardinality counts color functions with labeled colors, not colorings modulo color permutation or graph rotation.

The essential bijection is fully proved:

- `coloringWalk` traverses vertices 0,1,...,16,0 and uses the coloring's actual adjacency-validity proofs for all 17 edges.
- `loopColoring` reads vertices of a closed length-17 walk in the complete color graph. It handles `i = 16` separately, using the walk endpoint to prove the wraparound condition. For other vertices, `Fin` addition is shown to agree with ordinary successor.
- `proper_of_successor` proves that these successor inequalities cover both orientations of every cycle edge.
- `coloringEquivLoops` proves both inverse laws. The reverse direction destructs a length-17 walk and excludes every shorter or longer length; it is not merely an injection.
- `coloring_card_eq_trace` applies the bijection, sigma-type cardinality, and the genuine matrix-power walk-count theorem.

The four relevant mathlib files were fetched once at commit `d13f23b723b8a846827a245b89c10fc7d3f11612`. Their Git blob hashes and complete-file SHA256 values match the package's pinned excerpts. These include [CycleGraph](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Combinatorics/SimpleGraph/CycleGraph.lean), [Coloring/Vertex](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean), [AdjMatrix](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Combinatorics/SimpleGraph/AdjMatrix.lean), and [Polynomial/Roots](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Algebra/Polynomial/Roots.lean).

## 3. The polynomial bridge is an all-q counting theorem

`IsChromaticPolynomial G P` explicitly means

    for every q : Nat, P.eval (q : Int) = card (G.Coloring (Fin q)).

It is not defined by a closed formula, a finite sample of evaluations, an assumed recursion, or a name-only predicate.

Writing J for the all-ones q-by-q integer matrix, the source proves J*J=q*J and inductively establishes

    A^n = t(q,n) J + (-1)^n I,
    q*t(q,n) = (q-1)^n - (-1)^n,

where A is the complete color graph's actual adjacency matrix. Taking traces yields

    trace(A^n) = (q-1)^n + (q-1)(-1)^n.

There is no division by q or assumption that q >= 2. This matters for the empty color set and the one-color case. The formulas are valid even for the empty matrix; at q=0,n=0 the two terms cancel, and at n=17 the evaluation is zero for q=0,1,2. Thus none of these boundary cases is omitted or silently extrapolated.

`cyclePolynomial_isChromatic` combines that result with the actual coloring-cardinality theorem and proves the all-q law for the genuine integer polynomial

    cyclePolynomial = (X-1)^17 - (X-1).

`IsChromaticPolynomial.unique` uses the injective embedding of the natural numbers in the integers and the infinite-evaluation uniqueness theorem for polynomials. Therefore any integer polynomial satisfying the same C17 coloring law must be this one. `every_C17_chromatic_polynomial_fails` explicitly transports the conclusion through this equality.

A general existence theorem for the chromatic polynomial of every graph is not needed for the counterexample: the actual C17 witness and its counting law have already been supplied. Likewise, a single graph on `Fin 17` is enough to refute the universal claim over finite graphs, without formalizing a universal graph-relabeling theorem.

## 4. Coefficient and iteration conventions agree with the intended conjecture

The primary target is [Amdeberhan–Moll, Conjecture 21](https://combinatorialpress.com/article/ojac/vol17/305.pdf), page 9. It concerns absolute coefficients of every chromatic polynomial. Its preceding page defines that polynomial by proper-coloring counts and explicitly includes cycles. The journal introduction has a concave/convex wording inconsistency. [Amdeberhan v7, Section 13](https://arxiv.org/pdf/1207.4045v7), page 14, specifies nonnegative positive iterates and the left zero boundary; its Conjecture 13.1 is the earlier formulation. [Brändén](https://arxiv.org/pdf/0909.1927), page 2, gives the endpoint-retaining operator on the full finite index set with both external neighbors zero. These sources were directly rechecked in this audit.

The formalization uses:

- `absCoefficients P k = |P.coeff k|` over integers, indexed by polynomial degree.
- The true binomial coefficient formula for all k, not a detached coefficient list.
- A proof that coefficients vanish for k>17.
- `logConcavityOp a k = a(k)^2 - previous(k)*a(k+1)`, with `previous(0)=0` and `previous(k)=a(k-1)` for positive k.
- Ordinary repeated application of this operator; no absolute value or truncation is inserted after a transform.
- A proof that every iterate retains the zero tail beyond degree 17.
- `InfinitelyLogConcave a` quantifying over all positive iteration counts and all natural indices.

The lack of an r=0 requirement is harmless here because all initial absolute coefficients are already nonnegative. The finite sequence has the same values as its zero extension at every round. Ascending rather than descending coefficient order is also harmless: reversal commutes with this symmetric, endpoint-retaining operator. The initial constant coefficient zero is retained; deleting endpoints at each iteration is a different convention and is explicitly outside the Lean scope.

## 5. Exact certificate and final conclusion

The first six absolute coefficients are

    0, 16, 136, 680, 2380, 6188.

The relevant first-transform entries are

    0, 256, 7616, 138720, 1456560.

The next entries at indices 1,2,3 are

    65536, 22491136, 8150077440.

Thus the exact final calculation is

    22491136^2 - 65536*8150077440 = -28272276537344.

`third_iterate_value` proves this equality from the actual polynomial coefficients using kernel-checked arithmetic proof construction. `cyclePolynomial_not_infinitelyLogConcave` specializes the putative nonnegativity property to r=3,k=2 and derives a contradiction. `explicit_counterexample` includes connectedness, the chromatic counting law, and strict negativity. The final theorem substitutes this genuine witness into the universally quantified conjecture.

As an independent arithmetic cross-check, this audit enumerated all 131,072 subsets of the 17 conventional cycle edges, computed their component counts by disjoint-set union, and recovered all 18 signed coefficients by inclusion-exclusion. Their absolute values and all four complete iteration rows agree with the frozen certificates. A separate fixed-start coloring dynamic program also matched polynomial evaluation at q=0,1,2,3,4,5,17. These finite checks corroborate the source review; they are not offered as the proof for all q.

## 6. Complete declaration and closure coverage

The inventory contains 98 declarations belonging to the three source modules:

| Module | Declarations |
| --- | ---: |
| CycleColoring | 33 |
| ChromaticPolynomial | 21 |
| LogConcavityCounterexample | 44 |

Independent source parsing identified all 41 explicit declarations. Every one appears in the inventory, leaving 57 generated or auxiliary declarations. The inventory is based on module ownership rather than a user-supplied list of theorem names, so generated/private declarations are not excluded by name filtering.

The supplied closure has 10,964 unique nodes. The audit recomputed reachability from every owned declaration using the union of type, value, and structural dependencies. All edges terminate inside the graph; the whole graph is reachable from the owned set. The edge lists contain 78,851 type references, 138,852 value references, and 11,417 structural references. The union reachable from the five requested roots has 10,929 nodes.

Independently recomputed individual root counts:

| Root | Closure nodes |
| --- | ---: |
| explicit_counterexample | 8,828 |
| chromatic_infinite_logconcavity_conjecture_false | 8,355 |
| cyclePolynomial_isChromatic | 7,831 |
| every_C17_chromatic_polynomial_fails | 10,601 |
| third_iterate_value | 6,947 |

There are no owned axioms and no unsafe or partial declarations in the owned set or its closure. The only closure axioms are `propext`, `Classical.choice`, and `Quot.sound`. For each of the 98 owned declarations, the recorded axiom list exactly matches the independently traversed graph's reachable axioms. The violation and source-token-scan reports are empty. All roots are owned theorems.

The source's two recursive mathematical definitions are noncomputable; this suppresses unused executable auxiliaries while retaining their ordinary logical definitions and equations. The earlier failed run is distinguished in the record and is not used as evidence for the final source bytes.

## 7. Fresh compilation and trust-zero replay evidence

The supplied run is identified as `20261008T112728Z-31290fd6`. Its eight recorded commands comprise three fresh compilation commands, three dependency reports, one all-owned audit/replay, and one invalid-proof control. Every command records exit code zero; timing is ordered consistently. The three compilation logs are empty, and their six `.olean`/`.ilean` outputs are present and hash-bound.

Static inspection of the driver establishes that it:

1. Checks pinned Lean and package commits, tracked-tree cleanliness, and all input source hashes.
2. Creates a unique run directory with `exist_ok=False`, snapshots the sources, and puts that fresh build directory first in a reconstructed `LEAN_PATH`.
3. Compiles each owned module in dependency order without copying old owned outputs.
4. Records direct dependency paths; owned imports in these records point to the same run's fresh build directory.
5. Instantiates the checker from the supplied template, executes it, then performs the negative control and final source-stability/cache checks.

The instantiated checker matches its template and requested modules/roots exactly. Its source and the driver/negative-control sources match their recorded control hashes. The interface-print command also used the same fresh search path and recorded success.

The checker starts from `mkEmptyEnvironment 0`, checks that its constant map is empty, then replays the full all-owned closure into that kernel environment. The pinned upstream `Environment.lean`, `Replay.lean`, and `FoldConsts.lean` were reused from earlier hash-verified audit copies rather than downloaded again. They confirm that the empty environment initializes an empty constant map and the requested trust level; replay submits definitions, theorems, opaque declarations, and inductive blocks to `addDeclCore`; constructors and recursors are checked against those regenerated from inductives. Constant discovery includes types and opaque values. Additional structural dependencies cover mutual blocks, constructors, recursors, and quotient prerequisites.

Two safeguards are important:

- Replay itself skips unsafe/partial constants and can admit axioms. The external preguard rejects unsafe/partial nodes and all unapproved axioms **before** replay. Accordingly replay is not misrepresented as an axiom whitelist.
- The checker verifies that every original closure node exists after replay with matching type and universe parameters. The recorded success marker agrees with the summary's 10,964 nodes and trust level zero.

The negative control constructs a purported proof of `False` using `True.intro`. Its source demands a kernel type-mismatch rejection, rather than accepting an arbitrary failure. The log contains precisely that rejection and the expected success marker. This is a meaningful sanity check, not a demonstration that every conceivable malicious input is handled correctly.

## 8. Public projection and remaining trust limits

The public profile identifies two transformed environment-configuration files. Their declared original SHA256 matches an independently available original configuration from the earlier verification audit. Comparing the JSON objects confirms that the public version only removes the two internal coordination-ID fields; every operational configuration value is unchanged. Both transformed public hashes and their enclosing regenerated manifests match. No occurrence of either removed identifier value remains anywhere in the package.

The original unmodified execution archive was not supplied to this audit. Therefore the public profile's claim that all other original-archive members are unchanged is not independently established by a raw-versus-public archive diff yet. This is an archive-provenance limitation, not a missing mathematical proof: the public package independently contains and consistently binds all reviewed proof sources, outputs, controls, and logs. A later final-copy gate can compare the raw archive or a proposed publication copy without rerunning Lean.

Other explicit trust boundaries:

- The recorded shared-cache check compares file paths, sizes, and modification timestamps. Its unchanged result does not cryptographically authenticate every cached file or rule out changes that preserve those metadata.
- Tracked package source pins and reviewed source excerpts are verified; this audit did not rebuild or independently authenticate the entire dependency-cache/toolchain supply chain. As usual, the interpretation of source and stored proof terms relies on that pinned environment and its transparent execution record.
- The JSON graph and replay logs are execution evidence reviewed here, not a second independently implemented proof kernel. The trusted base includes the pinned Lean kernel, its runtime/compiler, and the audit infrastructure that extracts and submits terms.
- Machine success does not resolve semantic correspondence by itself. Sections 2–5 provide that separate review.

## 9. Reproducible audit artifacts

- `audit_record.py`: independent standard-library static checker and exact C17 reconstruction; never runs Lean or the supplied verifier.
- `static_audit_result.json`: machine-readable counts, hashes, edge checks, and arithmetic results.
- `live_reference_tree.json`: independently retrieved fixed-commit reference tree.
- `upstream/`: the four newly needed pinned mathlib sources and their Git metadata.
- `AUDIT_REPORT.md`: this report.

The checker completed successfully. No blocking defect was found in the C17 proof or the provided verification record.
