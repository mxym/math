# Hydrological tree identifiability — partial Lean formalization

**Partial formalization. The all-tree Jacobian theorem, the conjecture
corollaries, the positive singular-locus classification, and complete positive
realization/fiber count are NOT yet proved by this Lean package.**

## Actual proved core

`Gluing.lean` proves the actual Frechet derivative of the map

    (U,V,R,S) -> (UV, R V + U S)

in finite-dimensional real polynomial coefficient spaces, where U and V are
monic and R,S have the corresponding strict degree bounds. Its actual Jacobian
is `resultant U V m n ^ 2`. The off-diagonal derivative terms are derived, not
assumed. All degrees and all coefficient values are quantified, including zero
degrees, common roots, and zero resultants.

`Scaling.lean` proves that the actual map `(c,F) -> c F` for monic degree-n F
has coefficient Jacobian `c^n`, including c=0. `RootUpdate.lean` proves that the
actual coefficient operation `P=(X+d)F-N` has Jacobian `(-1)^n` in the specified
coefficient order. It also proves monicity, exact degree, and full polynomial
reconstruction. `LeadingCoefficients.lean` establishes the exact coefficient
isomorphisms, rather than postulating a coefficient-model identification.

The entry module is `HydrologyTree.lean`. These are proof-critical algebraic
steps of the manuscript, not the final tree-compartment theorem. The connection
to the actual tree characteristic/cofactor determinant and arbitrary-arity tree
induction remains explicit in `DEPENDENCY_MAP.md` and `GAPS.md`.

## Reproduction and verification scope

Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`;
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, with transitive Git revisions
and source blobs checked against `lake-manifest.json`.

    bash fetch_cache.sh
    python3 reproduce.py --output-dir /tmp/tree-proof-independent-check

The output directory must not exist. The script checks the source manifest,
constructs a new Lake source tree with zero owned objects, performs a Lake
build, separately recompiles every owned module, audits all declared roots,
and replays their full used declaration closure into `mkEmptyEnvironment 0`.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. It then
compiles deliberately false source mutations and requires rejection.

Historical completed checkpoints: run 38140690781 passed for the initial
coefficient/block core (24,604 declarations; 23 roots; two mutations).
Run 38143311408 passed for the actual gluing extension (four modules and
four mutations). The new scaling/root-update modules have compiled in the
source-isolated development compiler; their expanded source-bound independent
verification is a new run, not either historical receipt. Exact completed
receipts, not this prose alone, establish verification of their own bytes.

Development compiler requests are editor diagnostics, explicitly NOT formal
verification certificates. Main proof CI is a separate clean build and replay.

## Provenance

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology. mxymmxym1@gmail.com.
ORCID 0009-0000-3864-3536. No external funding; AI-assisted development.
Existing repository and third-party notices remain in force. Original additions
retain all rights not otherwise granted by an applicable existing license.
No completion Release, DOI, external peer review, or priority claim is made.
