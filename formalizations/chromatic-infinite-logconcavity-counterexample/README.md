# Complete C17 Lean counterexample

This package supplies the complete Lean proof that the absolute coefficients of
the genuine cycle C17's chromatic polynomial are not infinitely log-concave.
The proof follows the standard endpoint-retaining, zero-extension convention.
At degree index 2, the third iterate is exactly **−28,272,276,537,344**.

The chain is fully represented in Lean:

1. `SimpleGraph.cycleGraph 17`, including the edge from vertex 16 to vertex 0;
2. a bijection between proper q-colorings and closed length-17 walks in the complete q-color graph;
3. the coloring-count formula for **every natural q**, including q = 0, 1, 2;
4. uniqueness of the chromatic polynomial `(X - 1)^17 - (X - 1)`;
5. its actual absolute coefficients, zero extension, and iterated log-concavity operator;
6. the exact negative third iterate and a counterexample to the universal conjecture.

## Proof and evidence

- [Three source modules](evidence/formalization/sources), built in order:
  CycleColoring, ChromaticPolynomial, LogConcavityCounterexample.
- [Recorded complete result](evidence/formalization/RESULT.json).
- [Independent semantic and static evidence audit](audit/AUDIT_REPORT.md).
- [All-owned declaration inventory](evidence/fresh-verification/manifest/owned-inventory.json)
  and [complete dependency graph](evidence/fresh-verification/manifest/all-owned-closure.json).
- [Empty-kernel replay summary](evidence/fresh-verification/manifest/replay-summary.json)
  and [invalid-proof control log](evidence/fresh-verification/logs/negative-kernel.log).
- [Complete publication mapping](PUBLICATION_MAPPING.json), accounting for all 75
  original public-package files and each machine-path projection under `evidence/`.

The recorded fresh run compiled all three owned modules and audited **98 owned
declarations: 41 explicit and 57 generated/auxiliary**. Its complete closure has
**10,964 nodes**; the five named roots have **10,929 nodes** in their union. Every
owned declaration, including generated declarations, is covered. No owned axiom,
unsafe declaration, or partial declaration is admitted. The only closure axioms
are `propext`, `Classical.choice`, and `Quot.sound`.

The verifier starts from an empty constant map at trust level zero, replays the
whole closure through the kernel, and checks the replayed declarations. An invalid
proof of False using True.intro is required to fail with a kernel type mismatch.
The recorded run passed both replay and this negative control.

Pinned versions: Lean **4.34.1**, commit
`5045d0056413266e57c625dcd7c365b10e377c52`; mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.
All dependency pins are retained in the public environment configuration.

## Independent review versus execution

The original verification run executed Lean. The separate auditor performed
source-level semantic review, recomputed the complete dependency graph and all
98 axiom reports, and independently reconstructed all 18 coefficients by
inclusion-exclusion over 131,072 edge subsets. All four iteration rows agree.
The independent auditor **did not execute Lean**. Publication preparation also
does not claim a new Lean run. Its fresh Python checks are a portable recheck of
the recorded evidence and arithmetic, not a new kernel execution.

## Verify the public snapshot without Lean

From this directory:

```sh
python3 -B check_public.py
```

This checks the exact full inventory, byte lengths, SHA256 and Git blob hashes,
all 75 mapped evidence files, original historical manifest bindings, source
and checker bindings, all declaration/closure/axiom counts, command records,
pinned source copies, and independently recomputed C17 arithmetic. It writes no
file into the evidence tree and makes no network requests. The preserved
`audit/static_audit_result.json` is the historical result; a fresh portable result
is printed to stdout. To save a new result, use `audit/audit_record.py --output`
with a new filename outside this snapshot.

## Repeat fresh Lean verification

Use an existing exact-version Lean installation and the pinned Git checkouts,
with dependency build caches already populated. The helper downloads and installs
nothing. It preserves all original evidence and prepares a new external workspace:

```sh
python3 -B reproduce_lean.py \
  --toolchain /path/to/lean-4.34.1 \
  --packages-root /path/to/pinned-package-checkouts \
  --workdir /path/to/new-replay-workspace
```

The packages directory must contain each package under its configured name,
including `mathlib`. The command prints the doctor/verify commands. Add `--run`
to actually execute them. Preparation alone does not validate installed commit
pins or prove anything; the original driver performs those checks before the
fresh build. The helper copies the unchanged driver and checks, adjusts only
machine-dependent paths, keeps sources pointed at the hash-bound publication,
and never uses the archived owned `.olean` files as build inputs. The work
directory must be new and outside this snapshot.

The unchanged historical driver's missing-toolchain diagnostic mentions a
`RECOVERY.txt` file from its original environment. No such private recovery file
is needed or distributed here: supply the required existing pinned installation.

## Scope, provenance, and limits

This Lean result covers C17 only. It does not formalize C12, all cycles of length
at least 17, the full cycle classification, or endpoint-deleting variants.
The older mathematical proof and certificates at
[the frozen source commit](https://github.com/mxym/math/tree/2b73cde3ae77ab1227c7386e9e82d0e815f21e88/notes/chromatic-infinite-logconcavity-counterexample)
remain unchanged. Those broader mathematical claims are not silently promoted to
Lean-verified claims. No priority, novelty, peer-review, or acceptance claim is made.

The supplied historical public package had removed two coordination fields from
two configuration copies. For this publication, machine-dependent absolute roots
are additionally replaced by `<LEAN_TOOLCHAIN>`, `<PROJECT_ROOT>`,
`<PACKAGES_ROOT>`, `<CACHE_ROOT>`, and `<VERIFIER_ROOT>`. All relative suffixes,
command arguments, run identifiers, tool/package pins and mathematical content are
retained. `PUBLICATION_MAPPING.json` records the original and projected hashes,
lengths, and projection rules for every file. The three Lean sources, compiled
outputs, full declaration graphs, mathematical proof and exact certificates remain
byte-identical to the supplied public package.

The source archive is **not distributed**, because it contains the original
machine paths. Its hash identifies the historical input; it is not a checksum of
an included asset. The original package/fresh manifests and original public
profile are retained with `.historical` filenames. They describe the earlier
files and must not be used as checksums of projected files. The outer current
manifest and checksums describe every file actually delivered here.

The preserved `audit/AUDIT_REPORT.md` is the independent audit of the historical
public package. It remains unchanged. Its recorded JSON result has only the same
machine-root substitution. The portable checker recomputes the complete static
and arithmetic checks on the publication copy. The local final-copy gate can
compare all projected files with their original source bytes; the portable public
checker verifies every current hash and its binding to the recorded original
manifest hashes, but cannot independently recover the undisclosed original root
strings. This distinction does not alter a Lean statement or proof term.

The original unmodified execution archive was not supplied to the independent
auditor or this publication stage. A full raw-versus-public execution archive
comparison is therefore not claimed. The auditor previously checked both declared
coordination-field projections using available original configuration bytes.
Historical README/result/profile files inside `evidence/` describe that original
run; this README and `PUBLICATION_MAPPING.json` describe the current delivery.

Shared-cache stability is a path/size/mtime check, not authentication of all
cached bytes. The original build used pinned dependencies' existing caches; it did
not rebuild the entire toolchain/dependency supply chain. See the independent
report for these and other trust limits. A repository commit or absence of CI
checks is not an additional Lean verification.

`CURRENT_PUBLIC_MANIFEST.json` enumerates every payload file except itself and
`SHA256SUMS`; `SHA256SUMS` includes the manifest and every payload file, excluding
only itself. `PUBLICATION_MAPPING.json` identifies all original public files and
the portable auditor's explicit adaptations and path projections. No third-party paper PDF is bundled.
Pinned upstream source files retain their notices; their licenses are included
under `audit/upstream/`.
