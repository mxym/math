# CGF Conjecture 48: full Lean verification evidence

The explicit counterexample is

`F = (Φ₄ Φ₉ Φ₂₅ Φ₃₀)⁶ ∈ ℤ[X]`.

Here each `Φ` is the actual Mathlib `Polynomial.cyclotomic`, and `F` has degree
216. The complete original basic/unimodal version of Conjecture 48 is false:
`F` is nontrivial and basic, its coefficients are unimodal, and no prime-index
cyclotomic divides it. See [Billey–Swanson, Conjecture 48 and Definitions 1, 3,
45](https://arxiv.org/html/2305.07620v3) and the
[mathematical certificate](../../notes/cyclotomic-prime-factor-counterexample/cyclotomic_prime_factor_20261008/certificate.json).

## Four formal roots and their scope

All roots are in namespace `CyclotomicCounterexample`:

- `explicit_counterexample`: genuine cyclotomic product, nontrivial basic CGF,
  unimodality over all natural indices including the zero tail, and prime-factor
  exclusion for every `p` with `Nat.Prime p`.
- `conjecture48_false`: negates the entire formalized quantified conjecture in
  its published basic/unimodal domain. No squarefree, irreducible or non-power
  restriction is added to the witness.
- `F_centered_certificate`: proves the full centered q-integer polynomial
  identity with all 109 positive weights.
- `F_qInteger_quotient_certificate`: proves `N^6 = F * D^6` and `D^6 ≠ 0`.
  Numerator indices are 4, 9, 25, 30; denominator indices are 1, 6, 10, 15.
  This is a nonzero-denominator-cleared identity, not a separately formalized
  rational-function division theorem.

The 217 coefficients are proved equal to the genuine product's coefficients,
not merely assumed to be a list describing it. The proof gives strict increase
to index 108, strict decrease through index 216, and a unique maximum among all
natural indices. The peak is 11,434,392; the minimum first-half adjacent
difference is 5. The distinct list of centered weights begins with 1.

## Execution, independent review, and attribution

The designated independent verification operator checked the author's exact
11 Lean source files on 2026-10-08, 10:53:35–10:56:55 UTC. The original source
checkpoint is fixed at
[616877a1f3ac57ddc23737901581e666b0aabdd1](https://github.com/mxym/math/tree/616877a1f3ac57ddc23737901581e666b0aabdd1/notes/cyclotomic-prime-factor-counterexample/lean-source-checkpoint).

The recorded execution passed:

- Fresh compilation of eight mathematical modules and all three author audit
  modules. No old owned `.olean` was reused.
- Audit of all 112 owned declarations: 73 named and 39 generated/private.
  No author module or owned declaration was excluded.
- Replay of the entire 29,737-node owned dependency closure in an initially
  empty kernel environment with trust level zero. Individual root closures
  have 29,681, 29,661, 29,581 and 29,553 nodes; their union has 29,717.
- Only `propext`, `Classical.choice` and `Quot.sound` occur as closure axioms;
  no owned axioms or unsafe/partial mathematical declarations occur.
- A negative control deliberately used a proof of `True` for a theorem of
  `False`; it was rejected with the expected declaration type mismatch.

A separate reviewer checked semantic correspondence, exact source identities,
historical hashes, all closure edges and axiom reports, plus independent exact
coefficient arithmetic. That reviewer did not install or run Lean. The
publication step did not compile Lean either. It ran the portable static checks
and wrapper preparation tests described below. See the
[static semantic/evidence review](audit/AUDIT_REPORT.md),
[public-copy review](audit/PUBLIC_COPY_REVIEW.md),
[operator's execution assessment](INDEPENDENT_REVIEW.txt),
[commands](fresh-verification/manifest/commands.json), and
[compile/replay/control logs](fresh-verification/logs/).

The author `reference/verify.sh` was not run end to end. The operator used the
unchanged independent `leanctl.py` entry point to compile all 11 author Lean
files. Historical `pending`, `author_claim_verified=false`, and
`semantic_review=REQUIRED_SEPARATELY` fields are retained as originally recorded;
this page and the separate review supply the subsequent status. They are not
silent edits to the earlier checkpoint or machine records.

Trust level zero comes from `mkEmptyEnvironment 0`, followed by an empty-map
check. The zeros in `addDeclCore 0 0` are resource limits. `Lean.Replay` itself
permits axioms and skips unsafe/partial declarations; the surrounding whitelist
and rejection checks are essential. The final check verifies presence, types
and universe parameters. The Lean kernel/runtime and checker implementation
remain trusted machinery. Shared-cache checks establish unchanged path, size
and mtime metadata, not independent authentication of every cached byte.

## Exact environment and portable checks

- Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`
- Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`
- All nine package revisions and operational parameters:
  [PUBLIC_ENVIRONMENT_CONFIG.json](PUBLIC_ENVIRONMENT_CONFIG.json)

From this directory, using Python 3.9 or later and its standard library:

```sh
python3 check_public.py
sha256sum -c SHA256SUMS
```

The default checker verifies every published file and inventory entry, all
unchanged mapped original bytes, losslessly decoded complete graphs, source and
control consistency, the historical manifest mapping, every owned axiom report,
root and all-owned reachability, imported-interface source hashes, and exact
coefficient/weight arithmetic. It does not run Lean and does not write into the
evidence tree. Hashes of deliberately omitted binaries are reconciled as
historical records only, not checked against unavailable bytes.

`CURRENT_PUBLIC_MANIFEST.json` covers all payload files. The top-level
`SHA256SUMS` additionally covers that manifest; neither claims to hash itself.
`audit/audit_record.py` is the original static-review script with original
machine-local inputs. The portable public entry point is `check_public.py`.

## Reproduce Lean from the delivered configuration

The checker and control sources under `verifier/` are exact originals. Use an
existing matching Lean toolchain and all nine pinned dependency checkouts with
compiled `.lake/build/lib/lean` libraries:

```sh
python3 reproduce_lean.py \
  --toolchain /absolute/path/to/lean-4.34.1 \
  --packages-root /absolute/path/to/pinned-dependencies \
  --workdir /absolute/path/to/new-cgf-run \
  --run
```

The wrapper creates a new external workspace, copies the supplied verifier,
constructs its complete configuration from `PUBLIC_ENVIRONMENT_CONFIG.json`,
relocates toolchain/dependency/source paths, runs `doctor`, then compiles every
owned module fresh and runs the complete audit/replay/negative-control sequence.
The omitted compiled binaries are unnecessary: each new run creates its own.
Omit `--run` to prepare only. The wrapper performs no installation or download.
Obtain missing dependencies from the official upstream URLs listed in the
configuration. The pinned toolchain and dependency caches are not bundled.
Historical absolute paths record the original run and need not be recreated.

## Public projection and lossless graph packaging

This is a self-contained source/evidence projection, **not an unchanged or
complete republication of the original execution archive**. That archive is
18,311,823 bytes, SHA-256
`c2bcb597d513f9929eadd8bc749737a966ef9f919ee8040781609e02dac878d9`.

[PUBLICATION_MAPPING.json](PUBLICATION_MAPPING.json) accounts for all 112
original files individually, with original size and SHA-256:

- 86 files are exact byte copies, including all mathematical source, checker
  source, certificates, compile/kernel/control logs and historical records.
- Two full graph files use lossless gzip plus base64, split into ordered text
  parts. Their reconstructed bytes, sizes and hashes match the originals.
- 22 `.olean`/`.ilean` outputs are omitted, with every original hash and size
  retained in the mapping. They are rebuilt for a new execution.
- Two equivalent environment copies map to one public configuration. Only two
  non-mathematical administrative fields were removed; every remaining value
  was compared programmatically to the originals. The projection and retained
  canonical-JSON hashes are recorded.

The original 111-entry package manifest and 73-entry fresh-run checksum file
are preserved as `PACKAGE_SHA256.original.json` and
`fresh-verification/manifest/SHA256SUMS.original`. They describe the original
execution package, including omitted bytes. Use the current top-level inventory
and default checker for the actual public delivery.

The standard-library unpacker validates ordered-part, encoded and reconstructed
hashes before writing both full graph files into a new external directory:

```sh
python3 unpack_evidence.py --output /absolute/path/to/new-decoded-cgf-evidence
```

No applicable CGF GitHub Actions workflow is added by this publication. Recorded
operator execution and static publication checks are not a green GitHub CI run.
This result does not establish minimum degree, worldwide priority, uniqueness,
other CGF conjectures, or external human peer review. Novelty checking is separate.
