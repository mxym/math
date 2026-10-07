# Reviewed-source to public-copy delta

## Mathematics

**Section 1 and all 10 theorem, lemma, corollary and proof environments remain byte-identical to the independently reviewed source.** Their exact byte lengths and SHA-256 hashes are in provenance/PROTECTED_MATHEMATICS.json and are checked by the integrity verifier. The theorem's range, constants, coordinatewise quantifiers, zero-extension convention and conditional transport boundary are unchanged.

## Eleven precision corrections

The approved correction set adds the explicit critical marginal, complete compact-source/domain hypotheses, missing historical result citations and separated endpoint quantifiers, and updates completed model-review status. It changes four text files. See audit/CORRECTION_RECORD.md and RELEASE_DELTA.json for the complete edit record. It does not modify a theorem or proof, replace the independent potential estimate (P), establish novelty or claim human peer review.

## Public-copy preparation

Beyond those corrections, the TeX date and snapshot-description wording are made suitable for public reading. Only the final attribution block uses a local smaller-font group to avoid a nearly empty seventh page. This changes no words in that block and no protected proof bytes. The PDF is rebuilt from this revised source rather than reusing the pre-correction PDF.

The README is replaced with a public reading and reproduction guide. The scope review loses navigation/approval logistics and names the actual dependency manifest. The manifest's status loses workflow terminology and gains local paths and byte lengths. All existing source hashes, Git blobs and frozen public URLs remain unchanged.

The public-clean audit preserves its full analytic reconstruction and import analysis, with sanitation changes separately recorded in audit/SANITIZATION_CHANGE_LEDGER.json. Private workspace locations, account-specific file/download metadata, task identifiers and build logs are excluded. No personal author or new license is assigned. The included 57 historical source files and upstream notice/license are verbatim pinned copies.

Dependency explanations, runnable controls, recorded results, protected-byte checks, adversarial integrity tests and a deterministic source archive are added. These do not certify mathematics by computation; the finite diagnostics and their limits are stated explicitly. The exact before/after identities of the four source text files, revised TeX and rebuilt PDF are in RELEASE_DELTA.json.

## Final-copy packaging correction

The initial packaging helper generated fresh manifests before validating the release. Final-copy adversarial review showed that this could accidentally accept edited or missing verification wrappers and omitted hash-list entries. The public packaging command now performs full read-only preflight against the existing manifests and a fixed complete inventory before archive generation. It cannot reseal such damage. Optional archive output goes only to a new external file after verification.

Deliberate regeneration is isolated in regenerate_manifests.py and requires the explicit --acknowledge-no-authenticity flag. This maintainer operation still requires the complete fixed inventory and unchanged protected mathematics/dependency checks, but does not authenticate new edits. The negative suite now tests the public builder itself under normal Python and -O and compares whole-package bytes before and after rejected operations.

This correction changes only verification/packaging code, its tests, documentation, QA records and regenerated archives/manifests. The TeX and PDF bytes, Section 1, all 10 theorem/proof environments, and all 57 historical source copies are unchanged. The correction record additionally clarifies that its quoted replacement strings describe the intermediate approved correction stage rather than every final public-copy string.
