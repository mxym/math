# Actual raw compiler and partial resource bounds

This is a new independent audit profile. It does not enlarge or edit the frozen completion, algorithm or execution-v2 profiles. Its mathematical candidate is `04044ad0e1dc94634a8005f5f6abebe4518a012b`.

SCOPE.json records metadata readiness; verification/ records actual results. READY metadata alone is not an independent replay PASS. This profile selects 47 new mathematical modules, all 364 theorems and 186 model declarations in those modules, and 135 exact-type forged-proof controls. The positive audit replays the entire dependency closure of all 550 declarations, not just the 135 controls. Counts refer to this explicit closure; future unimported files do not enter it.

Read MODEL_LIMITS.md and REVIEW.md before interpreting any resource statement. The scope covers the actual raw finite-label compiler, original-register fidelity, actual target-provider root annotations plus online numerical root annotations, represented integer heights and selected serializer/stored-swap annotations. Whole machine time remains open. Fixed gate-provider execution is excluded.

Local commands, from this directory, are `python3 reproduce.py --plan`, `python3 reproduce.py --preflight`, and preliminary `python3 reproduce.py --types-only`. All builds verify the D-backed image and use the shared global build lock. After metadata is complete and READY, `python3 reproduce.py --freeze-source` creates new immutable manifests; the full run is `python3 reproduce.py --fresh`, followed by `python3 verify_local.py verification/raw-resource-TIMESTAMP`.

Fresh verification deletes only the reproducible `.lake/build` outputs of the two author packages in this isolated tree and this new audit package. It builds only the bound audit libraries, recursively compiling their actual imports. It never builds the unbound author umbrellas or scans future unused modules. Shared Mathlib and old frozen evidence are preserved.

The new GitHub template is a separate workflow. A producer must verify its actual installed workflow bytes equal the source-bound template and every execution input equals its event Git blob. Hosted mode explicitly rejects local Windows/WSL. Every artifact is downloaded into a separate job and checked by the bound reader. Local results alone are never labelled hosted CI results.

All source/semantic reviews here are internal AI-assisted reviews, not external peer review. Author BUILD_ONLY evidence is provenance, not independent kernel verification. State changes and actual evidence will be reported separately under verification/.

The 16 author claim/status documents are byte-exact snapshots in claims/, each bound to its original repository path, source commit and Git blob/hash in CLAIM_SNAPSHOTS.json. They preserve historical owned-only/as-of status and are not current standard-build evidence. These snapshots do not additionally freeze the live author report paths; all older 340/605/4378 protections still apply. Mathematical imports and package configuration remain directly bound to their actual files.
