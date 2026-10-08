# Sources and reuse

Work took place in a fresh directory created solely for this task. The saved
provisioning configuration's older project was not inspected, modified, or
resumed. Managed runtime/network guidance and `/etc/codex/network-policy.json`
were read before downloads. All downloads used the inherited permitted proxy
and official upstream sources, without adding credentials or disabling checks.
There were no `AGENTS.md` or `.agents/` instructions in the relevant new math
checkout trees at the inspected commits.

## mxym/math

The initial checkout was commit `8ad38152eac75993659c1f128a382bbc1a19ceab`.
The task later fetched main commit
`80b3317de497dffdaa6b6398d7ba908c29cb252a` to read entry005 v5 and incorporate
its scalar recurrence. Git checkout contents, rather than a stale unauthenticated
web view, supplied the papers. No Lean project was present in the initial mxym
tree. `references/SOURCES.json` records the exact commit, original repository
path, and SHA-256 of every included source-paper snapshot.

Repository: <https://github.com/mxym/math>.

## OpenAI/math

The inspected source commit is
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`:
<https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean>.
Its Lean toolchain and mathlib pin are the ones used by this project. Its root
Lake setup also includes comparator and other infrastructure not needed here.
The Lean README describes compiling small modules; the comparator README
describes its separate comparison/sandbox workflow. This task performs actual
Lean compilation and `#print axioms` audits and does not claim to have run the
upstream comparator infrastructure.

The relevant upstream `ProjectionVolume` solution development includes
geometric projection-volume statements; `ProjectionBody` includes related
projection-body development. Their challenge counterparts may contain
intentional placeholders. In particular,
`lean/ComparatorChallenges/ProjectionVolume.lean` has a `sorry` challenge.
No challenge file is imported. Only the following audited solution excerpts
are claimed as certified reuse here:

| Active file | Exact upstream relationship | Exported certified scope |
| --- | --- | --- |
| `OAI/Geometry/ProjectionVolume/Arithmetic.lean` | Byte-identical to upstream `lean/OAI/Geometry/ProjectionVolume/Arithmetic.lean` | Three scalar simplex-constant ratio/comparison theorems |
| `OAI/Geometry/ProjectionVolume/Model.lean` | Exact upstream `simplexConstant` definition; narrow imports; unused geometry removed | Only the scalar definition required by Arithmetic |
| `Mxym/UpstreamCancellation.lean` | Exact statement and proof of `twice_sum_negative_eq_sum_abs` from upstream `ProjectionCoefficients.lean`; narrow imports/namespaces | The finite zero-sum sign-mass identity |

Full originals of the three source files, upstream toolchain/config/lockfile,
READMEs, and Apache-2.0 license are retained in `vendor/openai/`. Byte/body
comparisons and a source scan of the relevant upstream solution directories
are recorded in `logs/upstream-audit.log`. Every actual reused theorem was
freshly compiled in this project and included in the transitive axiom audit.
No `sorryAx` or other hidden extra axiom occurs in these audited dependencies.
Scanning a directory is not certification of its uncompiled theorems; neither
the full upstream geometric solution nor all of OpenAI/math is certified here.

## Official tooling

- elan release 4.2.4:
  <https://github.com/leanprover/elan/releases/tag/v4.2.4>.
- Lean release 4.34.1:
  <https://github.com/leanprover/lean4/releases/tag/v4.34.1>.
- mathlib source pin:
  <https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612>.

The Linux x86_64 elan archive was actually downloaded from the official release
and its observed SHA-256 was
`42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63`.
The bootstrap script checks that value; this is an observed artifact checksum,
not a claim of an upstream signature verification. Lean and Lake are pinned
by the toolchain file, and all dependency repositories are pinned by commit in
`lake-manifest.json`.

The first dependency update resolved the lockfile but its automatic cache step
could not write the default `/home/agent/.cache/mathlib` location. Recovery used
an explicit task-local `MATHLIB_CACHE_DIR` and the official module cache command.
No security restriction was bypassed. `logs/lake-update.log` records the initial
cache error, `logs/mathlib-cache.log` the successful module-cache retrieval,
and `logs/lockfile-regeneration.log` the successful final fixed-toolchain lock
generation with automatic cache disabled. No installation blocker remains.
