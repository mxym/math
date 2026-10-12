# Quadratic orders Main: independent final release and execution review

**Result: PASS.** Reviewed on 2026-10-08 UTC. The exact final source copy and its completed public verifier run pass this review. This report does not itself establish that a repository upload or deployment has occurred.

## Exact identities

| Item | SHA-256 |
| --- | --- |
| `quadratic-orders-main-source-20261008-v2-final.tar.gz` | `8e16e2191c788738dbe3592578fb8c4a09082215ec373ff8d87201fbe6a15e6f` |
| Completed run `OUTPUT_MANIFEST.json` | `76db4a5a82937d9cb00506acbcb756447eade6426082600cc3f68eb5ee19c761` |
| Original input `entry002-v3-lean-round5-20261007.zip` | `c0fa4d986a4de3700f68deb4d4cead1a6a51713c144bc62d75ae5d4b90592dda` |
| Public reproduction addendum `SHA256SUMS` | `46bf11f38bab35b83ba11722b584bf6f0529555119eada3336719cb0bb8dedaf` |

The source archive is 14,635,994 bytes and contains 1,448 regular files under `formalizations/quadratic-orders-main`. All 1,256 received Lean source files retain their original bytes. The actual source tree used by the completed verifier is byte-identical to the independently extracted final archive.

## The public runner really completed

The public program began at 2026-10-08 00:24:59.919522 UTC, finished with exit code zero at 03:23:40.544773 UTC, and completed its producer-side terminal output checks at 03:24:22.283192 UTC. The final two stdout lines are the output-manifest digest above and `QUADRATIC_ORDERS_MAIN_PUBLIC_REPLAY_PASS`.

This was one fresh execution, without restart or resume. Its records and stdout contain exactly one successful build for each of:

- 995 ClassFieldTheory modules
- 129 main-library units
- Five arithmetic bridges

The 1,129 fresh module identities, source digests, compiler commands, zero exit codes, output identities and logs match the sealed source graph. No old owned or CFT object was accepted. There are 7,000 separately bound official/toolchain cached modules and zero fresh official fallback builds; this is not a full fresh rebuild of Lean or mathlib.

After the producer's normal and optimized checks, this review independently ran the sealed public `verify_output.py` from the auditor's separately extracted source copy, in both normal and optimized Python, using the previously printed manifest digest. Both exited zero. Each checked 43,270 recorded output entries, 1,129 fresh modules, three audit helpers, 7,000 official cached modules and 1,144 run logs. The review also independently reconciled every actual loaded module path against its fresh/helper/official record: exactly 8,132 modules, comprising the 8,129-module source graph and three helpers.

The checks cover all recorded primary objects and present recognized sidecars, helper source/output bindings, selected official cache links, run logs, result and closure files, and release identity. They leave the source and run tree unchanged. The artifact checker reports `proof_rechecked=false`: it validates the completed run's evidence and does not pretend to execute another kernel proof.

## Mathematical endpoint and actual kernel result

The exact endpoint remains:

`Entry002.arithmeticSupply_mainTarget_proved : Entry002.MainTarget`

It is accessed through `import ArithmeticSupplyWeakMain`. The original `Targets.lean` digest remains `f4cbd00f1853dc53b955a2b05e7d07223a6a7fe5e0fc762d87e8ed397fe64671`.

The completed public run itself executed the official Lean kernel replay of the literal Main's **125,368 distinct constants**, starting with **zero constants at trust level zero**. That kernel stage passed in 1,001,336 ms; its containing process exited zero. The closure's complete name array is byte-identical to the earlier sealed independent evidence. The permitted axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`; the stock and imported axiom types/universe snapshots match exactly.

The combined inventory again has 2,952 declarations: 2,501 theorems, 412 definitions, and 39 structural declarations. Its 2,906 safe logical roots comprise the theorems and 405 safe definitions. The seven remaining definitions are disclosed partial compiler-generated runtime helpers. They are not proof roots and do not occur in the accepted literal-Main or nonpartial stored closure. The 2,945 nonpartial logical/structural seeds have a 126,696-constant stored closure, also byte-identical to the prior evidence. That larger stored-closure check is distinct from the actual literal-Main kernel replay.

Positive endpoint/nonvacuity checks and all intended type-mismatch controls actually ran. The stored-proof corruption control was rejected by the kernel. All 1,144 command/log records match their retained hashes; the negative cases failed for their intended type/kernel reasons, not missing-module or parser failures.

The unchanged target covers all quadratic fields and all positive-conductor orders, actual irreducible elements, actual integral bases, full planar real-linear coordinates, uniformly bounded finite reachable components, bounded injective finite walks, and exclusion of infinite injective walks. It does not add the old strong natural-density/PNT target as an assumption. Those stronger endpoints, an effective bound algorithm, originality, and journal suitability remain outside the claims.

## Package controls, revision and public evidence

Earlier final-copy review checked direct original-ZIP/source equality, safe archive inventory, complete checksums, licenses and attribution, genuine cached-object source-deletion controls, duplicate/omitted provider controls, and production entry-point failures in both Python modes. It identified incomplete output-evidence recording in the first release wrapper. Revision 2 corrected that issue without changing any mathematical source or existing Lean audit helper. The exact v2 received independent normal/optimized integrity checks and 34 actual production output-checker controls, using explicitly synthetic artifact fixtures. The producer also completed the final 270 package-guard controls.

Those controls and the preliminary gate alone were never treated as full reproduction. The fresh public run described above now supplies the previously missing end-to-end execution evidence. A lone intermediate `FINAL_VERIFICATION.json` would still be insufficient: this review required the zero exit, final stdout marker, printed digest, sealed output tree and successful independent checks together.

The compact public reproduction addendum has 11 files totalling 189,475 bytes. This review verified its exact inventory and checksums, fresh/helper ledgers, selected audit commands, complete empty/nonempty log representation, kernel result, final certificate, scope summary and receipt against the actual completed run. No private workstation paths or private delivery identifiers were found in its decompressed text. It is a compact public record, not a standalone offline bundle of all compiled objects. Existing licenses and attribution remain; the review grants no new license.

Hashes are integrity identifiers, not digital signatures. Reproduction continues to assume the pinned official Lean implementation/runtime, the three standard axioms and the documented quiescent-filesystem boundary. No large cache, second CFT build, or second Main kernel run was created by this terminal review.
