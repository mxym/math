# Separate appendix: native canonical Word gate provider

Status: **No substantive defect found in the separately fixed binary bridge at `71147d7005d4315fb5439e36138d24482c794c30`. Independent source review plus existing author-log/hash verification only. No new kernel, Lean/Lake run, or negative controls.**

This appendix adds a new fixed object after the initial three-object review. It leaves `REPORT.md`, `MANIFEST.json`, and `recheck.py` unchanged. The initial manifest SHA256 is `512260dc06784f384c2799c8659a1dd41258f3724f7b7f582c5d2fab46768016`. The initial report's exclusion of then-unreviewed successor code remains an accurate statement of that earlier scope.

## Exact source and reviewed chain

The new prefix is `formalizations/extraction-rational-gate-binary`. Its `RationalGateBinary/Provider.lean` SHA256 is `fa0306e1fb07e4f71481943b402331b5ea6a876027f7ce2b08ecbac04988677c`, matching the parent's earlier uncommitted-source identity and the later sealed source snapshot. The fixed package has eight selected theorem roots. Its parent is `fb92b813b71f51f77083714c086c12369f049eb5`; the exact Git difference to the seal contains only ten new files under this new prefix. The old universality, provider and interface prefixes match their initial fixed review objects at this new seal.

The reviewer read the full Provider and Check files, package documentation/configuration, and relevant numerical dependency sources: `NativeBinaryPacketInput`, `NativeCachedSynthesis`, `NativeWordEvaluation`, `CanonicalBinaryWords`, `SignedBinaryWords`, `WordPacketMultiplication`, `IntegerPackets`, and `NativePacketCache`. The definitions of `binaryBitValue` and `binaryWordValue` were also read in `BinaryWordAddition`. The appendix manifest binds those entire files, while the human read of `BinaryWordAddition` is specifically its first definitions, not every unrelated arithmetic theorem in that file. Other transitive imports are byte-bound, not claimed to have been re-read in full.

The new read-only recheck independently resolves local imports from `RationalGateBinary.Check` through the fixed package manifest's path dependencies. It rejects ambiguous local module resolution and unresolved imports outside the named external Lean/Mathlib ecosystem, records every reachable local module's exact blob/hash/imports, and binds the listed package configuration inputs. This is static source provenance checking, not recreation of the compiled import environment.

## Actual value path and exact compatibility

`binaryEntry i p` evaluates one `entryBits i p` vector, stores signs and magnitudes extracted from it, and supplies `denominatorBits p`. Its only denominator-value arithmetic is in a proposition proving positivity. In the executable data path, `entryBits` uses the earlier finite-state `run`; the denominator is a Boolean-list replicate/append. There is no `Nat.bits`, integer/rational materialization, `.decode`, matrix evaluation, or real/complex gate computation in that data path. Semantic `binaryWordValue` occurrences in proof fields do not make it an integer-producing program.

The helper theorem equates the two actual little-endian natural-value functions, `binaryWordValue` and the provider's `bitValue`. `binaryEntry_decode` then proves equality of all four signed integer numerators and the exact natural denominator with `dyadicIntegerPacket (dyadicEntry i) p`. This is an exact packet-components equality, stronger than only equality after rational division. The denominator is precisely `2^p`, with no untracked scaling or gcd reduction.

`nativeEntryProgram` actually runs `binaryPacketInputProgram` on this bit input. Reading that dependency confirms it stores four signed normalizer results and one denominator trim, then builds the resulting canonical `WordIntegerPacket` from their actual output words. `nativeEntry` returns that program's packet. It is not an arbitrary value required by a semantic certificate.

The actual trim program recursively stores one tail result and branches only on its list constructor and the current Boolean. Its canonical predicate forces every nonempty little-endian word's high bit to be one. The signed normalizer additionally changes the sign to false exactly when the trimmed magnitude is empty. These are real program branches, so padding and negative zero need no input canonicality premise. The `WordIntegerPacket` constructor includes canonicality of every numerator and denominator and positivity of the denominator. At p=0, signed input zero becomes an empty magnitude with false sign, while the denominator is `[true]` and decodes to one.

The exact correctness chain is:

1. `binaryEntry_decode` relates raw input bits to the old dyadic integer packet.
2. `binaryPacketInputProgram_decode` preserves that exact packet under the actual normalizers.
3. `nativeEntry_decode` composes those equalities for the returned packet.
4. `nativeEntry_oracle` uses the existing `nativePacketDataOracle` definition, `(f p).decode.value`, and the existing `dyadicIntegerPacket_value` to prove function equality with the old `dyadicQuaternionOracle (dyadicEntry i)`.
5. `nativeEntry_correct` transfers the already-reviewed `dyadicEntry_correct`, obtaining the original `QApproximates` for the same concrete SU(2) gate.

All equalities refer to the same actual `nativeEntry` program and are quantified over every label and every natural precision. The definitions called by the executable provider do not run the denotational decoder that appears in these correctness statements. No caller-supplied correctness witness is hidden in any of the eight new theorem endpoints.

## Height and normalization actions

`nativeEntry_height` transfers the old `dyadicIntegerPacket_height` through exact decode equality. The notation is the established semantic exponent bound: `IntegerPacketHeight a B` means `a.denominator <= 2^B` and every integer numerator has absolute value at most `2^B`. Thus the new result has B=p+1; it is not a statement that the denominator's length is at most p, or that the entire packet uses p+1 bits. Canonicality connects this bound to real stored bit lengths through `WordIntegerPacket.height_width`, giving each magnitude and the denominator length at most B+1. The sharper input-list lengths p and p+1 are separately known here.

`nativeEntry_height_ninth` weakens the same actual packet's height to B=(p+1)^9. Its only arithmetic step is `p+1 <= (p+1)^9`, valid also at p=0 since p+1>=1. It does not ask callers to assume a query-height bound. It supplies the pointwise ninth-power envelope used by native compiler interfaces; it does not itself audit later numerical or encoding consumers.

The action theorem counts the actual returned normalizer traces. In the dependencies, a trim trace has one terminal charge and six per digit; a signed normalization adds four; the packet normalizer sums the four actual signed-result charges, the one actual denominator-trim charge, and sixteen fixed packet actions. There is no free function assigning a desired cost or an external budget certificate. `binaryPacketInputProgram_actions` proves the generic upper bound `64*(B+1)` from input lengths at most B. The new theorem supplies those input bounds from the actual list lengths, using B=p+1, hence obtains `64*(p+2)`.

These constants define the specified Bool/list/record action convention. They do not establish equality with instructions, wall time, or a complete implementation-level allocation model. In particular this counter excludes the earlier four finite-state emissions, denominator-bit construction, sign/magnitude-vector construction, precision-clock and recursion control, arithmetic on counters, full memory costs, input reading, cache generation/lookup, offline net discovery, and whole compiler execution. The program is concrete, and its **normalization** action bound is internally derived; a full provider-machine-time theorem remains absent.

## Existing author evidence and recheck

The fixed author report records eight selected theorem types/axiom outputs, a 3963-job successful standard aggregate build, and actual four-label precision-four plus precision-zero negative-zero checks. The independent read-only verifier checks the original log bytes and their actual markers, rather than trusting only the parsed report:

| Original author log | SHA256 |
|---|---|
| `20261018T223244898676Z-root-owned-RationalGateBinary.Provider.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `20261018T223443816684Z-root-owned-RationalGateBinary.Check.log` | `155c29279c434f90ac18c23c35e52cf532f0ea4dc22d00e757ac6ad0d3e34ff8` |
| `20261018T223454910161Z-extraction-rational-gate-binary.log` | `1005a67ed440f68334aceb923ac0e35ebb4a1f24e4be4428a76d5f449f1434c0` |

The empty owned Provider log has the expected empty-file hash; it is not an independent standalone validation record. The actual Check and aggregate logs contain `CONCRETE_NATIVE_WORD_PROVIDER_CHECK_PASS`; the aggregate log ends with successful 3963-job completion. The Check source tests the exact integer numerators, denominator 16, the stated loose action bound at p=4, and false signs for every magnitude at p=0. The actual printed axiom sets match the fixed report and use only `propext`, `Classical.choice`, and `Quot.sound` (the value-function helper uses only `propext`). The source declarations are theorems; this package Check prints types/axioms and executes small data checks, without a separate declaration-kind assertion loop.

Run `python3 -B /mnt/d/math/tmp/extraction-resume-20261018/native-library-independent-review-20261019/recheck_binary.py` in Ubuntu-22.04. The script verifies the unchanged initial review manifest and its original evidence first, then compares the new evidence with `BINARY_MANIFEST.json`. It performs no writes or kernel/compiler execution. The new manifest separately binds this appendix and its read-only script.

The reviewed bridge closes the native canonical-data compatibility gap identified in the initial report for this fixed successor. It does not convert any author-only native numerical/encoding result into an independent audit, and does not close whole classical compiler/provider machine bit time. No substantive source correction is requested for the appended fixed object.
