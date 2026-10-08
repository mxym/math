# Pinned public-source replay: Johnson short-cycle spectrum

Audit date: 2026-10-08 UTC. Independent clean-directory VPS replay, with no optimizer or pre-existing local source checkout.

## Exact public inputs

- Formal note: [paper at commit f678bd7](https://github.com/mxym/math/commit/f678bd749b1153a22910be21d74c59a6ea08ac54).
- Transfer checker (non-optimized guard): [commit b75edbd](https://github.com/mxym/math/commit/b75edbde39e26611590b1e1a340f36a6cf5de782). The raw downloaded transfer.py has SHA-256 **427592c994e8507b101814beb4a05fbebbe712742138d6a28a9be85738d829e2**.
- Rank-five checker: [commit 91f3ebc](https://github.com/mxym/math/commit/91f3ebc56e06fee5554d2ac6a6dce4da656c6dcc). The raw downloaded check_k4.py has SHA-256 **1e4bac4315e60406733a0d2bcbc6c3c3762b0bd3961957f41c65fb3b1cfaf5d5**.

Both files were downloaded via raw.githubusercontent.com at these pinned commits, not a moving main branch.

## Reproduction

Run from the folder containing both Python files:

~~~sh
sha256sum transfer.py check_k4.py
python3 transfer.py
python3 check_k4.py
~~~

The clean VPS replay returned:

~~~text
EXACT TRANSFER IDENTITY VERIFIED 1329 (degree,subset size,conjugacy type) combinations
PASS n=11 short-cycle states=54 C=1629/4549
PASS n=12 short-cycle states=72 C=131/357
PASS n=13 short-cycle states=92 C=6817/18427
PASS n=14 short-cycle states=118 C=3106/8153
PASS n=15 short-cycle states=148 C=1345/3493
PASS n=16 short-cycle states=185 C=3591/9187
PASS n=17 short-cycle states=227 C=29846/75821
PASS n=18 short-cycle states=278 C=211/523
PASS n=19 short-cycle states=335 C=445133/1091945
PASS n=20 short-cycle states=403 C=4147/9871
PASS n=21 short-cycle states=479 C=352459/826455
PASS n=22 short-cycle states=567 C=28029/64307
PASS n=23 short-cycle states=665 C=5926/13479
PASS n=24 short-cycle states=778 C=3441/7621
PASS n=25 short-cycle states=902 C=42843/94103
ALL FIFTEEN EXACT RANK-FIVE CERTIFICATES PASSED.
~~~

The 1,329 transfer regressions enumerate literal subset images in symmetric-group conjugacy class representatives. The 15 optimality checks independently reconstruct exact rational primal/dual witnesses and exhaust **every feasible reduced dual type**, rather than sampling or trusting an optimizer.

## Negative controls

1. Both scripts reject Python's -O optimized mode with the expected RuntimeError, preventing assertion stripping from printing false success.
2. An isolated modified checker with n=11 target changed from 1629/4549 to 1629/4550 exited nonzero with AssertionError. The modified script was removed after the test.

## Trust boundaries

This validates the public arithmetic and the exact finite primal/dual certificates at the pinned hashes. The all-degree short-cycle sufficiency theorem and the compression equivalence have complete mathematical proofs in the note; finite tests do not replace those proofs. No Lean proof, external human referee review, all-degree closed formula for the k=4 coefficients, or historical priority assertion is claimed.


## Extension: all degrees 26--50 (second public-source audit)

Following the first 15-degree release, another 25 fixed support bases and an optimizer-free rational checker were published. Both files were downloaded anew from their exact public snapshot [commit bddf3ac](https://github.com/mxym/math/commit/bddf3ac39f90fe828c85be269e984ffe050a4136), together with the transfer evaluator pinned above:

- check_k4_26_50.py SHA-256: **753144b18af8926cba84fd94c62c85a03d0fb9b505bdf4bbcbca779d68a54638**
- certificates/k4_n26_50.json SHA-256: **68917e56c211687411574f97710b3479fe9ec13cb2deeadeebf0198b0e51a5db**

Run after downloading both files at the noted locations:

~~~sh
python3 check_k4_26_50.py
~~~

The ordinary Python replay exited successfully after printing one exact rational optimum for **each n=26,...,50**, followed by:

~~~text
ALL 25 EXACT RANK-FIVE CERTIFICATES n=26..50 PASSED; types=129523
~~~

The checks covered exactly **129,523** feasible short-cycle types and reconstructed both primal and dual rational witnesses without SciPy, SymPy, or any floating-point call. All tests use only Python standard-library integers and Fraction semantics. The running time of the clean-source replay on the VPS was approximately 36 seconds; this is informational, not a complexity-theoretic bound.

**Second set of negative controls:** running the new checker with -O exited nonzero and rejected optimized mode. Replacing the literal n=26 certificate target 31178983/66734529 by 31178983/66734530 caused a nonzero AssertionError. The original file was restored; its SHA-256 was rechecked and matched the pinned value above.

**Current mathematical scope:** Complete four-subset sharp constants for each integer 11<=n<=50, together with the all-n fixed-k compression and subset-rank monotonicity theorems. There is no asserted exact formula beyond n=50, historical priority, or external referee verification.


## All fixed subset ranks: exact symbolic and rational cross-checks

The subsequent [all-fixed-rank theorem](ALL_K_CHEBYSHEV_ASYMPTOTICS.md) proves for every fixed integer k >= 1 that C(n,k) = 1 - 2 k^2/n + O_k(1/n^2), combining a global Chebyshev dual with positive, exactly moment-matched rational class measures. Its proof, especially the uniform dual interpolation for *all* n and k, is a mathematical analytic argument **not** based on a finite test cutoff.

**Public inputs independently downloaded at fixed commits:**

- [All-rank rational primal check, commit 8f8a0ee](https://github.com/mxym/math/commit/8f8a0ee3b4b9d9d0e111dc31c06897c0f7d74236): check_all_k_asymptotic_primal.py SHA-256 **5626cba86dc907df487bb829e981557fba408d4a63289af110a3bbb42e16ea13**.
- [All-rank exact Lobatto-algebra check, commit 8428e17](https://github.com/mxym/math/commit/8428e17273dab7f7d37e12da946f7cdeb631eb96): check_all_k_lobatto_algebra.py SHA-256 **2a929dd9ef2a3b905dbef61262ce366ab3982218fa2b01868b62edb041672c19**.
- [k=4 symbolic dual and primal limit checker, commit c50b12f](https://github.com/mxym/math/commit/c50b12fdf727e35bd988b7ee1b9fe56d503d9695): check_k4_asymptotic_algebra.py SHA-256 **14c5c300f9d245d6c677909806a45aa69b98e04cfa90b89dae2ecb18e7fc860e**.
- [k=4 rational asymptotic primal checker, commit d892eac](https://github.com/mxym/math/commit/d892eacc8ef87f4ac1c32364c9ab4cb7c59aa916): check_k4_asymptotic_primal.py SHA-256 **55592bc2f287ebeedea2e70d976fd35155dfb92f24ba4b9286c84dd591b8e43d**.

All sources were retrieved into the clean VPS replay folder, separate from the active Git checkout and with no numerical discovery script imported by any proof checker.

Reproduction from the repository root:

~~~sh
python3 notes/johnson-short-cycle-spectrum/check_all_k_asymptotic_primal.py
python3 notes/johnson-short-cycle-spectrum/check_all_k_lobatto_algebra.py
python3 notes/johnson-short-cycle-spectrum/check_k4_asymptotic_algebra.py
python3 notes/johnson-short-cycle-spectrum/check_k4_asymptotic_primal.py
~~~

Observed complete results:

~~~text
ALL 18 ALL-RANK PRIMAL REGRESSIONS PASSED (k=1..6)
SIX EXACT ALGEBRAIC LOBATTO CHECKS PASSED
EXACT k=4 TRANSFER POLYNOMIAL: H, J, R3, R2, R1 verified
ABSOLUTE REMAINDER COEFFICIENT SUM = 1704864
LIMITING PRIMAL MATRIX DET = -sqrt(2)/4096
LIMITING PRIMAL WEIGHTS = (16-8sqrt(2), 16+8sqrt(2), 2, 8)
SHARP FIRST ORDER COEFFICIENT = 32 (algebra verified)
NINE EXACT FOUR-SUBSET ASYMPTOTIC PRIMAL REGRESSIONS PASS
~~~

The rational all-rank tests check k=1,...,6 at n=100,300,1000, with **every orbital moment** exact, strictly positive weights, and finite-dimensional linear systems reconstructed from integer cycle types. The symbolic Lobatto checker uses exact SymPy algebra (no floating-point evaluation) to verify the derivative identity on every monomial through degree k and the limiting primal matrix in ranks 1,...,6. The separate k=4 symbolic checker reconstructs the complete finite dual polynomial identity and the limiting algebraic primal solution, while the rational k=4 primal checker tests genuine positive class measures in degrees through 2000.

**Negative controls:** Python optimized mode -O was rejected by each all-rank certificate checker. In a temporary copy of the all-k primal checker, changing k=2,n=100 support from [50,0] to duplicated [0,0] caused a nonzero AssertionError; the mutated copy was removed. The earlier n=11 and n=26 exact-target mutation tests also failed as expected.

**Audit limitation:** Neither 18 finite rational instances nor six exact algebraic checks imply the infinite-family theorem; the written proofs of the transfer expansion, globally corrected Chebyshev dual, Lagrange derivative quadrature and continuity/positivity of exact rational class measures do. This project has not obtained human peer review, formalized the arguments in a proof assistant, or verified historical world-first novelty.


## New rank-six and simultaneous all-rank audit (2026-10-08 UTC)

All four proof inputs were downloaded anew in the clean VPS replay directory from immutable Git commits, without using numeric discovery sources:

| Public proof input | Pinned commit | SHA-256 of downloaded bytes |
|---|---|---|
| [check_k5_11_14.py](check_k5_11_14.py) | [6dd88f6](https://github.com/mxym/math/commit/6dd88f6c7b9aa93baff5a905e5f339ad783f8c11) | 9ced5bfa4a9fa634b568d90a3742b02db143d4ec40300cd59bc13d00cb78d7b6 |
| [check_k5_15_40.py](check_k5_15_40.py) | [346267e](https://github.com/mxym/math/commit/346267ea1b7a8d09b4c283d727ca4e079d7a231a) | b122e12b4fe20acc257fd82c60f84316f7a07385369025808fd1bab49653c359 |
| [certificates/k5_n15_40.json](certificates/k5_n15_40.json) | [346267e](https://github.com/mxym/math/commit/346267ea1b7a8d09b4c283d727ca4e079d7a231a) | 16623243b5412135542b3148d2872fc70feb31129ddd79cc1f15843373b687f3 |
| [check_all_rank_trace_kernel.py](check_all_rank_trace_kernel.py) | [72af1c6](https://github.com/mxym/math/commit/72af1c6dbc719dd38398ec6dca389ab304185fcc) | 2341b55c2bacf9409720208dd2bb892399b059da94997ee14407ad3c9e31c100 |

Reproduce directly from the public repository root with ordinary Python:

~~~sh
python3 notes/johnson-short-cycle-spectrum/check_k5_11_14.py
python3 notes/johnson-short-cycle-spectrum/check_k5_15_40.py
python3 notes/johnson-short-cycle-spectrum/check_all_rank_trace_kernel.py
~~~

Fresh replay terminal summaries (individual degree values are in [the rank-six paper](RANK_SIX_EXACT_11_40.md)):

~~~text
PASS rank-six k=5 n=11: sharp C=5/14
PASS rank-six k=5 n=12: sharp C=5/14
PASS rank-six k=5 n=13: sharp C=5/14
PASS rank-six k=5 n=14: sharp C=5/14
ALL FOUR DEGENERATE RANK-SIX CERTIFICATES PASS; types=361
PASS k=5 n=15 states=167 sharp=29275/81761
...
PASS k=5 n=40 states=10584 sharp=6198650425199/13306819837380
ALL 26 RANK-SIX EXACT CERTIFICATES PASSED; STATES=82377
PASS degree-six polynomial identity for n=6..100
PASS every orbital k=1..n for n=6..21
PASS exact full trace-rank floor(n/2)+1 for n=6..30
ALL-RANK TRACE-KERNEL TESTS PASSED
~~~

The 30 new rank-six certificates exhaust a total of **82,738** feasible five-short-cycle types with exact integer/Fraction arithmetic. The primal and dual weights are independently reconstructed, and every represented class is realizable by a concrete permutation. The all-rank trace checker tests the exact degree-six polynomial identity, every subset rank in small degrees, and independent rational rank witnesses; the [paper](ALL_RANK_TRACE_KERNEL.md) proves the corresponding all-degree results algebraically, not by extrapolation.

**Negative controls:** All three new scripts reject optimized Python mode (-O). Modifying the rank-six n=15 target fraction from 29275/81761 to 29275/81762 in a temporary JSON input caused a nonzero AssertionError. Modifying the n=11 exceptional dual coefficient 121/300 to 121/301 in a temporary checker also caused AssertionError. The original certificate input was restored, and its pinned SHA-256 was verified.

**Scope:** The exact rank-six table covers n=11,...,40; larger n are not claimed. The simultaneous all-rank four-class relation proves a **lower bound** 5/14 for all n>=6. Whether this lower bound is the exact all-ranks sharp value for every n remains **conjectural** despite finite numerical LP observations. No optimizer outputs, claimed historical priority, or outside peer review are used in the proofs.
