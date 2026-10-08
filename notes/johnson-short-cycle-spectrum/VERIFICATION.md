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


## Closure audit: exact 5/14 theorem for every n>=6 (8 October 2026)

**Result:** The previously conjectural all-subset simultaneous-image atom/TV modulus is **exactly 5/14 for every symmetric group of degree n>=6**, and equivalently for its single middle-rank subset action. The full written proof is [ALL_RANK_SHARP_FIVE_FOURTEENTHS.md](ALL_RANK_SHARP_FIVE_FOURTEENTHS.md). Unlike earlier exploratory finite LP observations, the theorem relies on an exact **global rational dual** and a matching explicit **four-class rational primal**, with no unverified numerical step. It further proves a universal 5/14 upper bound for any faithful finite permutation subgroup under matching all-subset image marginals, and characterizes the contact-supported equality class masses.

**Pinned public inputs and byte hashes**, independently downloaded from raw.githubusercontent.com into the authorized VPS replay directory:

| Input | Immutable commit | SHA-256 |
|---|---|---|
| Primary cleared-integer dual checker | [27dd9a5](https://github.com/mxym/math/commit/27dd9a53ebad814cca2448910926199e7b69deed) | 9eb31dcc9f70b3d1c3ae898dfb9568b5517f98a1ce3c645c37994784f5978472 |
| Independent Fraction and rational-Gaussian dual checker | [d70f300](https://github.com/mxym/math/commit/d70f300c2d5601d073fde02e3a2f844395d6721f) | 2c69d99b2465047ae2f5cf1a5c0eacfd52ffef702b492daecd9b4162a08c1371 |
| Negative-control runner | [c13fe63](https://github.com/mxym/math/commit/c13fe635d40327faa21c769becaf076bbb8e77e3) | c2cf6964c5ea893c0e94ff178c89fe24da2ea5de686125f6262ac469ddbf6b66 |
| Proof note, including faithful-subgroup theorem and equality rigidity | [0e7ae9b](https://github.com/mxym/math/commit/0e7ae9b7831c7ceaa4a67141ada96969841bbcf4) | The immutable Git blob can be retrieved directly at this commit |

**Replay from public repository root** with standard-library Python 3 (no optimizer, SymPy or external dependencies):

~~~sh
python3 notes/johnson-short-cycle-spectrum/check_allrank_sharp_five_fourteenths.py
python3 notes/johnson-short-cycle-spectrum/check_allrank_sharp_five_fourteenths_independent.py
python3 notes/johnson-short-cycle-spectrum/check_allrank_sharp_five_fourteenths_negative_controls.py
~~~

**Observed complete exact replay assertions:**

~~~text
EXACT CONTACTS: Phi(2)=Phi(3,3)=9/14; Phi(4)=1.
FINITE PARTITIONS (all cycle lengths >=2, moved<=41): 44582
EXACT GLOBAL FINITE MINIMUM: 9/14 at (2,)
EXACT GLOBAL FINITE MAXIMUM: 1 at (4,)
UNBOUNDED TAIL: sum |weight| rho^21 < 7/50: True
ALL-RANK 5/14 UNIVERSAL DUAL CERTIFICATE PASS.

EXACT RATIONAL COEFFICIENTS RECONSTRUCTED:
  [239124191777/1120000000, -344827/1000,
   138704974923/490000000, -205889/1000,
   430736498793/7840000000]
INDEPENDENT FRACTION PARTITIONS REPLAYED: 44582
LOWER CONTACT SHAPES: [(2,), (3, 3)]
UPPER CONTACT SHAPES: [(4,)]
TAIL < 7/50: True
INDEPENDENT UNIVERSAL 5/14 CHECKER PASSED

EXPECTED REJECTION: modified rational input
EXPECTED REJECTION: finite-tail gap
EXPECTED REJECTION: tail exponent
EXPECTED REJECTION: false strict tail
ALL NEGATIVE CONTROLS PASS; ORDINARY AND -O BOTH EXPLICITLY CHECKED
~~~

The first program implements an **integer cleared-denominator inequality** on every partition; the second independently **reconstructs the dual coefficients** using exact rational Gaussian elimination and uses its own partition generator and Fraction products. Both certify exactly **44,582** nontrivial partitions of moved counts 2,...,41, the unique upper and lower contact shapes, and the exact rational bound
\(\sum_i|\alpha_i|[q_i^2+(1-q_i)^2]^{21}<7/50\).
The *mathematical* power-mean proof then covers every moved count at least 42, so **no infinite or unchecked cycle-type range is left**.

**Negative controls and Python optimization:** All checks use explicit ArithmeticError/require paths, **not Python assert statements**. Running the primary checker under Python's -O flag continues to execute every check and passes, so assertion-stripping does not silently disable validation. Four isolated mutations—altered integer weight, broken finite/tail cutoff, altered tail exponent, and a deliberately false strict tail target—were each rejected with nonzero ArithmeticError. The untouched public files were not modified by negative controls.

**Mathematical trust boundary:** The machine-checkable portion is the exact, finite list of inequalities and the strict rational tail threshold; its completeness follows from the explicit nonincreasing-partition recursion and analytic tail inequality in the paper. The converse four-class measure identity, faithfulness/group translation, middle-rank inclusion-matrix argument, and support/class-mass equality theorems are **written mathematical proofs** not inferred from the finite replay. Model-assisted research; **no external peer review, Lean formalization, or mathematical priority adjudication** is asserted.


## Alternative reciprocal-node certificate (independently certified)

A *second* rational dual, with evaluation parameters \(1/2,1/3,1/4,1/5,1/6\) and all weights sharing the much smaller integer denominator \(30,625\), independently proves the same global 5/14 bound. Its certificate covers **every** partition with 2--43 moved vertices, or **63,260** nonincreasing partitions with parts >=2; a strict rational bound \(\sum_i|\widetilde\alpha_i|\widetilde\rho_i^{22}<7/50\) proves every moved count >=44. This is a different **mathematical dual** from the 44,582-partition original, not merely a second implementation of the same rational numbers.

**Fresh fixed-commit VPS source replay:**

| Exact proof input | Public immutable commit | SHA-256 |
|---|---|---|
| [Reduced-denominator integer checker](check_allrank_sharp_five_fourteenths_small.py) | [562548b](https://github.com/mxym/math/commit/562548b37d280890cd19c6899a103878dbe2fb58) | a5d6cc2abcaa6350be540540b1f4e0104e171d887af0972324310afaa59f9a86 |
| [Independent reconstructed Fraction checker](check_allrank_sharp_five_fourteenths_small_independent.py) | [91cfe61](https://github.com/mxym/math/commit/91cfe61682a60c82bdcc7d8c57d82be1fb7695a7) | 8c8d856c3a2f9df90f784ab3044d46cd48d7cdd3d7bfe7a6bc62055710085a0c |
| [Adversarial mutation check](check_allrank_sharp_five_fourteenths_small_negative_controls.py) | [f5fe9f5](https://github.com/mxym/math/commit/f5fe9f59da2dc06e4e7b0c03712ad1de94de1e86) | 3157da6f924d444685e4a6a998a4e8873593602c930c77d17ef7c4bd1dab8b4b |

**Reproduce in ordinary Python 3:**

~~~sh
python3 notes/johnson-short-cycle-spectrum/check_allrank_sharp_five_fourteenths_small.py
python3 notes/johnson-short-cycle-spectrum/check_allrank_sharp_five_fourteenths_small_independent.py
python3 notes/johnson-short-cycle-spectrum/check_allrank_sharp_five_fourteenths_small_negative_controls.py
~~~

**Observed complete audit:**

~~~text
EXACT CONTACTS: Phi(2)=Phi(3,3)=9/14; Phi(4)=1.
RATIONAL INPUT DENOMINATOR: 30625
FINITE PARTITIONS (all cycle lengths >=2, moved<=43): 63260
EXACT GLOBAL FINITE MINIMUM: 9/14 at (2,)
EXACT GLOBAL FINITE MAXIMUM: 1 at (4,)
UNBOUNDED TAIL: sum |weight| rho^22 < 7/50: True
ALL-RANK 5/14 UNIVERSAL DUAL CERTIFICATE PASS.

EXACT RATIONAL COEFFICIENTS RECONSTRUCTED:
[576642/4375, -354, 13334928/30625, -289, 2344953/30625]
INDEPENDENT FRACTION PARTITIONS REPLAYED: 63260
LOWER CONTACT SHAPES: [(2,), (3, 3)]
UPPER CONTACT SHAPES: [(4,)]
TAIL < 7/50: True
INDEPENDENT SMALL-DENOMINATOR 5/14 CHECKER PASSED

EXPECTED REJECTION: modified rational input
EXPECTED REJECTION: finite-tail gap
EXPECTED REJECTION: tail exponent
EXPECTED REJECTION: false strict tail
ALL SMALL-DENOMINATOR NEGATIVE CONTROLS PASS; ORDINARY AND -O BOTH EXPLICITLY CHECKED
~~~

The checker uses exact integer comparisons with a common parameter denominator \(60\) and weight denominator \(30,625\). The independently authored Fraction-check path **reconstructs** the missing three weights from fixed integers \(-354,-289\) and the exact cycle-contact equations, and checks every possible short moved cycle list. The analytic power-mean proof from Section 3 of the main paper covers all unbounded cases; no finite-LP extrapolation or heuristic inequality enters the result. Both literal-source replays and all four negative-control mutations passed; Python optimized mode does not disable any verification step.
