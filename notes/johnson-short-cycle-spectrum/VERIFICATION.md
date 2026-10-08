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
