# Exact Eisenstein irreducible-component bounds and sharp periodic sieves

**Research note, 7 October 2026.** [Full theorem statements and
proofs](paper.md) · [independent integer checker](code/check.py) ·
[finite proof witnesses](code/) · [replay results](results/replay.txt) ·
[scope and proof audit](AUDIT.md).

We study the graph of *elements* irreducible in
\(\mathbb Z[\omega]\), with \(\omega^2+\omega+1=0\), for the six
unit steps and the eight nearest coefficient-lattice steps.

| Step set | Exact largest irreducible component | Other components | Least finite principal-sieve scalar period |
| --- | ---: | ---: | ---: |
| Six Eisenstein units | 48, uniquely attained | at most 6 | 6 |
| All eight nonzero \(\{-1,0,1\}^2\) coefficient steps | 132, uniquely attained | at most 74 | 546 |

The optimal six-step sieve uses \(2\) and \(1-\omega\). Its allowed
lattice is a disjoint union of six-cycles, also proved analytically.
The eight-step full sieve uses the six generators
\(2,1-\omega,3+\omega,2-\omega,4+\omega,3-\omega\).
At period \(546\), **four irreducible generators** are necessary and
sufficient; all four minimal lists are classified in Section 5 of the
paper. The four-generator minimality statement is *not* extended to
arbitrary composite generators.

The infinite results follow from explicit finite proofs:
333 checked nonzero-displacement walks exclude every squarefree period
below 546; complete partition/closure certificates cover all 298,116
residue pairs modulo 546, with exact quotient-component connectivity
and neighbor closure checks. The exceptional components are closed
finite sets of 54 and 138 lattice points, with 48 and 132 verified
irreducibles respectively. All arithmetic checks use integers only.

## Reproduction

From the directory containing this README:

    python3 code/check.py
    python3 -O code/check.py
    python3 code/self_test.py
    python3 -O code/self_test.py
    sha256sum -c SHA256SUMS

A successful main replay ends with **ALL EXACT CERTIFICATES VERIFIED**.
A successful tamper-test replay ends with
**ALL TAMPER AND IRREDUCIBILITY TESTS PASSED**.
No solver, network connection, Lean, SageMath or nonstandard Python
package is required. The committed compressed JSON witness files
contain the actual finite data; the checker never invokes the generator
and does not rely on a Boolean result stored in them.

The nontrusted producer is [code/generate.py](code/generate.py); its
exact options and the checkpoint hashes are in [AUDIT.md](AUDIT.md).
Do **not** infer that rerunning a generator verifies a theorem: the
published mathematical proof and separate checker establish the
infinite conclusions.

## Relationship to other results and verification scope

This is a continuation of
[entry 002](../../preprints/002-quadratic-order-moats/README.md).
The method is motivated by the [OpenAI/math Gaussian-prime manuscript
(family 028)](https://github.com/openai/math), pinned at
adc7f1241b42e322a6451854ab7e4b4c146bf78a, and the separate
Gaussian and real-quadratic period certificates in entry 002 v4.
The assertions here concern Eisenstein integers, with their own
complete arguments and proof witnesses. Other original OpenAI results
and older 002 releases are unchanged.

This is a model-assisted written proof with independently replayable
finite arithmetic, **not** a Lean formalization, external peer
review, worldwide novelty determination, or claim of first priority.
