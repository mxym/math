# Graph-state monogamy: the forbidden-subgraph implication

**Status:** complete written proof with independently replayable exact certificates. No complete Lean verification or external human peer review is claimed.

We prove Fuentes–Keeler–Munizzi–Pollack, arXiv:2511.19585v1, **Conjecture 1**, for every finite qubit graph state: positive tripartite information implies that some locally equivalent graph contains an **induced four-vertex star**.

The structural theorem is a complete classification: a graph has no `K_{1,3}` vertex-minor exactly when every connected component is locally equivalent, up to isomorphism, to one of

`K_1, K_2, P_3, P_4, C_5, W_5`,

where **`W_5` has six vertices** (a five-cycle plus its universal hub). Consequently seven is the sharp size threshold forcing a claw vertex-minor in a connected graph. At most eight local complementations at vertices of a connected seven-vertex subset suffice; deletions can be postponed until the end. This gives four-qubit GHZ extraction on some four vertices by local Clifford operations and computational-basis measurements, not an assertion for four prescribed vertices or unrestricted non-Clifford protocols.

The unbounded theorem is not inferred from a graph catalog. A removable-vertex induction reduces every hypothetical exception to one of **120** nonempty one-vertex extensions of the six representatives. Each extension has an explicit witness of at most three local complementations. The exact cut-rank profiles of the representatives then prove the original entropy implication for every partition; the reduced-density entropy identity is proved directly from graph-state amplitudes.

## Proof and verification

* [Complete definitions, proof, boundary cases and literature](PROOF.md).
* [Finite certificate](certificate.json): 120 extension witnesses and 281 states in six LC-closed claw-free sets.
* [Bit-row checker](check_certificate.py) and [independent edge-set/span/state checker](verify_independent.py). Neither imports the generator or the other checker.
* [Optional witness generator](generate_certificate.py). The generator is not a trusted proof input.
* [Screening and provenance](SCREENING.md); [rights](RIGHTS.md).

Run with Python 3.10 or later, standard library only:

```sh
python3 check_certificate.py
python3 -O check_certificate.py
python3 verify_independent.py
python3 -O verify_independent.py
python3 test_rejection.py
```

The checkers verify all 120 extensions, all 1511 one-step closure transitions, and all 5460 assignments of representative vertices to four labeled blocks. The independent checker regenerates the orbits, computes binary ranks by enumerating spans, and constructs exact graph-state reduced-density numerators for all 126 representative cuts. Those finite quantum diagnostics supplement the all-order written entropy proof; they do not replace it.

## What is not claimed

This is a necessary forbidden-subgraph condition, not an equivalence between star extraction and MMI violation. It does not classify all MMI-satisfying graph states, all equality cases outside the classified claw-free class, mixed/non-stabilizer states, qudit states, or other holographic inequalities. Small representative graph states and the local-Clifford/cut-rank formalism are prior work. The limited source search is not a basis for a historical-priority claim.

Yongxian Zhang (张永贤), School of Computer Science and Engineering, South China University of Technology. Email: mxymmxym1@gmail.com. ORCID: 0009-0000-3864-3536. No external funding. AI-assisted research; no external human peer review.
