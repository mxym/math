# Mathematical research · mxym/math

Papers, proofs you can check, and open problems studied by Yongxian Zhang (张永贤).

[中文](README.md) · **English**  
[Browse by field](RESEARCH.md) · [Results index](SOLVED_PROBLEMS.md) · [Manuscript catalogue](CONTENTS.md)

<a name="preprints"></a>
<a name="results-with-complete-written-proofs"></a>

## Selected results

| Question | What was proved? | Evidence |
| :--- | :--- | :--- |
| **Bapat’s q-permanent conjecture** | The q-permanent can decrease as q increases. One explicit 200 × 200 complex positive-definite matrix disproves the monotonicity conjecture. | [Counterexample and Lean proofs](submissions/arxiv-2026-10/bapat-q-permanent-counterexamples/README.md) · [DOI](https://doi.org/10.5281/zenodo.23252928) |
| **Maximum purity of a quantum state** | For every n ≥ 3, the maximum purity of an absolutely PPT (APPT) state on a 3 × n system is determined exactly. Explicit states attain it. | [Paper and Lean proof of the main theorem](preprints/appt-qutrit-purity-2026-10/README.md) · [DOI](https://doi.org/10.5281/zenodo.23269470) |
| **Infinite log-concavity of cycles** | The absolute coefficients of a cycle’s chromatic polynomial are infinitely log-concave exactly for cycles with 3 to 11 vertices. Every longer cycle fails. | [Paper and proof of the classification](preprints/lean-certified-2026-10/cycle-chromatic-classification/README.md) · [DOI](https://doi.org/10.5281/zenodo.23249722) |
| **Walsh supports of Boolean functions** | Count two supports as the same shape if an affine map identifies them. There is just one shape of size 21, but at least two at every size from 22 onward. | [Theorem and frozen release](https://github.com/mxym/math/releases/tag/walsh-support-last-unique-cardinality-v1.0.0) |

<a name="problems-explored"></a>

## Open problems

- **Does a Conway 99-graph exist?** [An automorphism of order two has been ruled out](research/conway-99-involution/README.md). If the graph exists, it has no nonidentity symmetry that undoes itself when applied twice. Existence remains open.
- **How many equal spheres can touch one sphere in six dimensions?** If the contact points include at least 38 of the 40 roots of a single D₅ equator, [there are at most 72 in total](https://github.com/mxym/math/blob/71206c3b40a6fd1b16bb8a14cf29ed9b39efbbce/research/euclidean-tensor-geometry/KissingPartialD5D6Equators.md). The unrestricted kissing number remains open.

[Active research branch](https://github.com/mxym/math/tree/research/euclidean-tensor-geometry) · [Other research attempts](research/research-attempts-20261015/README.md)

## Proof and reproduction

To try one proof, start with the [cycle classification’s Lean project](formalizations/chromatic-cycles-all-n-lean/README.md). From the repository root, run:

```sh
cd formalizations/chromatic-cycles-all-n-lean
lake exe cache get
bash scripts/replay.sh
```

[All Lean projects](formalizations/) · [Verification records](verification/). Each project states its scope; a finite certificate only covers the subproblem it checks.

## Citation, versions, and licensing

Cite the result’s version DOI or frozen commit. [GitHub Releases](https://github.com/mxym/math/releases) · [Zenodo records](releases/ZENODO_RECORDS.md) · [Rights and provenance](NOTICE.md). Archiving is not peer review.

<a name="collective-unitary-logarithmic-negativity-rate"></a>
<a name="global-unitary-extraction-capacity-and-exact-exponents"></a>
<a name="state-independent-extraction-reliability-and-gaussian-threshold"></a>

[Author](AUTHOR.md) · [ORCID](https://orcid.org/0009-0000-3864-3536) · [Contact](mailto:mxymmxym1@gmail.com) · [Previous full English index, including quantum extraction results](https://github.com/mxym/math/blob/19c895a2c64d1306d1011931a291fb22a021b279/README.en.md)
