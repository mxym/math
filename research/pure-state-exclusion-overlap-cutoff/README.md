# Sharpness of the pairwise overlap guarantee for quantum state exclusion

For how many pure states is the overlap test of [Johnston, Russo and Sikora, Corollary 5.4](https://doi.org/10.22331/q-2025-02-04-1622) sharp? In ordinary one-copy state exclusion, a measurement must be able to rule out its matching state without error; zero effects are permitted. The published test guarantees exclusion when every **squared** pairwise overlap is at most $(n-2)/(2(n-1))$.

* **Five states:** the guarantee is sharp. A cyclic five-state ensemble in complex dimension three meets the squared cap $3/8$, and arbitrarily small perturbations give ensembles that cannot be perfectly excluded. The endpoint ensemble itself can be excluded.
* **Six or more states:** for every fixed $n\ge6$, there is a positive amount by which the cap can be raised in every finite dimension. This argument does not compute the best cap or an explicit improvement.

Together with the known cases $n=2,3,4$, this locates the qualitative cutoff at five. The note combines an explicit five-state sharpness witness with a reduction of near-failures to an equiangular qutrit configuration. From six on, a classical projective Jacobi kernel already excludes that boundary; from seven on, Balla’s spectral cubic also does so. Both deductions and a separate elementary projection proof are included. For ten or more the [trureturing project](https://the-omega-institute.github.io/trureturing-mdbook/Problems/johnston-russo-sikora-2025-antidistinguishability-tightness.html) already gives an explicit stronger threshold. No priority claim is made for a qutrit line construction, a state-exclusion criterion, or a new line classification.

Read the [proof](PROOF.md), [source comparison](SOURCES.md), and [independent internal audit](REVIEW.md). Both implementations use Python and SymPy 1.14; no semidefinite program or floating-point experiment is used. To reproduce the algebraic checks from this directory:

```sh
python verify.py
python independent.py
sha256sum -c SHA256SUMS
```

The note was written with AI assistance and checked in a separate internal AI review. It has not been externally peer reviewed; the source comparison does not establish worldwide priority.
