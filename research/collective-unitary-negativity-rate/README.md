# Collective-unitary logarithmic negativity: exact rate for every spectrum

**Complete written analytic argument; not Lean-formalized or externally peer reviewed.** The proof uses Tropp's published matrix Bernstein inequality. Exact ancillary checks are supplied separately and are not presented as a certificate of the full analytic theorem.

Let $\rho$ be any density matrix on $\mathbb C^m\otimes\mathbb C^n$, with $2\le m\le n$ and spectrum $p$, including zero eigenvalues. Set

\[
 E_k=\max_U\log\|(U\rho^{\otimes k}U^*)^{\Gamma_{A^k:B^k}}\|_1.
\]

The [proof](PROOF.md) establishes

\[
 \lim_{k\to\infty}\frac{E_k}{k}
 =\min_{1\le\alpha\le2}
 \frac{\log m+(\alpha-1)\log n+\log\sum_i p_i^\alpha}{\alpha}.
\]

For equal local dimensions $m=n=d$, this is exactly
$\frac12\log(d^2\operatorname{Tr}\rho^2)$. Every state other than the maximally mixed state has positive rate. In unequal dimensions there can be a strictly interior optimizer: the proof gives an exact $2\times8$ example with $\alpha_*=3/2$.

The same rate is attainable by permuting the tensor-power eigenvalues into a fixed blockwise Bell basis (a complete generalized Bell basis in the balanced case); no continuous optimization of the output eigenvectors is needed for the exponent. This is an existence result, not an efficient search algorithm for the permutation.

A finite-dimensional theorem supports the lower bound. If $L_r$ is the sum of the $r$ largest eigenvalues and $N=ab$, define $T=\max_r\min\{a,\sqrt{N/r}\}L_r$. The unitary-orbit maximum of the partial-transpose trace norm lies between $T/[12\log(8N)]$ and $H_NT$, where $H_N$ is the harmonic number. The proof constructs a Bell-basis projection with controlled partial-transpose norm and uses spectral types to match a Schatten-norm upper bound.

## Research boundary

This is a regularized global-unitary problem, not a local entanglement-distillation rate. It does not solve the finite-copy APPT purity conjecture, APPT=AS, the exact one-copy negativity maximum, or efficient circuit synthesis. Prior qualitative finite-copy activation is credited to Kondra et al.; recent finite-spectrum bounds are credited to Abellanet-Vidal et al. No exhaustive historical-priority claim is made.

The preceding qutrit purity proof and preprint are already public: immutable `appt-qutrit-purity-complete-v1`, immutable `appt-qutrit-purity-preprint-v1`, DOI **10.5281/zenodo.23269470**. None of those frozen artifacts is changed here.

## Check the ancillary identities

```sh
python3 check.py --report verification/exact-checks.json
python3 -O check.py --self-test
```

Only Python's standard library is needed. The checker works in exact cyclotomic fields for Bell matrices of local sizes 2, 3, 4, and 5, checks variance identities, rational Bernstein constants, multinomial type counts, and escort algebra. It rejects changed Bell phases, an incorrect transpose, a wrong covariance factor, and an altered Bernstein coefficient. Those finite checks support, but do not replace, the arbitrary-dimension argument.

See `RESEARCH_LOG.md` for selection, literature comparisons, and unresolved neighboring problems. Work was carried out with AI assistance and is supplied for independent mathematical review.
