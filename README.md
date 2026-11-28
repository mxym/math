# Uniform finiteness of nonadjacent equal-offset binomial repetitions

This is the reproducibility slice for the **ordinary positive Pascal-integer** result
\[
 {n\choose k}={n-d\choose k+d},\qquad
 k\ge1,\quad d\ge2,\quad n\ge k+2d.
\]
There are only finitely many such triples jointly in \(n,k,d\), with neither entry required to be in the left half. Thus, on all sufficiently large antidiagonals \(n+k=T\), the only possible repeats of a value \(>1\) are the adjacent, classical [Lind–Singmaster family](https://www.fq.math.ca/Scanned/13-4/singmaster.pdf). This does not classify the finite exceptions, prove their set empty, bound the unrestricted number of representations of a binomial coefficient, or settle the affine polynomial question for signed and exterior integer points.

## Proof map

1. [IndependentAsymptoticRowBound.md](IndependentAsymptoticRowBound.md) is a nonauthor rederivation of \(d>\sqrt{u}\) for sufficiently large \(u=n-k\), using the signed expansion and an absolute quarter-lattice gap. It does not use the constants table in the prior signed bound or any finite enumeration.
2. [FactorSingmasterPrimeSeparation.md](FactorSingmasterPrimeSeparation.md) uses precisely that row bound, joint square-root interval prime-factor mass and the golden-ratio spacing argument to exclude every moderately sized offset in a sufficiently large solution. A prime in the backward short interval forces \(k\le n^{21/40}\) in the other branch. Reflecting the shorter row gives \(k<s<3k\), with \(s=(n-d)-(k+d)\). The same note separately proves the sharper near-edge bound and rules out \(s=k+1\) for all \(d\ge1\).
3. [FactorSingmasterUniformEqualOffsetFiniteness.md](FactorSingmasterUniformEqualOffsetFiniteness.md) closes the whole branch by the classical consecutive-integer prime-deletion argument; it uses steps 1–2 only up to \(k\le n^{21/40}\) and \(k<s<3k\), not a computational cutoff.
4. The [earlier signed bound](FactorSingmasterBalancedShiftDrift.md) and its exact finite replay are included as additional context. This run of shifts \(2\le d\le256\) is a separate finite result and does not enumerate the exceptions to the uniform theorem.

The analytical inputs are [Baker–Harman (1995), formula (1.6) and Corollary 2](https://doi.org/10.4064/aa-73-2-119-145), and [Baker–Harman–Pintz (2001), Theorem 1](https://doi.org/10.1112/plms/83.3.532). They are used in their published uniform forms and do not require assuming the Riemann hypothesis. [Jenkins (2016), §§3–4](https://math.colgate.edu/~integers/q69/q69.pdf) treats the fixed-offset direction, including the fixed case \((2,2)\) in §3, and discusses finiteness of integral points on more general affine curves. The current theorem concerns the positive binomial problem motivated by that work, not all integral points on those curves. See the [audit and provenance](RELEASE_NOTES.md).

## Reproduce

Run in this directory with normal Python, not with the optimization switch that disables assertions. The theorem is analytical given the published prime inputs, and the small exact companion scripts check selected arithmetic and finite cases without computing the asymptotic threshold.

```sh
sha256sum -c MANIFEST.sha256
python3 verify_independent_asymptotic_row_bound.py
python3 verify_singmaster_prime_separation.py
python3 verify_factor_singmaster_balanced_shift_drift.py --max-shift 256
```

The last command can also be run with a smaller bound to replay a prefix. There is no dependence on external certificate data and no claim of Lean formalization.
