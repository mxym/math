# Which pairs of bases are most incompatible under jointly measurable noise?

A pair of mutually unbiased bases is among the most incompatible orthonormal-basis pairs in every complex dimension $d\ge 2$, when the noise pair must itself be jointly measurable. This answers the corresponding question of [Designolle, Farkas and Kaniewski (DFK), §IV.C.2, after Eq. (84)](https://arxiv.org/pdf/1906.00448).

The quantity minimized here is the largest fraction of the original measurements that can be retained. For **every** pair of bases in $d\ge3$, the visibility
$$
\eta=\tfrac12(1+1/\sqrt d)
$$
is achievable with compatible noise. For mutually unbiased bases it cannot be exceeded. The distinct qubit minimum $2(\sqrt2-1)$ was already known. The result does not classify all extremizers or optimize over arbitrary POVMs with unrestricted outcome counts.

**What the proof adds.** DFK already knew the sharp value on mutually unbiased bases and a positive joint measurement for the mixture at this visibility for arbitrary bases. But a parent for the mixture alone only establishes *generalized* robustness. Here we give the missing second parent: a joint measurement for the **specific pair of noise marginals** left by that mixture. These are not required to be uniform or state independent. In particular, this is separate from the repository's [binary/$m$-outcome uniform-noise result](../binary-m-outcome-compatibility/README.md).

[Complete proof](PROOF.md) · [Sources and attribution](SOURCES.md) · [Independent internal review](REVIEW.md)

## Reproduce the checks

With Python 3.8+ (standard library) in this directory:

```sh
python3 -O verify.py
python3 -O independent.py
sha256sum -c SHA256SUMS
```

The [recorded outputs](CHECKS.txt) cover exact matrix tests on complex bases and an independent check in the algebra of two projective measurements. The argument for all dimensions is analytical, not an extrapolation from these tests.

**Status:** AI-assisted mathematical research, independently reviewed internally by AI. Not externally peer reviewed or formally verified; no worldwide priority claim.
