# An analytic proof of Bellini's switched-cube conjecture

This proves [Conjecture 14 of Bellini, arXiv:2611.10269v1 §7](https://arxiv.org/html/2611.10269v1#S7). For every odd \(m\ge5\), it classifies all \(m\)-dimensional subspaces of non-bent components of the switched-cube map \(F_a(x)=x^3+a^{-1}\mathrm{Tr}(a^3x^9)\), and proves that none can lift to a Walsh-zero space.

- If \(3\nmid m\), there is exactly one such subspace for each nonzero \(a\), including noncube \(a\); it equals \(a\mathbb F_{2^m}\) exactly when \(a\) is a cube.
- If \(3\mid m\), there are three such subspaces when \(a\) is a cube and none otherwise.
- No map in this family in the stated dimensions is CCZ-equivalent to a permutation. This concerns the specified family, not the existence of APN permutations in general.

The [proof](PROOF.md) is analytic. The main new ingredients are a cubic-coset rigidity lemma in binary dimensions \(m\) and \(m-1\), a reduction from maximal non-bent subspaces to subspaces in the image, and an alternating-minor obstruction to Walsh-zero lifting. The [source notes](SOURCES.md) locate the existing results used in the argument.

## Reproduce the optional checks

These are finite cross-checks, not premises of the proof:

    bash replay.sh

This builds [verify.cpp](verify.cpp) with a C++20 compiler and performs exact finite-field tests for \(m=5,7,9,11\) with cube and noncube parameters. It checks full signed spectra, every spread direction by both direct-spectrum and dual-image criteria, all four- and five-dimensional cube subspaces when \(m=5\), two full component-subspace searches in \(m=5\), and alternating-form kernel degrees and parity moments. No external data or libraries are needed. [RESULTS.txt](RESULTS.txt) records the output.
