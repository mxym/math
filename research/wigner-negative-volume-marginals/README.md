# Joint Wigner negative volume can be less than the sum of the marginal volumes

Cerf, Hertz and Van Herstraeten [reported numerical evidence](https://arxiv.org/html/2310.19296v2#S4.SS2) that the imaginary part of complex Wigner entropy might be superadditive for general correlated two-mode states. With their logarithm convention it is $\pi$ times the Wigner negative volume $N(W)=\int(-W)_+$. This note gives an explicit counterexample:
$$
N(W_{12})<N(W_1)+N(W_2).
$$

The state is a finite-energy mixture of product number states, supported on photon numbers 0 through 64 in each mode. No entanglement or numerical phase-space integration is needed. The [proof](PROOF.md) writes down its rational density matrix and certifies the strict inequality by comparing the regions where the two marginal Wigner functions have equal or opposite signs. The proved product-state identity and the monotonicity of negative volume under partial trace remain valid.

This is **not** the vacuum-entropy conjecture: that concerns the real Shannon entropy of Wigner-positive states, whose negative volume is zero. See [sources and comparisons](SOURCES.md), including the directly checked [September 2026 Zenodo manuscript](https://zenodo.org/records/22941099).

### Verification

Both Python scripts use only the standard library. They check the finite matrix arithmetic and polynomial identities by different methods; the continuous tail estimates are proved in the text.

~~~sh
sha256sum -c SHA256SUMS
python3 -B -O verify.py
python3 -B -O independent.py
~~~

[Expected output](CHECKS.txt) · [Independent checks of the proof](REVIEW.md)

**Status:** AI-assisted research with independent internal mathematical review, not external peer review or formal verification. No claim of worldwide priority or of an experimentally resolvable gap.
