# Verification and limitations

Separate internal AI review recomputed the operator block square and its Hilbert–Schmidt norm, the two equality conditions at the threshold, feasibility of the two-class witnesses, the truncation $C\le0$ in the scalar profile, the correct stationary root, and the half-density closed form. It also checked the convention against Theorem 2.7 of the original v2 paper. This is not external peer review, a proof-assistant formalization, or an external reproduction of that paper's calculations.

To reproduce the arithmetic checks, from this directory run:

```sh
python3 verify.py
sha256sum -c SHA256SUMS
```

The verifier uses only the Python standard library. It directly enumerates ordered four-label patterns on 30 exact rational kernels and compares them to the **block identity** and to its compressed upper bound. It compares the labelled and undirected conventions by independent finite cycle enumeration on nine simple graphs. It verifies the radical identities for the threshold and half-density maximizing root exactly in the relevant quadratic fields. Output is recorded in [CHECKS.txt](CHECKS.txt). These finite checks supplement rather than replace the proofs in [THRESHOLD.md](THRESHOLD.md) and [PROFILE.md](PROFILE.md).
