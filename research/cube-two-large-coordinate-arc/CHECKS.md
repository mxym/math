# Reproduce the two checks

Run from this directory with Python 3.10 or newer; both programs use only the standard library.

```sh
sha256sum -c SHA256SUMS
python -B -O verify.py
python -B independent.py
```

The first (author) program uses conditional exceptions, so its comparisons survive Python optimization. The second (independent reviewer) program uses assertions, and explicitly refuses to run with optimization; do not pass it -O. It imports no part of the author program. The [archived independent replay](CHECK-OUTPUT.txt) reports 1,023 finite-dimensional cells, 55 interior roots in bounded cells, 7 on the final rays, none at knots, and 8 positive high-dimensional sign certificates with rational error margins. Both programs verify exact integer/rational claims, not a numerical root grid. The analytic bounds and the reduction to those finite claims are in [the proof](PROOF.md).

The independent implementation constructs the finite cells by expanding the homogeneous forms directly rather than first doing Taylor shifts. It uses homogeneous Horner evaluation on the eight high-dimensional certificates. The two programs agree. These replays are internal checks, not a proof-assistant certificate or external peer review.
