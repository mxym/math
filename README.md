# The sharp optimized quartic energy of eight kissing points

**Yongxian Zhang** · [repository author profile](https://github.com/mxym/math/blob/main/AUTHOR.md) · [ORCID](https://orcid.org/0009-0000-3864-3536)

For eight points on any Euclidean unit sphere separated by at least 60°, minimize the weighted energy with kernel `f(t) = t^4 − t²/4` over probability distributions on the chosen points. **The largest possible value of that minimum is exactly 3/16**. A three-dimensional example attains it. The same formula `3/(2q)` holds at even sizes `q = 2, 4, 6, 8`.

[Proof and scope](KissingSharpEvenEightPointEnergy.md) · [Prior work and attribution](PROVENANCE.md)

At sizes 2, 4 and 6, all equality cases are classified. At eight this also holds if the strict graph has two distinct maximum independent sets: the code then consists of four signed lines with all cross-line products in `{0, ±1/2}`. For the eight graph types with just one maximum independent four-set the manuscript gives a necessary-and-sufficient test of a supplied realization, **not** a complete isometry classification. No global kissing number is claimed.

## Check the finite proof locally

From this directory, with **ordinary Python 3.10+** (no `-O`), run:

```sh
python3 replay.py
```

No network, third-party software or optimization solver is needed for this replay. It checks the file manifest, the three frozen closed-box trees and an independent complete labeled graph census. Expected counts: **31, 65, 99** nodes (16, 33, 50 leaves); **17,640** labeled Ramsey graphs in 3 classes; **1,836** labeled graphs with a specified unique maximum four-set in 8 classes. Read the manuscript as well: the analytic proof for almost antipodal rungs, the exchange argument and the matching lower-bound examples are not delegated to the finite file.

## Optional: regenerate the witnesses

The original checker adds a numerical *discovery* step. Tested with Python 3.12.14, NumPy 2.3.5, SciPy 1.17.0 and threadpoolctl 3.6.0. For a normal run and an independent arithmetic audit of a regenerated transcript:

```bash
python3 verify_kissing_even_eight.py
set -o pipefail
python3 emit-even-eight-audit.py verify_kissing_even_eight.py | python3 independent-even-eight-boxes.py
```

The frozen leaf choices are supplied separately from the independent checker. Numerical LP multipliers alone never certify a box. The checks use integer normalization, exact rational aggregation, outward integer angle bounds and Bernstein coefficients of the quartic on closed intervals.
