# How many outcomes or dimensions does a universal joint-measurability construction need?

There are n-setting compatibility structures for which **every** realization by q-outcome measurements in Hilbert dimension d must satisfy

    q d² ≥ c · 2^(n/2) / n^(9/4)

for an absolute c>0 and all sufficiently large n. The same structure excludes all cheap pairs (d,q) simultaneously. The lower bound applies with overwhelming probability to the explicitly specified random middle-layer model, not to every complex or every probability distribution on complexes.

* Holding d≥2 fixed, the worst-case number of outcomes per **individual setting** has base-two exponential rate at least 1/2.
* Holding q≥2 fixed, the worst-case dimension has rate at least 1/4, with lower bound c_q 2^(n/4) n^(−7/8).

These are rates in the sense of a lower bound on a liminf, not matching exponents. Prior constructions establish finite exponential upper bounds: binary outcomes with growing dimension, or a qubit with growing outcome count. This result counts possible realizations of *all faces at once* using one family of incompatibility witnesses; it is not a lower bound on outcomes of a parent for a single compatible family, and it gives no small explicit hard complex.

See [proof](PROOF.md), [sources and scope](SOURCES.md), [independent internal review](REVIEW.md) and [exact regression results](CHECKS.txt). [PR #118](https://github.com/mxym/math/pull/118) supplies the positive variable-outcome qubit construction; [PR #119](https://github.com/mxym/math/pull/119) supplies a small explicit binary-qubit obstruction. Neither alone yields this uniform resource tradeoff.

AI-assisted research with internal adversarial review, not external peer review. No guarantee of priority. Reproduce the supplementary finite checks with standard-library Python: `python -B -O verify.py` and `python -B -O independent.py`.
