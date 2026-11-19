# A 144-vertex compatibility graph impossible for binary qubit measurements

Every finite joint-measurability complex has a [single-qubit realization with sufficiently many outcomes](https://github.com/mxym/math/pull/118). **Two outcomes cannot suffice in general.** For any families of binary qubit measurements, put a + at each compatible cross-pair and a − at each incompatible one. This sign table always admits a real matrix of ordinary rank at most 11 with precisely those *strict* signs. A symmetric 144-by-144 Hadamard sign table with diagonal + has sign-rank at least 12. Reading its positive off-diagonal entries as edges gives the promised graph and its flag complex.

* [Eleven-feature lemma and 256-vertex bipartite parity example](PROOF.md). Includes unrestricted biases, complex effects, and boundary cases.
* [144-vertex graph](SYMMETRIC.md). An explicit order-12 Paley seed gives one set of 144 measurements rather than two families of 128.
* [Scope and prior work](SOURCES.md), [independent internal review](REVIEW.md), [exact checks](CHECKS.txt).

The two leading ingredients are existing results: the Busch–Schmidt pair criterion and Forster's sign-rank inequality. The Hadamard constructions are also classical. The result does not give a smallest nonrealizable graph or a sharp sign-rank bound, and does not contradict the unrestricted finite-outcome result. This work was AI-assisted and internally audited. It has not been externally peer reviewed; no priority guarantee is made.

Reproduce with Python 3.10 or later, standard library only: run `python -B -O verify.py`, `python -B -O independent.py`, `python -B -O symmetric_check.py`, and `python -B -O independent144.py` in this directory. The testers complement the general proof rather than establishing it by finite samples.
