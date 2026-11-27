# An all-degree rules-matrix proof of the Easy Coefficients Conjecture

Cusick's original general rules matrix tracks the monomials that have started but not yet finished. It forgets the previous state after a bounded number of bits, so each indexed periodic word gives exactly one closed walk. This links the matrix's **characteristic** roots, with their full multiplicities, to the Hamming-weight sequence of each fixed finite sum of monomial rotation-symmetric functions in arbitrary degrees.

Read [PROOF.md](PROOF.md) for the full argument, including the exact match to the original published construction and the convention for short cyclic periods. Read [SOURCES.md](SOURCES.md) for its distinction from the known existential representation and quadratic result. Verify the original mixed-degree example and the small-parameter regression checks with Python 3.8+:

    python3 -B verify.py

The proof does not depend on experiments. The claim does not extend to arbitrary families chosen independently at each dimension, nor does it assert higher-degree diagonalizability or nonsingularity. The verifier has no external data, third-party dependencies, or network access.
