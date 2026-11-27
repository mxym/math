# An unconditional classification of length-six Salem polynomials

This archive rules out a Salem root in (1, 1.01] for a length-six Salem polynomial, where length is the sum of absolute coefficients. In conjunction with [McKee and Smyth, Theorem 2 and Tables 2–3](https://arxiv.org/abs/2605.19013), the twelve families and 126 sporadic polynomials are therefore an unconditional list. The least Salem number admitting a polynomial of this length is Lehmer's number; this does not settle the unrestricted Lehmer problem.

- `FactorLengthSixSalemClassification.md`: proof, references, and verification details.
- `verify_length_six_salem_cutoff.py` and `verify_length_six_salem_classification.js`: exact primary replays (Python 3 and Node.js).
- `verify_salem_length_six_independent.py`: independently structured exact replay (Python 3 with NumPy), including a larger search bound.
- `SHA256SUMS`: fingerprints of all four research payloads.

Pinned research commit: `8c18b45b54d27ac69886527cf7030ce0c5a63d41`.
