# Exact periodic twelve-cycle ranks: dimension seven and powers of two

**Yongxian Zhang.** AI-assisted proof development and independent internal checks; no external peer review claimed.

The exact complex alternating rank is 117648 at dimension seven and 262144 at dimension eight in the one-site periodic trace model. In particular, every power-of-two dimension (2^m) for (mge 2) attains full rank, and the previously established binary dimension instead has rank 48. The general twelve-cycle problem is not settled.

- [Dimension seven proof and reproducible checkers](twelve-cycle-q7/README.md)
- [Dimension eight and the complete powers-of-two classification](twelve-cycle-q8/README.md)
- `SHA256SUMS` checks the archive source files.

The C++17 and Node implementations compute the finite-field ranks independently, with explicit integer slices and exact arithmetic; no external data or solver is needed.
