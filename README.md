# Exact alternating eight-cycle quantum max-flow in every odd dimension

**Yongxian Zhang** (ORCID [0009-0000-3864-3536](https://orcid.org/0009-0000-3864-3536)). Version 1.1.0. AI-assisted proof development and internal checks; no external peer review claimed.

For the complex periodic eight-cycle with a single shared tensor and both dimensions equal to odd \(q\), the maximum alternating flattening rank is
\[
F_8(q)=
\begin{cases}
q^4& q\equiv1\pmod4,\\
q^4-1&q\equiv3\pmod4.
\end{cases}
\]
This completes the odd-dimensional case; general even dimensions remain open. It supersedes the partial odd-dimensional bound of v1.0.0 without changing its immutable files.

- [All odd dimensions, including full rank in the 1 modulo 4 class](eight-cycle-odd-poles/AllOddDimensions.md)
- [Exact rank in the 3 modulo 4 class](eight-cycle-odd-poles/README.md)
- [Base construction and certificates](eight-cycle-charge-and-hub/README.md)
- [Second-jet proof](eight-cycle-second-jet/README.md) and [sector addendum](eight-cycle-second-jet/Addendum.md)

The proof incorporates reproducible rational-function identities and exact modular checks, then a characteristic-zero argument that is uniform in the dimension. Verify the scoped archive with `sha256sum -c SHA256SUMS`.
