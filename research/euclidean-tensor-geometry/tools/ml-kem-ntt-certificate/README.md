# ML-KEM incomplete-NTT algebra certificate

This directory is a small, dependency-free **conformance/assurance tool** for the
public algebra in [NIST FIPS 203](https://doi.org/10.6028/NIST.FIPS.203),
Section 4.3 and Appendix A. It is not a cryptanalytic result, a vulnerability
test, or a claim about the security of ML-KEM.

Run **python3 verify_mlkem_ntt.py**. Expected result:

    PASS: order/factorization/CRT/tables/NTT/inverse/product

## What is certified

Let

\[
q=3329,\qquad n=256,\qquad \zeta=17,\qquad
R_q=\mathbf F_q[X]/(X^{256}+1).
\]

The verifier checks, with exact integer arithmetic:

1. \(q-1=2^8\cdot13\), \(\zeta^{128}=-1\), and
   \(\zeta^{256}=1\). Thus \(\zeta\) has exact order \(256\).
   There is no element of order \(512\), because \(512\nmid q-1\).
2. BitRev7 permutes \(0,\ldots,127\), and every one of the 128
   Appendix A constants is exactly \(\zeta^{\operatorname{BitRev}_7(i)}\).
3. With
   \[
   \gamma_i=\zeta^{\,2\operatorname{BitRev}_7(i)+1},
   \]
   the 128 constants \(\gamma_i\) are distinct nonsquares. Hence all
   \(X^2-\gamma_i\) are irreducible and pairwise coprime over
   \(\mathbf F_q\).
4. Direct coefficient multiplication gives
   \[
   X^{256}+1=\prod_{i=0}^{127}(X^2-\gamma_i)\pmod q.
   \]
5. FIPS 203 Algorithm 9 agrees, on all 256 monomial basis vectors, with
   the direct CRT residue map
   \[
   f\longmapsto
   \bigl(f\bmod(X^2-\gamma_i)\bigr)_{i=0}^{127}.
   \]
   Algorithm 10 maps every resulting basis column back to the original
   monomial. Both algorithms are linear, so these 256 column checks
   cover every input in \(\mathbf F_q^{256}\), not merely test vectors.
6. Algorithms 11 and 12 implement multiplication in each quadratic
   component:
   \[
   (a_0+a_1X)(b_0+b_1X)
   =(a_0b_0+\gamma_i a_1b_1)
    +(a_0b_1+a_1b_0)X.
   \]
   Deterministic end-to-end checks compare inverse-NTT/pointwise
   multiplication against direct negacyclic multiplication.
7. The 128 constants in the
   [pq-crystals reference table at commit
   3edd5af](https://github.com/pq-crystals/kyber/blob/3edd5af5991927164edd4aacebfcbee00b8064e7/ref/ntt.c)
   are exactly the FIPS constants multiplied by \(R=2^{16}\bmod q\) and
   written as centered representatives.

A short proof of Item 4 is useful for avoiding a common notation mistake.
The roots of \(Y^{128}+1\) are
\(\zeta^{2k+1}\) for \(0\leq k<128\). Bit reversal only reorders \(k\).
Substituting \(Y=X^2\) gives the displayed quadratic factorization.
Because each \(\gamma_i\) has order 256 while the subgroup of squares has
2-primary order only \(2^7\), no \(\gamma_i\) is a square.

The absence of a 512th root is precisely why this is an **incomplete NTT**:
the ring decomposes into 128 quadratic fields rather than 256 scalar
evaluation components.

## Normative table and NIST errata note

The script embeds the two public 128-entry tables it checks so the run is
reproducible offline:

- FIPS 203 Appendix A in ordinary residues;
- pq-crystals ref/ntt.c in centered Montgomery representation.

NIST's current
[potential-updates spreadsheet](https://csrc.nist.gov/files/pubs/fips/203/final/docs/fips-203-potential-updates.xlsx)
notes that Algorithms 9 and 10 use indices \(1,\ldots,127\), whereas
Appendix A also includes the \(i=0\) value \(1\). The proposed clarification
says the latter is included so array index \(i\) equals
\(\zeta^{\operatorname{BitRev}_7(i)}\). This certificate uses that exact
indexing. The spreadsheet does not alter the factorization or NTT formulas.

## Prior-art boundary

This is intentionally a transparent, executable certificate, **not a new
formal-verification theorem**. Stronger prior work already exists:

- Almeida et al.,
  [*Formally verifying Kyber Episode IV: Implementation
  Correctness*](https://eprint.iacr.org/2023/215), gives machine-checked
  implementation-correctness results for Kyber.
- Trieu,
  [*Formally Verified Number-Theoretic
  Transform*](https://doi.org/10.62056/ahbn-4tw9), specifies complete and
  incomplete NTTs in Rocq and derives verified implementations.

The value here is narrower: one readable standard-library Python file that
ties the exact FIPS 203 formulas, Appendix A values, direct CRT map, and the
public reference Montgomery table together.
