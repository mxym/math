# Sources and scope

1. **David Harvey and Markus Hittmeir**,
   *A log-log speedup for exponent one-fifth deterministic integer
   factorisation*, Mathematics of Computation 91 (2022), 1367--1379.
   DOI: https://doi.org/10.1090/mcom/3708
   Preprint: https://arxiv.org/abs/2105.11105

   Their theorem rigorously and deterministically factors a positive
   integer \(Y\) in
   \[
   O\!\left(
   Y^{1/5}\log^{16/5}Y/(\log\log Y)^{3/5}
   \right)
   \]
   bit operations. This is the only general-factorization bound used in
   the composition.

2. **Factored-advice predecessor**, repository commit
   46afa65c4e8fd9999822dcdd8bfd492522cff0b7,
   directory factor-factored-exponent-max-prime.

   Given the complete factorization of \(E\) with
   \(\lambda(N)\mid E\), it proves complete deterministic factorization
   of \(N\) in
   \[
   P_E(N)^{1/(4\sqrt e)+\varepsilon}
   \operatorname{poly}(\log N+\log E).
   \]
   The present note removes the factored-advice assumption by paying the
   established one-fifth cost to factor \(E\) itself.

3. **François Morain, Guénaël Renault, and Benjamin Smith**,
   *Deterministic factoring with oracles*, arXiv:1802.08444,
   version dated 22 March 2026:
   https://arxiv.org/abs/1802.08444

   Section 5.7 discusses using complete factorizations of
   \(\varphi(N)\) or \(\lambda(N)\) and the obstacle posed by large
   divisor counts. The conclusion emphasizes that complete
   factorizations of oracle values did not yield a known deterministic
   polynomial-time algorithm for all inputs. The present theorem is
   consistent with that statement: its bound is still a positive
   value exponent.

This package uses the peer-reviewed Harvey--Hittmeir theorem and the
pinned repository predecessor. It does not rely on recent unreviewed
claims of subexponential deterministic factorization. It does not
construct \(E\), does not imply ordinary deterministic
\(N^{o(1)}\)-time factoring, and makes no absolute priority claim.
