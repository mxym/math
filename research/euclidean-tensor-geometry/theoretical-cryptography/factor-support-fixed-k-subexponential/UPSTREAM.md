# Sources, comparison, and corrected scope

## Dominating earlier machinery

1. **Bartosz Zralek**, *A deterministic version of Pollard's p-1
   algorithm*, Mathematics of Computation 79 (2010), 513--533,
   DOI https://doi.org/10.1090/S0025-5718-09-02262-5,
   arXiv:0707.4102v5.

   Lemma 8.4 lower-bounds the common order \(A\) when the number of
   prime factors is small; Lemma 8.5 reconstructs all factors by
   factoring the base-\(A\) digit polynomial.

2. **Markus Hittmeir and Jacek Pomykala**,
   *Deterministic Integer Factorization with Oracles for Euler's
   Totient Function*, Fundamenta Informaticae 172 (2020), 39--51,
   DOI https://doi.org/10.3233/FI-2020-1891.

   This work explicitly gives deterministic polynomial-time
   factorization for bounded \(\omega(N)\) when the prime-power
   decomposition of \(\varphi(N)\) is available.

The present support input constructs a fully factored multiple
\[
 E=\prod_{r\in\mathcal S,r\le N}
 r^{\lfloor\log_rN\rfloor}
\]
with \(\varphi(N)\mid E\). Exact orders of every scanned base are
computed by stripping prime powers from \(E\) with modular-power
tests. Repeated prime powers of \(N\) are removed first because their
underlying prime belongs to the support.

For fixed \(K\), take bases through
\(y=(\log d)^{K+2}\) in each squarefree recursive block \(d\).
If a gcd or Fermat--Euclid witness appears, split. Otherwise all local
orders agree and
\(A=\operatorname{lcm}_{b\le y}\operatorname{ord}_d(b)\) divides
every \(p-1\). With \(k=\omega(d)\le K\),
\[
 A^k\ge\Psi(d,y)>d^{1-1/(K+2)}.
\]
Hence
\[
 A^{k+1}>
 d^{(1-1/(K+2))(k+1)/k}>
 \binom{k}{\lfloor k/2\rfloor}d
\]
for all sufficiently large \(d\), with finite exceptions handled
directly. Zralek Lemma 8.5 then recovers the factors in polynomial time.
This dominates the local ratio-enumeration bound.

The earlier version of this file missed this consequence. The local
proof remains valid but no novelty or best-bound claim remains.
