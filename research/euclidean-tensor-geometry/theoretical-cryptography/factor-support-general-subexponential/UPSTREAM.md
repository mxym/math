# Sources, prior art, and search scope

1. **Pollard--Strassen small-divisor detection.**

   **Edgar Costa and David Harvey**, *Faster deterministic integer
   factorization*, Mathematics of Computation 83 (2014), 339--345,
   DOI: https://doi.org/10.1090/S0025-5718-2013-02707-X
   and author version https://arxiv.org/abs/1201.2116

   Their product-tree / multipoint framework refines Strassen's
   deterministic method. The parameterized consequence used here is
   the standard one: a divisor in an interval of length \(D\) can be
   detected in \(D^{1/2+o(1)}\) bit operations. Repeating the small-factor
   routine only polynomially many times removes every prime at most the
   selected cutoff.

2. **Jacek Pomykała and Maciej Radziejewski**,
   *Integer factoring and compositeness witnesses*:
   https://nutmic2019.imj-prg.fr/confpapers/FactoringWitnesses.pdf

   Lemma 4.2 records the Konyagin--Pomerance lower bound
   \[
     \Psi(x,y)>x^{1-\log\log x/\log y}.
   \]
   Their Algorithm 2 is the closest consulted small-order /
   power-difference witness framework.

3. **François Morain, Guénaël Renault, and Benjamin Smith**,
   *Deterministic factoring with oracles*, arXiv:1802.08444:
   https://arxiv.org/abs/1802.08444

   This is the principal comparison for exact \(\Phi\), \(\Lambda\),
   order, and sum-of-divisors oracle models. The current input is not an
   exact Carmichael value: it is the completely exposed prime support,
   which is strong structured advice and need not be obtainable by
   factoring the exact value in polynomial time.

4. Repository predecessors, pinned:

   * factor-carmichael-support-advice/, commit
     4e0f3489260d13e8b3607d63fe8f29e3d3f94cdc;
   * factor-support-fixed-k-subexponential/, commit
     d17b125afd883cf597c96ae0b45bfc7bc3d56d4a.

   The first synthesizes a factored exponent multiple from support
   advice. The second gives the
   \(\sqrt{2(K-1)}\) bound for at most \(K\) prime factors. The new step
   is to use fast small-factor removal to force
   \(K<\log N/\log Z\), then optimize \(Z\) jointly with the two
   fixed-\(K\) exits.

5. Unadvised deterministic baseline:

   **David Harvey and Markus Hittmeir**,
   *A log-log speedup for exponent one-fifth deterministic integer
   factorisation*, Mathematics of Computation 91 (2022), 1367--1379,
   DOI: https://doi.org/10.1090/mcom/3708

   This is a general-input power-time theorem and does not assume the
   advice (1). The present \(L_N[2/3,1]\) bound is not comparable as an
   unadvised result.

Targeted searches did not locate this exact support-advised
three-way balance of small-divisor removal, subgroup escape, and
shifted-ratio reconstruction. No absolute priority claim is made. The
theorem does not obtain or certify the completeness of its support
advice and makes no statement about a concrete system.
