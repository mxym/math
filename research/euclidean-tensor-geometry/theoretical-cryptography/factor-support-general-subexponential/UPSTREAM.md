# Sources, prior art, and corrected search scope

## Dominating prior result

**Bartosz Zralek**, *A deterministic version of Pollard's p-1
algorithm*, Mathematics of Computation 79 (2010), 513--533,
DOI: https://doi.org/10.1090/S0025-5718-09-02262-5,
arXiv: https://arxiv.org/abs/0707.4102

The definitive arXiv v5 numbering is Theorem 8.1 and Lemmas 8.3--8.5,
PDF pp. 18--20. The theorem states a deterministic
\(L_N[1/3,1+o(1)]\) factorization from the complete factorization of
\(\varphi(N)\). Inspection of the proof shows that the factored
totient is used only to compute exact orders of small bases,
Fermat--Euclid witnesses, and their common least common multiple
\(A\). A completely factored multiple \(E\) of \(\lambda(N)\)
supports the same operations: repeatedly remove a prime factor from
\(E\) exactly when the corresponding modular-power test remains one.
The support advice in this directory constructs such an \(E\) in
polynomial advice length. Repeated prime factors of \(N\) are removed
first because their underlying prime belongs to
\(\operatorname{supp}\lambda(N)\).

Thus the present \(L_N[2/3,1]\) proof is mathematically valid but
strictly dominated by a direct support-advice corollary of Zralek's
earlier proof. The earlier version of this file incorrectly reported
that the exact support-advised route had not been located. No novelty or
priority claim remains.

A later exposition of the same common-order mechanism is:

**Jacek Pomykala and Maciej Radziejewski**,
*Integer factoring and compositeness witnesses*,
https://nutmic2019.imj-prg.fr/confpapers/FactoringWitnesses.pdf

See Lemma 4.4 and equations (4.4)--(4.5), pp. 11--12.

## Sources used by the weaker local proof

1. **Edgar Costa and David Harvey**, *Faster deterministic integer
   factorization*, Mathematics of Computation 83 (2014), 339--345,
   DOI: https://doi.org/10.1090/S0025-5718-2013-02707-X,
   arXiv: https://arxiv.org/abs/1201.2116

   The local proof uses the Pollard--Strassen product-tree consequence
   for deterministic small-divisor removal.

2. **Jacek Pomykala and Maciej Radziejewski**, cited above.

   Lemma 4.2 records the Konyagin--Pomerance lower bound used in the
   local smooth-subgroup argument.

3. **Francois Morain, Guenael Renault, and Benjamin Smith**,
   *Deterministic factoring with oracles*, arXiv:1802.08444:
   https://arxiv.org/abs/1802.08444

   This remains the principal comparison for exact totient, Carmichael,
   order, and sum-of-divisors oracle models.

4. Repository predecessors, pinned:

   * `factor-carmichael-support-advice/`, commit
     `4e0f3489260d13e8b3607d63fe8f29e3d3f94cdc`;
   * `factor-support-fixed-k-subexponential/`, commit
     `d17b125afd883cf597c96ae0b45bfc7bc3d56d4a`.

5. Unadvised deterministic baseline:

   **David Harvey and Markus Hittmeir**,
   *A log-log speedup for exponent one-fifth deterministic integer
   factorisation*, Mathematics of Computation 91 (2022), 1367--1379,
   DOI: https://doi.org/10.1090/mcom/3708

The support list is assumed complete and is not obtained or certified by
these arguments. No statement concerns a concrete system.
