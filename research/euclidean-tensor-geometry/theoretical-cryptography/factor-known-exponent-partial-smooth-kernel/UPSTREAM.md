# Sources and scope

1. **Sergei Konyagin and Carl Pomerance**,
   *On primes recognizable in deterministic polynomial time*, in
   *The Mathematics of Paul Erdős*, Springer, 1997, 176--198.

   The proof uses their lower bound
   \[
   \Psi(x,y)>x^{1-\log\log x/\log y}.
   \]

2. **Jacek Pomykała and Maciej Radziejewski**,
   *Integer factoring and compositeness witnesses*:
   https://nutmic2019.imj-prg.fr/confpapers/FactoringWitnesses.pdf

   Algorithm 2 uses small-prime local-order and power-difference
   witnesses from a multiple of the group exponent. Lemma 4.2 states the
   Konyagin--Pomerance smooth-number bound, and Lemma 4.4 uses
   smooth-product growth to force large generated subgroups. The present
   theorem records a deterministic all-pairs promise directly in terms
   of the positive part of the **known small-prime valuation
   difference**, and it allows arbitrary prime multiplicities because
   all chain primes are smaller than every residual prime.

3. **Multiradix predecessor**, repository commit
   e26f5a40dbca8113de927a0f2b4ca9cabdc2fe66,
   directory factor-known-exponent-multiradix.

   It gives a general output-sensitive bound using a small-prime cutoff
   but falls back to a two-prime quadratic character on equal partial
   signatures. The present theorem instead identifies a promised class
   where the positive partial index is a fixed power and smooth-kernel
   growth makes every pair separable in polynomial time.

4. **Full smooth-kernel predecessor**, repository commit
   42e70b4c5310678a9c628b82d29238bf9229e40b.

   It assumes the complete factorization of \(E\). The present theorem
   removes that advice by using only primes up to a polynomial-logarithmic
   cutoff.

The input still includes the value of a multiple \(E\) of
\(\lambda(N)\); the theorem does not construct that value. The
small-order and smooth-subgroup ingredients are known, and no absolute
priority claim is made for the exact partial-profile promise.
