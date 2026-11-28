# Sources and scope

1. **Sergei Konyagin and Carl Pomerance**,
   *On primes recognizable in deterministic polynomial time*, in
   *The Mathematics of Paul Erdős*, Springer, 1997, 176--198.

   Their smooth-number lower bound is quoted as Lemma 4.2 in the next
   source:
   \[
   \Psi(x,y)>x^{1-\log\log x/\log y}
   \qquad(x\ge4,\ 2\le y\le x).
   \]

2. **Jacek Pomykała and Maciej Radziejewski**,
   *Integer factoring and compositeness witnesses*, conference
   manuscript:
   https://nutmic2019.imj-prg.fr/confpapers/FactoringWitnesses.pdf

   Algorithm 2 develops prime-adic order and power-difference witnesses.
   Lemma 4.2 states the Konyagin--Pomerance bound, and the proof of
   Lemma 4.4 uses the standard principle that many smooth integers force
   a large generated subgroup. The present theorem applies that
   principle to the exact pair kernel of size
   \(\gcd(p-1,q-1)\), records an output-sensitive criterion for every
   residual pair, and derives the fixed-\(\delta\) all-pairs polynomial
   class.

3. **GCD-kernel predecessor**, repository commit
   7f8ac6b7d76fc4634781025a59c021a1d6f360ed,
   directory factor-factored-exponent-gcd-kernel.

   Its elementary count scans through
   \(\gcd(p-1,q-1)+1\). The present result replaces the consecutive
   count by a smooth-product count: if all small prime bases lay in the
   kernel, every small-prime-smooth product would also lie there.

4. **Gary Miller**, *Riemann's hypothesis and tests for primality*,
   Journal of Computer and System Sciences 13 (1976), 300--317.

   Repeated-power gcd splitting from a supplied exponent is standard.

The input includes a completely factored multiple \(E\) of
\(\lambda(N)\). This is not the same as unrestricted factoring and does
not construct the advice. The broad smooth-subgroup method is known;
no absolute priority claim is made for the exact pair-profile
formulation or its fixed-\(\delta\) corollary.
