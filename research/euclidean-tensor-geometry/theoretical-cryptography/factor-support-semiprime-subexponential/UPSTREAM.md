# Sources, correction, and exact comparison

## Prior-art correction

The original search missed a directly stronger consequence of the
following source:

**Jacek Pomykała and Maciej Radziejewski**,
*Integer factoring and compositeness witnesses*,
Journal of Mathematical Cryptology 14(1) (2020), 346--358,
DOI: https://doi.org/10.1515/jmc-2019-0023

Author PDF:
https://nutmic2019.imj-prg.fr/confpapers/FactoringWitnesses.pdf

Section 6 (printed pp. 15--16) defines **Dec Mul Φ**: the input contains
the complete prime factorization of a polynomial-size multiple D of
φ(N). After Theorem 6.1 the paper explicitly states that every semiprime
N=pq is solvable by Algorithm A3 under this input. Complete support
advice for λ(N) supplies such a D, namely
\[
 D=E_{\mathcal S}(N)
 =\prod_{r\in\mathcal S,\ r\le N}r^{\lfloor\log_rN\rfloor}.
\]
Indeed supp φ(N)=supp λ(N) and, for every r,
v_r(φ(N))≤floor(log_r N). Hence φ(N) divides D, the factorization of D
is explicit, and log D≤|S| log N.

A second relevant source is:

**Bartosz Źrałek**,
*A deterministic version of Pollard's p-1 algorithm*,
Mathematics of Computation 79 (2010), 513--533,
arXiv: https://arxiv.org/abs/0707.4102 ,
DOI: https://doi.org/10.1090/S0025-5718-09-02262-5

In arXiv v5, Theorem 8.1 and Lemmas 8.3--8.5 (printed pp. 18--20) give
a deterministic L_N[1/3,1+o(1)] route from a completely factored φ(N).
The proof uses the factorization to compute orders by prime-factor
stripping, so the same factored multiple D is sufficient. Repeated prime
powers can be removed first: if p^a divides N with a≥2, then p divides
λ(N), hence p appears in the support advice.

These adaptations dominate the historical subexponential theorem in
this directory; they are corollaries of the cited proofs, not literal
restatements of the published theorem inputs.

## Sources used by the retained proof

1. The Konyagin--Pomerance smooth-number lower bound, in the form used
   as Lemma 4.2 of Pomykała--Radziejewski:
   \[
     \Psi(x,y)>x^{1-\log\log x/\log y}.
   \]

2. **François Morain, Guénaël Renault, and Benjamin Smith**,
   *Deterministic factoring with oracles*, arXiv:1802.08444,
   https://arxiv.org/abs/1802.08444 .
   Lemma 5.3 gives
   φ(N)=λ(N) gcd(N-1,λ(N)) for distinct-prime semiprimes when the exact
   Carmichael value is known.

3. Repository dependencies originally used:
   factor-carmichael-support-advice/ and
   factor-factored-exponent-smooth-kernel/.

The original sqrt(2)-constant argument remains a correct but weaker
route. No novelty or priority claim remains attached to it.
