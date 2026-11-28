# Prior art and exact scope

The proof in this directory is correct, but its enumeration is an
immediate specialization of established algorithms.

## Carmichael-side predecessor classification

**Peter J. Cameron and D. A. Preece**,
*Notes on primitive lambda-roots*, draft dated 17 July 2009,
https://maths.qmul.ac.uk/~pjc/csgnotes/lambda.pdf

Section 5, especially Theorem 5.2 and the explicit algorithm following
it on printed p. 9, describes the maximal integer \(\lambda^*(E)\)
associated with \(\lambda(n)\mid E\). It lists every admissible odd
prime through \(p-1\mid E\) and gives its maximum allowed exponent.
Thus the predecessor scan and the handling of arbitrary multiplicities
are already present on the Carmichael side.

## Explicit divisor enumeration

**Max A. Alekseyev**,
*Computing the Inverses, their Power Sums, and Extrema for Euler's
Totient and Other Multiplicative Functions*,
Journal of Integer Sequences 19 (2016), Article 16.5.2,
https://cs.uwaterloo.ca/journals/JIS/VOL19/Alekseyev/alek5.pdf

Section 4 Step 1 and Section 5.1 (printed pp. 5--6), together with
Theorem 4, explicitly enumerate the divisors \(d\mid E\), test
\(d+1\) for primality, and bound the work in terms of \(\tau(E)\).
This is the same candidate-generation mechanism used here.

A still earlier inverse-totient predecessor search appears in:

**Scott Contini, Ernie Croot, and Igor E. Shparlinski**,
*Complexity of Inverting the Euler Function*,
Mathematics of Computation 75 (2006), 983--996,
DOI: https://doi.org/10.1090/S0025-5718-06-01826-6,
arXiv: https://arxiv.org/abs/math/0404116 .

## Parameter substitution

For support advice \(\mathcal S\), set
\[
 E=\prod_{r\in\mathcal S,\ r\le N}r^{\lfloor\log_rN\rfloor}.
\]
Then \(\lambda(N)\mid E\), its factorization is explicit, and
\[
 \tau(E)=
 \prod_{r\in\mathcal S,\ r\le N}
 (1+\lfloor\log_rN\rfloor)=C(N,\mathcal S).
\]
Testing the established candidate list against the supplied \(N\)
removes false candidates and recovers exact multiplicities. Therefore
the displayed fixed-support complexity is a useful parameterized
corollary of these methods, not a novelty claim.

The advice may contain false-positive primes but may not omit any prime
from \(\operatorname{supp}\lambda(N)\). No ordinary unadvised factoring
claim is made.
