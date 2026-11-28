# Prior-art classification

Independent audit found the theorem in this directory correct but not
independently new.

1. Cameron--Preece, *Notes on primitive lambda-roots*, Section 5,
   Theorem 5.2 and the algorithm on printed p. 9, already classify the
   prime powers that may occur in an integer \(n\) satisfying
   \(\lambda(n)\mid E\). The condition \(p-1\mid E\) supplies all odd
   prime candidates and their formula supplies the allowed
   multiplicities.

2. Alekseyev, JIS 19 (2016), Section 4 Step 1 and Section 5.1, explicitly
   obtains the candidate primes by enumerating \(d\mid E\) and testing
   \(d+1\). Its work is measured through the divisor count \(\tau(E)\).

3. Under the present support advice,
   \[
     E=\prod_{r\in\mathcal S,\ r\le N}
       r^{\lfloor\log_rN\rfloor}
   \]
   is completely factored, contains \(\lambda(N)\) as a divisor, and
   has
   \[
     \tau(E)=
     \prod_{r\in\mathcal S,\ r\le N}
       (1+\lfloor\log_rN\rfloor)=C(N,\mathcal S).
   \]
   Divisibility into \(N\) filters the general candidate list and exact
   division recovers each multiplicity.

Hence the fixed-\(|\mathcal S|\) polynomial bound is a direct
support-advice complexity corollary of a mature predecessor-enumeration
method. The original proof and checker are retained for a self-contained
verification of that corollary. This package should not receive a
standalone novelty claim, release, or DOI.
