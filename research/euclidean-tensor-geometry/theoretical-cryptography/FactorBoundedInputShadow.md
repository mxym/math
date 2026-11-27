# Optimal factor-output probability with bounded input leakage and hidden-ring zero tests

This is an average-case theorem for a **restricted input representation**. It concerns outputting a factor, not just detecting a departure from a simulated transcript. Unlike ordinary integer factorization, the observer cannot read the binary encoding of the semiprime for free. The result neither proves nor suggests hardness of factoring in the standard bit model.

## Experiment

Let S be a known pool of M≥2 distinct primes, each at least P≥2. The hidden unordered pair {p,q} is uniform among the binomial(M,2) distinct pairs; let N=pq. Independently conditional on the pair, sample X_p uniformly in F_p^m and X_q uniformly in F_q^m. Together these represent a hidden uniform ring vector modulo N. Coordinates may be reused arbitrarily by different queries. The observer may use private coins independent of all inputs. It interleaves two sorts of observations:

1. At most b binary responses to arbitrary predicates of N. The choice of predicate can depend on the entire transcript so far, but for a fixed transcript its response is a function of N alone; it cannot additionally read the hidden vector. The bits are unrestricted in computational power. This includes any precomputed b-bit hint about the actual prime factors.
2. Global polynomial zero tests. A test selects an integer polynomial f(X) depending only on the transcript and coins. It returns one bit: whether f is zero *at the hidden vector*, simultaneously modulo p and q. The integer N, if used purely as a ring scalar, vanishes modulo N; a polynomial in formal N and X may accordingly be specialized at its N-variable zero before this definition is applied. Other computational access to the integer N or to encodings of the hidden ring values is **not** permitted except via the binary predicates above.

The observer outputs one ordinary integer g. Success means g is p or q. Let K=2^b, let k=min(K,M), and put
```
A(K)=1−binomial(M−k,2)/binomial(M,2).
```
We use binomial(0,2)=binomial(1,2)=0.

On the *arithmetic shadow*, genuinely zero integer polynomials are answered as zero and all other polynomials are reported as nonvanishing. Binary predicates keep their true responses for N. After fixing the coins, this leaves a binary decision tree with at most K leaves. On each shadow path index the nonzero-integer-polynomial tests i=1,…,t (pad shorter paths with f=1). Assume the i-th such test on any path has total degree at most d_i, 0≤d_i≤P. At most s_i members of S divide its integer coefficient content, meaning that they each divide every coefficient, with 0≤s_i≤M. Bounds on these resources on the shadow paths suffice; behavior after the first arithmetic departure may be arbitrary. If the nonzero coefficients have bit length at most h_i, one can take s_i≤min(M, floor(h_i/log_2 P)): the product of the distinct content primes divides any nonzero coefficient.

## Finite upper bound and sharp leading term

For any such observer,
```
Pr(output is a factor) ≤ A(K) + Δ,
Δ = Σ_i [ d_i²/P²
          + (d_i/P) min(1,2K s_i/M)
          + min(1,K binomial(s_i,2)/binomial(M,2)) ].
```
Conversely A(K) is achievable using the b binary answers alone and no polynomial queries. The finite error bound Δ need not itself be tight. When k=M or M−1 the guessing term already equals one.

In particular for K≤M, dividing by A(K)≥K/M yields
```
Δ/A(K) ≤ Σ_i [ M d_i²/(K P²) + 2d_i s_i/P + s_i(s_i−1)/(M−1) ].
```
For the full pool of n-bit primes, P=2^(n−1) and M is asymptotic to P/log P by the prime number theorem. If t, degree bounds and coefficient bit lengths are polynomial in n, the right hand side tends to zero uniformly for 1≤K≤M. For K≥M−1 the exact optimum is one already. Thus, writing OPT for maximum success over observers in this resource class (the no-test observer is allowed),
```
OPT = (1+o(1)) A(2^b), uniformly in b.
```
In particular this is a *relative* bound when success itself is exponentially small. If 2^b/M→α∈[0,1], the success tends to 2α−α². If 2^b=o(M), the sharper formula is OPT∼2·2^b/M. A bit budget ≤(1−ε)log_2 M for fixed ε>0 therefore has exponentially small success in n. These numerical profiles concern the specified encoded-input problem exclusively.

## Proof

Fix the coins. The tree of arbitrary input bits in the arithmetic shadow has at most K leaves, hence at most K distinct output guesses, irrespective of which hidden pairs map to those leaves. A pair can be guessed correctly only if it intersects that guess set. A set of at most k candidate primes intersects at most binomial(M,2)−binomial(M−k,2) pairs. This proves the A(K) shadow bound. Conversely fix k candidate primes. An unconstrained predicate transcript may encode an index of one of those present when the input pair meets the set (and an arbitrary default index otherwise); at most K messages suffice. This proves optimality absent arithmetic, without claiming these predicates can be computed quickly on plain input.

If real and shadow do not agree, they first disagree at a nonzero integer polynomial that vanishes on both components in the real data. To bound this event one must evaluate the tests **on the shadow path chosen by N**, unconditionally in the hidden vector, rather than condition the samples on prior actual answers. Given the pair, the path does not depend on X_p or X_q, including when the input-bit queries are interleaved with arithmetic queries. If no such shadow-path polynomial vanishes at X, real and shadow histories (including predicate choices and replies) agree by induction.

For a fixed path and i, let T be the set of candidate primes dividing that polynomial's content. There are at most K alternative sets T for query index i, each of size ≤s_i. For the actual pair and the path it selects, there are three cases.

* Neither component prime belongs to T. The polynomial reduced modulo each prime is formally nonzero. Its probability of vanishing at the uniform component vector is ≤d_i/p and ≤d_i/q, respectively, by the polynomial zero bound. Given the pair, the two vectors are independent: the global response differs from shadow with probability at most d_i²/P². This first term is **not** multiplied by K.
* Exactly one prime lies in the selected T. The other component gives conditional probability at most d_i/P. The probability over input pairs that this containment can happen is at most min(1,2K s_i/M), since for any fixed T the expected number of selected primes in T is 2|T|/M and one may union over paths. No independence between the advice and the choice of T is assumed.
* Both primes lie in the selected T. The global test vanishes for all hidden vectors. The number of such input pairs is at most the sum of binomial(|T|,2) over the ≤K path alternatives, giving the final term.

A union bound over i controls the probability of any departure; no independence across adaptive tests is used. Adding the shadow success, averaging over coins, and using A(K)≥K/M (already true for the intersection probability of the first of two ordered draws) proves the claims.

## Scope and prior art

The theorem builds on the distinction between the global and local zero tests in [the earlier CRT observation note](FactorCRTPolynomialObservationBounds.md). Local zero bits from individual prime components are not supplied here. The restricted-model factor-output theorem is stronger than transcript closeness for a fixed, publicly readable N in one respect, and more restrictive in another. It measures actual guessing success for a random pair, but imposes the limited-access-to-input hypothesis needed for that statement. In particular an arbitrary computation that reads N as an ordinary integer for free would invalidate the leaf-count argument. A low-cost arithmetic circuit also need not have small formal degree or small coefficient heights. This is not an attack or a universal accounting of classical factoring algorithms. The no-test guessing bound and finite-field polynomial identity estimates are standard counting ideas; no global priority claim is made.

* [J. T. Schwartz, Fast Probabilistic Algorithms for Verification of Polynomial Identities](https://doi.org/10.1145/322217.322225), for the finite-field polynomial zero estimates.
* [U. Maurer, On the Oracle Complexity of Factoring Integers](https://crypto.ethz.ch/publications/Maurer96.html), studies integer input N available to a polynomial-time algorithm with additional oracle answers. Its small-oracle-budget conclusion is not contradicted here.
* [D. Aggarwal and U. Maurer, Breaking RSA Generically is Equivalent to Factoring](https://crypto.ethz.ch/publications/AggMau09.html), a reduction in a generic ring model including arithmetic and inverse ring operations, not this average-case encoded-input guessing bound.
* [J. B. Rosser and L. Schoenfeld, Approximate formulas for some functions of prime numbers](https://doi.org/10.1215/ijm/1255631807) for classical prime-count context; only the ordinary prime-number-theorem asymptotic is used.

[The toy audit](verify-factor-bounded-input-shadow.js) checks the exact no-test combinatorial profile and enumerates small adaptive experiments, including data-dependent leakage branches and exceptional polynomial content. These checks do not substitute for the asymptotic proof.
