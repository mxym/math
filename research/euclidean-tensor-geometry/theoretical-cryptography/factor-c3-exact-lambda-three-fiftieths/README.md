# Exact-lambda factoring of all C3 Carmichael radicals in exponent 3/50

## Result

Let (R=pqr) be a Carmichael number with exactly three distinct prime
factors.  Given (R) and the **single exact value** (lambda(R)), there is
an unconditional deterministic complete-factorization algorithm using

[
  R^{3/50}(log(2R))^{O(1)}
]

bit operations.

If (N=2^eprod_{pmid R}p^{k_p}) has arbitrary unknown multiplicities and
the odd radical (R) satisfies the same promise, then (N) and the one exact
value (lambda(N)) suffice for complete factorization in
(R^{3/50}(log(2N))^{O(1)}) bit operations.

This is a promised-class result with arithmetic advice.  It is **not** a
bit-polynomial algorithm for all C3 Carmichael numbers, not a general
factoring algorithm, and not a result for an arbitrary multiple of
(lambda(N)).  Gupta--Sikarov--Volkovich already give polynomial time for
the *simple* C3 subclass.  The new scope is the full C3 class; the exponent
improves the companion all-C3 bound (1/13).

## New ingredient

Write
[
 p=1+ga,quad q=1+gb,quad r=1+gc,quad L=abc,
]
where (a<b<c) are pairwise coprime, and put (A=ab).  Exact lambda
recovers (g,L), and
[
 Amid L,qquad rmid R,qquad gcd(A,r)=1,qquad A+gL=Ar.
]
For a dyadic bucket (Wle A<2W), a one-variable LLL lattice simultaneously
uses the two divisibilities (Amid L) and (rmid R).  Its determinant
condition is
[
 	au<mu^2+rac{	au^2}{ell},qquad
 	au=log_R W,quad ell=log_R L,quad
 mu=log_Rrac{gL}{2W}.
]
A uniform parameter split has exact worst idealized margin
[
 rac{50339}{23397500}>0.002
]
and leaves either a short progression interval or a short cubic-coefficient
list.  Each remaining list has size (O(R^{3/25})) or (O(R^{3/50}));
fast product-tree batching makes the progression cost its square root.

The full proof, integer-arithmetic implementation details, and scope
comparison are in [PROOF.md](PROOF.md) and [UPSTREAM.md](UPSTREAM.md).
Run:

```bash
python3 verify.py
```

The checker tests the exact identities, the two-modulus divisibility,
the rational parameter margin, all C3 examples with prime factors below
400, and the arbitrary-multiplicity reduction.  It is a finite companion,
not a substitute for the asymptotic LLL proof.
