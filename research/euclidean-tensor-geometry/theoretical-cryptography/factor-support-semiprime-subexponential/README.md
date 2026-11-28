# Support-advised semiprime factoring in deterministic subexponential time

## Status

Research-branch theorem. The proof has passed its deterministic finite
checker and a full self-review. It is not an immutable release and has
not yet received an author-independent proof audit.

## Theorem

Let \(N=pq\) be the product of two distinct primes. The auxiliary input
is a finite list \(\mathcal S\) of distinct primes containing every
prime divisor of \(\lambda(N)\); false positives are allowed. The value
of \(\lambda(N)\) and all of its prime exponents are *not* supplied.

There is an unconditional deterministic algorithm recovering \(p,q\)
in
\[
 \exp\!\left((\sqrt2+o(1))
       \sqrt{\log N\,\log\log N}\right)
 \operatorname{poly}\!\left(
   \log N+|\mathcal S|+\sum_{r\in\mathcal S}\log r\right) \tag{1}
\]
bit operations.

This improves the general deterministic power-time bound for this
advice model to a true subexponential bound. It combines two exits:

1. a smooth-number subgroup escape, detected through the synthesized
   Carmichael multiradix chains; and
2. an exhaustive reconstruction of the small coprime coefficients in
   \(p-1=Ag,\ q-1=Bg\).

The balance between the two exits gives the constant \(\sqrt2\).

## Exact scope

The semiprime promise is essential to the coefficient-reconstruction
step. This is not a general-input factoring theorem. The support list is
advice and the theorem does not compute it from \(N\) or from an
unfactored Carmichael value. If the exact value \(\lambda(N)\) is known,
Morain--Renault--Smith already give a polynomial-time semiprime
factorization via
\(\varphi(N)=\lambda(N)\gcd(N-1,\lambda(N))\); the result here concerns
the strictly weaker support-only input.

No concrete modulus, key, implementation, or security conclusion is
involved.

## Reproduction

\`\`\`sh
./replay.sh
\`\`\`
