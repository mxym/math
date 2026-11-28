# One high-power divisor sum factors squarefree integers with at most three prime factors

## Scope

Let (nge 2) be promised squarefree with (omega(n)le 3), let
[
M=lceillog_2 nceil,qquad Jge 16M,
]
and suppose the single integer
[
S=sigma(n^J)
]
is given. This note gives a deterministic algorithm, polynomial in (log n) and in the bit length of (S), that returns the complete prime factorization of (n).

This is a promised-family result. It is **not** a polynomial-time algorithm for factoring unrestricted integers, and it does not claim that one divisor-sum value is necessary.

## Theorem

For squarefree (n) with at most three distinct prime factors, (n) and one high-power divisor sum (sigma(n^J)), with (Jge16lceillog_2nceil), determine the complete factorization of (n) in deterministic polynomial time.

Consequently, composing with Shunia's deterministic abundance-to-comparison reduction, this promised family can be factored with (O((log n)^2)) adaptive abundance queries, each on an integer of (O((log n)^4)) bits.

## Proof

### 1. Recover the totient from the same value

Shunia's Lemma 3.2 proves, for every (Jge16lceillog_2nceil),
[
arphi(n)=leftlfloorrac{n^{J+1}}{sigma(n^J)}ightfloor.
]
Thus (S) supplies both the exact divisor sum at the high power and the exact integer (arphi(n)).

Primality testing handles (omega(n)=1). If (n=pq) is squarefree, then (p+q=n+1-arphi(n)), so the two primes are the roots of a quadratic. It remains to treat (n=pqr) with distinct primes.

### 2. Eliminate the three primes to one integer parameter

Put
[
s=p+q+r,qquad C=n-arphi(n)-1.
]
Since
[
arphi(n)=(p-1)(q-1)(r-1)=n-(pq+pr+qr)+s-1,
]
we have (pq+pr+qr=s+C). Therefore (p,q,r) are the roots of
[
P_T(X)=X^3-TX^2+(T+C)X-n
]
at the true parameter (T=s).

Let (g_J(X)=1+X+cdots+X^J). Because (n) is squarefree,
[
S=sigma(n^J)=prod_{uin{p,q,r}}g_J(u)
=operatorname{Res}_X(P_s(X),g_J(X)).
]
Hence (s) is an integer root of
[
R(T)=operatorname{Res}_X(P_T(X),g_J(X))-Sinmathbb Z[T].
]

This polynomial is not identically zero. If (zeta) runs through the (J) distinct roots of (g_J), then
[
P_T(zeta)=zeta^3+Czeta-n+Tzeta(1-zeta).
]
Using
[
operatorname{Res}(P_T,g_J)=(-1)^{3J}prod_{g_J(zeta)=0}P_T(zeta),
]
the coefficient of (T^J) is
[
(-1)^{3J}prod_zetazeta(1-zeta)
=(-1)^{3J}(-1)^Jg_J(1)=J+1.
]
Thus (R) has exact degree (J).

Factor (R(T)) over (mathbb Q) deterministically. For every integer root (t), factor the cubic (P_t(X)), and retain a candidate only when its three roots are distinct positive primes and reproduce (n), (arphi(n)), and (S). The promised input has the valid root (t=s).

### 3. Bit complexity

The Sylvester matrix for (P_T) and (g_J) has size (J+3). Standard exact resultant algorithms construct (R) in polynomial time. Equivalently, evaluate the integer resultant at (T=0,ldots,J) and interpolate exactly.

Writing (P_T(zeta)=A_zeta+T B_zeta) gives
[
|operatorname{Res}_X(P_T,g_J)|_1le (n+|C|+3)^J.
]
Also (Sle n^{2J}). Hence every coefficient has (O(Jlog n)) bits. Here (J=O(log n)), so exact interpolation, deterministic rational polynomial factorization, cubic factorization, and deterministic primality testing all have polynomial bit complexity.

For the abundance-oracle corollary, set (x=n^J). Then (log x=O((log n)^2)). Binary search recovers the exact (S=sigma(x)) using (O(log x)=O((log n)^2)) comparisons. Shunia's comparison theorem implements each comparison by at most one abundance query of (O((log x)^2)=O((log n)^4)) bits.

## Prior work and precise increment

* Bach, Miller, and Shallit (1986) gave randomized polynomial-time factorization from (n) and the ordinary value (sigma(n)).
* Morain, Renault, and Smith studied deterministic factoring with (arphi)- and (sigma)-type oracles. The symmetric-polynomial reconstruction from separately supplied (arphi(n)) and (sigma(n)) for a squarefree product of three primes is a direct predecessor.
* Hillar and Levine studied reconstruction from cyclic resultants.
* Shunia (2026) observed the cyclic-resultant form of (sigma(n^j)) and proved deterministic general factoring from many consecutive high-power divisor sums.
* Eriksson (2026) sharpened Shunia's normalization exponent and gave a generic (2k)-sum guarantee when (omega(n)le k).

The increment here is narrow: in the squarefree three-prime case, **the same single high-power sum first yields (arphi(n)) by flooring and then supplies the one additional resultant equation**, so no second oracle value or consecutive list is needed. The resultant itself and the separate two-value reconstruction are prior techniques.

## Reproduction

```bash
python3 verify_resultant.py
```

Expected output is recorded in `RESULTS.txt`.

## References

1. Joseph M. Shunia, *Deterministic integer factorization from abundance decisions*, arXiv:2611.34242v1, 2026. https://arxiv.org/abs/2611.34242
2. François Morain, Guénaël Renault, Benjamin Smith, *Deterministic factoring with oracles*, AAECC 34 (2023), 663–690. https://doi.org/10.1007/s00200-021-00521-8
3. Eric Bach, Gary L. Miller, Jeffrey Shallit, *Sums of divisors, perfect numbers and factoring*, SIAM J. Comput. 15 (1986), 1143–1154. https://doi.org/10.1137/0215083
4. Christopher J. Hillar, Lionel Levine, *Polynomial recurrences and cyclic resultants*, Proc. AMS 135 (2007), 1607–1618. https://doi.org/10.1090/S0002-9939-07-08658-5
5. Lluis Eriksson, *Sharp Normalization Exponents, a 19x Rescaled-Vandermonde Contraction, Linear-Exponent Bounded-omega(n) Factoring, and Resolution of the c=1 Endpoint for Abundance-Oracle Factorization*, AIRR ARR-2026-1ZVBB45HG78WNVDH v1, 2026. https://airr.science/papers/ARR-2026-1ZVBB45HG78WNVDH/
