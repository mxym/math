# Squarefree abundant integers at critical roughness

There are unconditionally infinitely many odd squarefree abundant numbers whose least prime factor exceeds the square root of their natural logarithm. In fact, for every fixed A>0 one can require a consecutive prime product starting at p with logarithm at most p^2-A p^(3/2).

The existence endpoint was left open in Shunia, arXiv:2611.34242v1, §5.2, p. 15. Eriksson's related Theorem 3(b) assumes a strict gap between the supremum of zeta-zero real parts and 1. The proof here does not impose that gap; it uses ordinary PNT, Mertens' asymptotic, and Diamond–Pintz's unconditional oscillation, with a maximum argument in a continuous prime-cost interpolation.

This does not extend the abundance-oracle reduction to c=1 or give a bound on finding large witnesses. See PROOF.md and UPSTREAM.md. The small fixed-data sanity check is not evidence for the asymptotic theorem:

```sh
sha256sum -c SHA256SUMS
python3 -B verify_finite.py
```
