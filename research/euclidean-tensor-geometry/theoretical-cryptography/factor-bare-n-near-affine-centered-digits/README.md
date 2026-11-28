# Factoring a connected near-affine prime family by centered digits

Fix the number of prime factors and a nonnegative integer C. The only input is the binary integer N. Suppose N is squarefree, and the graph on its prime factors is connected when an edge is allowed between p<q if q differs from m p by at most p^(1/r) L^C for some integer m in [1,L^C], where r is the fixed number of primes and L is the bit length. Neither the slopes, the offsets, the graph nor the primes are supplied.

There is a deterministic polynomial-bit-time algorithm on this promise. It guesses only the small slopes on a spanning tree, not the potentially large offsets. An integer rescaling gives a product with normalized factors close to a known center. The coefficients of their monic polynomial can then be recovered in polynomially many signed-digit windows from one exact product.

The overlap with classical close-factor results is explicit in UPSTREAM.md. The contribution is the hidden graph normalization and the elementary lattice-free reconstruction, not a general factoring theorem or a new claim for unscaled close primes. The checkers verify finite constructed number-theory examples, not cryptographic instances or runtime in practice.

```
python3 -B verify_normalization.py
python3 -B verify_digits.py
```
