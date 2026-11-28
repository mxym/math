# Two-point coefficient recovery for clustered fixed-\(\omega\) factoring

## Status

This research-branch theorem has passed an author-independent paper
audit. It is not an immutable release and makes no priority claim.
The uniform polynomial-time threshold below is also a consequence of a
classical CRT plus Coppersmith--Howgrave-Graham small-root theorem; the
package records a different elementary coefficient-recovery proof, not
a first solvable range.

## Theorem

Fix \(k\ge4\). Let
\[
N=\prod_{i=1}^k p_i,\qquad 2\le p_1<\cdots<p_k
\]
be a product of exactly \(k\) distinct primes, and suppose only the
numeric value \(T=\varphi(N)\) is supplied. Put
\[
u=N^{1/k},\qquad H=p_k-p_1.
\]
There is an unconditional deterministic algorithm, not given \(H\),
whose running time for \(H\le u\) is
\[
 \operatorname{poly}_k(\log N)
 \prod_{j=1}^{k-2}
 \left(1+O_k\!\left({H^{j+2}\over u^2}\right)\right). \tag{1}
\]
Consequently, for every fixed \(A\ge0\), the factors are recovered in
deterministic bit-polynomial time under the promise
\[
 H\le N^{2/k^2}(\log N)^A. \tag{2}
\]

No factorization of \(T\) is used. The method evaluates one shifted
degree-\(k\) polynomial at the two consecutive integer points
\(\lfloor u\rfloor\) and \(\lfloor u\rfloor-1\), then recovers its
coefficients by a finite-difference tree. The last two coefficients are
solved exactly from the two known values.

The same proof also applies to \(k=3\), but the sibling triprime
result cited below is strictly stronger there. For \(k=4\), (1)
specializes to
\[
 \operatorname{poly}(\log N)
 \left(1+{H^3\over N^{1/2}}\right)
 \left(1+{H^4\over N^{1/2}}\right),
\]
up to absolute fixed-\(k\) constants. Thus
\(H\le N^{1/8}\operatorname{polylog}N\) is sufficient.

## The promise is nonempty at scale

For every fixed \(k\ge4\), prime-number-theorem binning gives
\[
 \Omega_k\!\left({Y^{\,3/k-2/k^2}\over(\log Y)^k}\right)
\]
distinct promised inputs in a fixed multiplicative shell
\([Y,2Y]\) for all sufficiently large shells. For \(k=4\), this is
\(\Omega(Y^{5/8}/\log^4Y)\). These inputs also have
\(\gcd(N,\varphi(N))=1\), so they are not the elementary gcd branch.

This is a sparse cluster promise, not arbitrary equal-bitlength
multi-prime factoring and not general factoring from \(\varphi(N)\).

## Reproduction

```sh
./replay.sh
sha256sum -c SHA256SUMS
```
