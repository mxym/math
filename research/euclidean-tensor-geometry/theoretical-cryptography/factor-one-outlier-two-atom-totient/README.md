# One-outlier factoring from one numeric totient value

## Status

This research-branch theorem has passed an author-independent paper
audit. It is not an immutable release and makes no priority claim.
The small-root step is classical and is attributed explicitly below.

## Theorem

Fix \(k\ge4\), constants \(0<c<C\), \(\delta>0\), and \(A\ge0\).
Let
\[
 N=q\prod_{i=1}^{k-1}p_i
\]
be squarefree with distinct prime factors. Suppose there is an
unprovided scale \(X\) such that every factor lies in \([cX,CX]\), while
the \(k-1\) factors \(p_i\) satisfy
\[
 W:=\max_i p_i-\min_i p_i
 \le X^{2/(k-1)}(\log N)^A.                               \tag{1}
\]
Put
\[
 g=\left(\prod_{i=1}^{k-1}p_i\right)^{1/(k-1)}
\]
and assume the remaining factor is genuinely separated:
\[
 |q-g|\ge\delta X.                                        \tag{2}
\]

Given only \(N\) and the single numeric value \(T=\varphi(N)\), there is
an unconditional deterministic bit-polynomial algorithm recovering the
complete factorization. The scale, cluster, width, side of the outlier,
and outlier are not input.

There is also a separate \(k=3\) endpoint: if two comparable primes
form a cluster of width
\[
 W\le X^{5/6}(\log N)^A
\]
and the third prime is a distance \(\Omega(X)\) away, the same input
\(N,\varphi(N)\) suffices for deterministic bit-polynomial factoring.

The key new step locates the unknown outlier. With \(m=k-1\), solve the
fixed-degree equation
\[
 (x-1)^m(N-x^m)-Tx^m=0.                                  \tag{3}
\]
It has exactly two relevant real roots. For one of them,
\(y=N/x^m\) satisfies
\[
 |y-q|=O_{k,c,C,\delta}(W^2/X).                           \tag{4}
\]
Under (1), the exponent in (4) is strictly below the classical
unknown-divisor small-root radius \(X^{2/k}\). A CRT construction and
the Coppersmith--Howgrave-Graham--May theorem recover \(q\). The
remaining \(k-1\) factors form an ordinary short cluster at their
classical threshold.

## A large promised family

For \(k=3\), the endpoint above gives
\[
 \Omega(Y^{17/18}/\log^3Y)
\]
promised inputs in every sufficiently large shell.

For every fixed \(k\ge4\), ordinary prime-number-theorem binning gives
\[
 \Omega_k\!\left(
 \frac{Y^{(4-2/(k-1))/k}}{(\log Y)^k}
 \right)                                                  \tag{5}
\]
distinct promised inputs in every sufficiently large fixed
multiplicative shell \([Y,2Y]\). For \(k=4\), this is
\[
 \Omega(Y^{5/6}/\log^4Y),
\]
and for \(k=5\) it is \(\Omega(Y^{7/10}/\log^5Y)\).

The shell construction uses two macroscopically separated fixed
subintervals, so it is outside every all-factors-in-one-short-window
promise. It needs no short-interval prime theorem. The factors can be
chosen with ratio below two, so \(\gcd(N,\varphi(N))=1\) on this family.

This is a fixed-\(k\), squarefree, promised-family theorem. It is not a
general deterministic factoring algorithm, does not use a factored
totient, and does not imply insecurity of a concrete scheme.

## Reproduction

~~~sh
./replay.sh
sha256sum -c SHA256SUMS
~~~
