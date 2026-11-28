# Multiscale Rolle recovery from one numeric totient value

## Status

This research-branch theorem has passed a separate author-independent
paper audit. It is not an immutable release and makes no priority claim.

## Theorem

Fix \(k\ge4\). Let
\[
 N=\prod_{i=1}^k p_i,\qquad 2\le p_1<\cdots<p_k,
 \qquad u=N^{1/k},\qquad H=p_k-p_1\le u,
\]
and suppose only the numeric value \(T=\varphi(N)\) is supplied.

For \(2\le m\le k-1\) and a consecutive \(m\)-block
\[
 I=[p_a,p_{a+m-1}],\qquad L(I)=p_{a+m-1}-p_a,
\]
put
\[
 E(I)=
 \prod_{r<a}(p_{a+m-1}-p_r)
 \prod_{r>a+m-1}(p_r-p_a)
\]
and
\[
 W_m=\min_{I}\frac{L(I)^2E(I)}{u^2}.
\]
There is an unconditional deterministic algorithm, given neither the
blocks nor any \(W_m\), that recovers all factors in
\[
 \operatorname{poly}_k(\log N)
 \prod_{m=2}^{k-1}\bigl(1+O_k(W_m)\bigr).                 \tag{1}
\]

The proof turns \(N\) and \(T\) into the two exact values
\(P(0)\) and \(P(1)\) of the unknown factor polynomial
\(P(X)=\prod_i(X-p_i)\). At each coefficient level, repeated Rolle
differentiation of \(P(X)/(X(X-1))\) supplies finitely many algebraic
centers. A short consecutive root block makes the true coefficient close
to one center. The algorithm enumerates all centers with a universal
geometric budget, so none of the geometric quantities in (1) is input.

The uniform-cluster result follows from \(E(I)\le H^{k-m}\):
\[
 \operatorname{poly}_k(\log N)
 \prod_{m=2}^{k-1}
 \left(1+O_k\!\left(\frac{H^{k-m+2}}{u^2}\right)\right).
\]
The new point is that different levels may use different local blocks,
while other factors may be macroscopically separated.

## A large nonuniform promised family

For every fixed \(k\ge4\), prime-number-theorem binning constructs
\[
 \Omega_k\!\left(
 \frac{Y^{(3-2^{-(k-2)})/k}}{(\log Y)^k}
 \right)                                                   \tag{2}
\]
distinct squarefree inputs in \([Y,2Y]\) for which every \(W_m=O_k(1)\).
These inputs have \(H\asymp u\), so they lie outside the earlier
all-factors-in-one-short-window promise. For \(k=4\), (2) is
\(\Omega(Y^{11/16}/\log^4Y)\).

The construction uses only the ordinary prime number theorem in fixed
positive-length intervals, not a short-interval prime theorem. It also
has \(\gcd(N,\varphi(N))=1\), so it is not the elementary gcd branch.

This is a fixed-\(k\), squarefree, one-oracle-value theorem. It is not a
general deterministic factoring algorithm and does not use or compute a
factorization of \(\varphi(N)\).

## Reproduction

~~~sh
./replay.sh
sha256sum -c SHA256SUMS
~~~
