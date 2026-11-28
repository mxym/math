# Factoring clustered squarefree triprimes from Euler's totient

## Status

This is a self-checked research-branch result pending an
author-independent proof audit. It is not an immutable release and makes
no priority claim.

## Theorem

Let
\[
N=xyz,\qquad 2<x<y<z
\]
be distinct primes, and suppose that \(T=\varphi(N)\) is supplied. Put
\[
H=z-x,\quad
R_-=(\sqrt y-\sqrt x)^2{H\over x-1},\quad
R_+=(\sqrt z-\sqrt y)^2{H\over z-1},\quad D=\min(R_-,R_+).
\]
There is an unconditional deterministic algorithm that recovers
\(x,y,z\) in
\[
O\bigl((1+D)\operatorname{poly}(\log N)\bigr)
\]
bit operations. The algorithm does not receive the gaps or \(D\).

Define
\[
F(t)=(t-1)^2\left({N\over t^2}-1\right),\qquad
G(t)=2t+{N\over t^2},\qquad u=N^{1/3}.
\]
The equation \(F(t)=T\) has roots \(s_-\in(1,u)\) and
\(s_+\in(u,\sqrt N)\). The unknown sum \(e_1=x+y+z\) satisfies
\[
G(s_+)\le e_1\le G(s_+)+R_+,\qquad
G(s_-)-R_-\le e_1\le G(s_-).
\]
Scan integers upward from the first endpoint and downward from the
second. Each candidate fixes \(e_2=e_1+N-1-T\) and is checked by
factoring
\[
X^3-e_1X^2+e_2X-N.
\]

## Corollaries

If \(x,y,z\in[u/C,Cu]\) for fixed \(C\), and
\(\ell=\min(y-x,z-y)\), then
\[
D=O_C\!\left({\ell^2(z-x)\over N^{2/3}}\right).
\]
Thus the method is polynomial-time whenever
\(\ell^2(z-x)\le N^{2/3}(\log N)^{O(1)}\). In particular,
\(z-x\le N^{2/9}(\log N)^{O(1)}\) is sufficient. For constant-ratio
triprimes of full spread \(\Theta(N^{1/3})\), an adjacent gap
\(\ell\le N^{1/6}(\log N)^{O(1)}\) is sufficient. The exact \(R_+\)
bound also covers two close largest primes when the third is not
comparable.


The promise contains many inputs outside the published MRS sufficient
size regions. For every sufficiently large \(X\), partition the primes
in \([1.15X,1.20X]\) into intervals of length at most \(\sqrt X\), take
two primes from one interval, and take the third from
\([X,1.05X]\). There are
\[
\Omega(X^{5/2}/\log^3X)
\]
distinct products in \([X^3,2X^3]\). They have
\(H=\Theta(X)\), an adjacent gap at most \(\sqrt X\), and hence
\(D=O(1)\). In terms of \(Y=X^3\), each such shell contains
\(\Omega(Y^{5/6}/\log^3Y)\) promised instances. This is a shell count,
not a density statement.

These are thin additive-cluster promises, not a two-dimensional region
in prime-size exponent space and not a general solution of factoring
from \(\varphi(N)\).

## Reproduction

\`\`\`sh
./replay.sh
sha256sum -c SHA256SUMS
\`\`\`
