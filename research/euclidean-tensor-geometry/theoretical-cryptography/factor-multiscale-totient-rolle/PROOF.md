# Proof

## 1. Two known polynomial values

Write
\[
 P(X)=\prod_{i=1}^k(X-p_i)
     =X^k+b_1X^{k-1}+\cdots+b_k.
\]
The input gives
\[
 P(0)=(-1)^kN,\qquad P(1)=(-1)^kT.                         \tag{1}
\]
We recover \(b_1,\ldots,b_{k-2}\) recursively. The last two
coefficients are then forced by (1).

Suppose \(b_1,\ldots,b_{j-1}\) are fixed, where
\(1\le j\le k-2\). Define
\[
 P_0(X)=X^k+\sum_{\ell<j}b_\ell X^{k-\ell}+AX+B,            \tag{2}
\]
where \(B=(-1)^kN\) and \(A\) is the unique integer making
\(P_0(1)=(-1)^kT\). Since \(P-P_0\) vanishes at \(0\) and \(1\),
\[
 P(X)=P_0(X)+D(X)Q(X),\qquad D(X)=X(X-1),                  \tag{3}
\]
where
\[
 d:=\deg Q\le k-j-2,\qquad [X^d]Q=b_j.                    \tag{4}
\]
Put \(m=k-j=d+2\) and \(F_0=P_0/D\).

## 2. Rolle centers

Choose any consecutive block \(p_a,\ldots,p_{a+m-1}\).
The rational function
\[
 F=P/D=F_0+Q
\]
is smooth on their interval and has these \(m=d+2\) distinct zeros.
Repeated Rolle differentiation gives a point
\(\xi\in(p_a,p_{a+m-1})\) such that
\[
 F^{(d+1)}(\xi)=0.
\]
But \(Q^{(d+1)}=0\), hence
\[
 F_0^{(d+1)}(\xi)=0.                                      \tag{5}
\]
Equation (5) depends only on the known prefix. Its numerator is a
nonzero polynomial of \(O_k(1)\) degree and height
\(\exp(O_k(\log N))\). It is nonzero because \(F_0\) has genuine poles
at \(0\) and \(1\).

Since \(Q^{(d)}=d!b_j\),
\[
 b_j-z(\xi)=\frac{F^{(d)}(\xi)}{d!},\qquad
 z(\xi):=-\frac{F_0^{(d)}(\xi)}{d!}.                       \tag{6}
\]
Thus all real roots of (5) give a fixed finite list of coefficient
centers.

## 3. The local profile bound

Let \(I=[p_a,p_{a+m-1}]\), \(L=L(I)\), and factor
\[
 P=P_{\rm near}P_{\rm far}
\]
according to the \(m\) roots in \(I\) and the \(j=k-m\) roots outside it.
For \(x\in I\),
\[
 |P_{\rm near}^{(r)}(x)|\le C_kL^{m-r}.                    \tag{7}
\]
For an outside root \(q\), let
\(M_q=\max_{x\in I}|x-q|\). Because \(q\) lies outside a consecutive
block, \(M_q\ge L\). Therefore
\[
 |P_{\rm far}^{(s)}(x)|
 \le C_k\,E(I)L^{-s},\qquad E(I)=\prod_{q\notin I}M_q.      \tag{8}
\]
Also
\[
 |(1/D)^{(t)}(x)|\le C_{k,t}p_1^{-2-t}.                   \tag{9}
\]

In a Leibniz term of \(F^{(d)}=(P_{\rm near}P_{\rm far}/D)^{(d)}\),
let \(r,s,t\) derivatives fall on the three factors. Since
\(r+s+t=d=m-2\), (7)--(9) give
\[
 C_kL^{m-r}E(I)L^{-s}p_1^{-2-t}
 =C_k\frac{L^2E(I)}{p_1^2}\left(\frac L{p_1}\right)^t.     \tag{10}
\]
The hypothesis \(H\le u\) implies
\[
 p_1\ge 2^{-(k-1)}u,
\]
because \(u^k\le p_1(p_1+u)^{k-1}\). Hence \(L/p_1=O_k(1)\), and
(6), (10) yield
\[
 |b_j-z(\xi)|\le O_k\!\left(\frac{L(I)^2E(I)}{u^2}\right). \tag{11}
\]
We may independently minimize the right side over all consecutive
\(m\)-blocks at every level.

## 4. Deterministic universal search

For every surviving prefix, fixed-degree exact real-root isolation
finds all roots of (5) and approximates every center \(z(\xi)\) to
absolute error below \(1/4\). All of this is polynomial in \(\log N\)
for fixed \(k\).

The algorithm does not know the successful radii. It runs the finite
search trees associated with dyadic radius vectors
\((2^{s_1},\ldots,2^{s_{k-2}})\), ordered by
\(s_1+\cdots+s_{k-2}\), and intersects every candidate list with the
elementary coefficient cap
\[
 |b_j|\le {k\choose j}N^j.
\]
The first radius vector containing the true branch has total tree size
bounded, up to a fixed-\(k\) polylogarithmic factor, by the product in
(1). Geometric summation over all earlier budgets has the same bound.

For a full prefix, (1) is a nonsingular two-by-two integer system for
\(b_{k-1},b_k\). Factor the resulting fixed-degree polynomial over
\(\mathbb Q\), and accept only \(k\) distinct prime roots reproducing
\(N\) and \(T\). Exact fixed-degree polynomial factorization and
primality testing are polynomial in \(\log N\). This proves (1).

## 5. The multiscale shell

Fix a small \(\delta>0\) with \((1+\delta)^k<2\). Work with primes in
\([X,(1+\delta)X]\), reserving two disjoint fixed positive-length
subintervals: one for local points and one for a far point.

For \(2\le m\le k\), put
\[
 \alpha_m=2^{-(k-m)},\qquad w_m=X^{\alpha_m}.
\]
At every local scale \(m<k\), partition the local interval into cells
of length at most \(w_m\). A cell is rich if it contains at least
\(c_kw_m/\log X\) primes. The total prime mass in non-rich cells is at
most
\[
 O(X/w_m)\,c_kw_m/\log X.
\]
Choosing \(c_k\) sufficiently small and intersecting the rich-anchor
sets over the fixed number of scales leaves \(\Omega(X/\log X)\)
anchors simultaneously rich at every scale.

For each such anchor, choose one new prime from its rich cell at every
scale \(m=2,\ldots,k-1\), and choose the last prime in the reserved far
interval. After deleting the fixed number of previously chosen primes,
each step still has \(\Omega(w_m/\log X)\) choices. Any unordered prime
set is counted at most \(k!\) times.

Order the other factors by distance from the anchor. The \(m\)-th
distance is \(O(w_m)\), and the far distances in the \(m\)-level profile
are \(O(w_s)\). Consequently
\[
 W_m\ll_k X^{\,2\alpha_m+\sum_{s>m}\alpha_s-2}=O_k(1),     \tag{12}
\]
because
\[
 2\alpha_m+\sum_{s>m}\alpha_s=2.
\]
The number of distinct products is
\[
 \Omega_k\!\left(
 \frac{X^{\,1+\sum_{m=2}^k\alpha_m}}{(\log X)^k}
 \right)
 =
 \Omega_k\!\left(
 \frac{X^{\,3-2^{-(k-2)}}}{(\log X)^k}
 \right).                                                  \tag{13}
\]
Putting \(Y=X^k\) gives (2).

The reserved far interval makes \(H\asymp X\), while all factors are
\(\asymp X\), so \(H\le u\) after shrinking the fixed interval if
necessary. All factors are odd and have ratio below two. If
\(p\mid q-1\), then \(q-1\ge2p\), contradicting \(q<2p\). Hence
\(\gcd(N,\varphi(N))=1\).

## 6. Scope

The theorem fixes \(k\) before the input grows, assumes squarefreeness,
and uses one exact numeric value \(\varphi(N)\). It does not cover
repeated prime powers, growing \(\omega(N)\), a factored totient,
Carmichael values, or unassisted factoring. The shell count is a lower
bound for one promised family, not a density or optimality claim.
