# Proof

## 1. Integer anchor and the two known values

Fix \(k\ge4\). Let \(N=\prod_{i=1}^k p_i\) be squarefree with exactly
\(k\) prime factors, and let \(T=\varphi(N)\). Put
\[
 u=N^{1/k},\qquad v=\lfloor u\rfloor,\qquad a_i=p_i-v.
\]
The geometric mean lies between the smallest and largest factors.
Because these factors and \(v\) are integers,
\[
 p_1\le v\le p_k,\qquad |a_i|\le H:=p_k-p_1. \tag{1}
\]
Define the monic integer polynomial
\[
 R(t)=\prod_{i=1}^k(t+a_i)
     =\sum_{j=0}^k c_jt^{k-j},\qquad c_0=1. \tag{2}
\]
The input gives two consecutive values exactly:
\[
 R(v)=N,\qquad R(v-1)=T. \tag{3}
\]
All \(c_j\) are integers and
\[
 |c_j|\le {k\choose j}H^j. \tag{4}
\]

## 2. Recursive finite differences

Suppose \(c_0,\ldots,c_{j-1}\) have been fixed, where
\(1\le j\le k-2\). For \(t>0\), define
\[
 S_j(t)=
 {R(t)-\sum_{\ell=0}^{j-1}c_\ell t^{k-\ell}
  \over t^{k-j-1}}. \tag{5}
\]
Using (2),
\[
 S_j(t)=c_jt+c_{j+1}
       +\sum_{s=2}^{k-j}c_{j+s}t^{1-s}. \tag{6}
\]
The rational center
\[
 \widehat c_j=S_j(v)-S_j(v-1) \tag{7}
\]
is computable from (3) and the preceding candidate coefficients.
Equations (6) and (7) give
\[
 \widehat c_j-c_j
 =\sum_{s=2}^{k-j}c_{j+s}
   \bigl(v^{1-s}-(v-1)^{1-s}\bigr). \tag{8}
\]
For \(s\ge2\), the mean value theorem and (4) imply
\[
 \left|v^{1-s}-(v-1)^{1-s}\right|
 \le {s-1\over(v-1)^s}. \tag{9}
\]
Hence, if \(h\ge H\),
\[
 |c_j-\widehat c_j|\le
 B_j(h):=\sum_{s=2}^{k-j}
 {k\choose j+s}{(s-1)h^{j+s}\over(v-1)^s}. \tag{10}
\]
This is an exact rational interval and can be rounded outward using
integer arithmetic.

## 3. The search tree does not need \(H\)

Try the increasing schedule \(h=1,2,4,\ldots,m\), replacing the
first power of two above \(m\) by \(m\). At a fixed \(h\), start with \(c_0=1\).
For every surviving prefix and each \(j=1,\ldots,k-2\), compute (7) and
branch over all integers in
\[
 [\widehat c_j-B_j(h),\widehat c_j+B_j(h)]
 \cap[-{k\choose j}h^j,{k\choose j}h^j]. \tag{11}
\]
The truncation preserves the true branch once \(h\ge H\), by (4), and
keeps every wrong branch at \(O_k(\log N)\) bits.
At the first \(h\ge H\), the true coefficient prefix survives every
level by (10). No gap information is input to the algorithm.

For a full prefix, let
\[
\begin{aligned}
 A&=N-\sum_{\ell=0}^{k-2}c_\ell v^{k-\ell},\\
 B&=T-\sum_{\ell=0}^{k-2}c_\ell (v-1)^{k-\ell}.
\end{aligned} \tag{12}
\]
Then (3) yields the nonsingular two-by-two system
\[
 A=c_{k-1}v+c_k,\qquad
 B=c_{k-1}(v-1)+c_k, \tag{13}
\]
so
\[
 c_{k-1}=A-B,\qquad c_k=A-v(A-B). \tag{14}
\]
Factor the fixed-degree integer polynomial \(R\). Its integer roots
must be \(v-p_i\); equivalently,
\[
 (-1)^kR(v-X)=\prod_{i=1}^k(X-p_i). \tag{15}
\]
Accept only \(k\) distinct primes greater than one whose product is
\(N\) and whose totient is \(T\).

## 4. Complexity

For fixed \(k\), every rational in (5)--(14) has
\(O_k(\log N)\) bits. At the first successful guess, \(H\le h\le\min(2H,m)\), the
number of tree leaves is at most
\[
 \prod_{j=1}^{k-2}\bigl(1+2B_j(2H)\bigr). \tag{16}
\]
Earlier guesses and the \(O(\log(2+H))\) stages add only a polylogarithmic
factor.

If \(H\le u\), then \(v-1\ge u/3\) (the finitely many smaller inputs can
be handled directly). Since \(k\) is fixed, (10) gives
\[
 B_j(2H)=O_k(H^{j+2}/u^2). \tag{17}
\]
Standard deterministic fixed-degree polynomial factorization and
primality testing are polynomial in \(\log N\), proving (1).

Now assume \(H\le u^{2/k}(\log N)^A\). For
\(1\le j\le k-2\),
\[
 {H^{j+2}\over u^2}
 \le u^{\,2(j+2)/k-2}(\log N)^{A(j+2)}
 \le(\log N)^{Ak}. \tag{18}
\]
All factors in (1) are therefore polylogarithmic. Since
\(u^{2/k}=N^{2/k^2}\), (2) follows.

For \(k=2\), the familiar quadratic recovery from \(N,\varphi(N)\)
needs no enumeration. For \(k=3\), the tree has one level and its exact
tail is \(-c_3/[v(v-1)]\), giving \(O(H^3/N^{2/3})\). The sibling
triprime endpoint theorem is strictly stronger because it replaces
\(H^3\) by the square of the smaller adjacent gap times \(H\). Thus the
new fixed-\(k\) increment here is stated for \(k\ge4\).

## 5. Many promised inputs

Fix a small constant \(\delta>0\) with
\((1+\delta)^k<2\), and take all primes in
\([X,(1+\delta)X]\). Partition this interval into
\[
 J=O(X^{1-2/k})
\]
cells of length at most \(X^{2/k}\). The prime number theorem gives
\(P=\Theta(X/\log X)\) primes in the full interval. If cell \(r\)
contains \(n_r\) primes, convexity (or equalization) gives
\[
 \sum_r {n_r\choose k}
 =\Omega_k(P^k/J^{k-1})
 =\Omega_k(X^{3-2/k}/\log^kX). \tag{19}
\]
Each chosen \(k\)-tuple lies in one cell, so \(H\le X^{2/k}\), while
its product lies in \([X^k,2X^k]\). Writing \(Y=X^k\) proves the shell
count in the README.

For large \(X\), all factors are odd and lie in an interval of ratio
less than two. No one can divide another minus one, so
\(\gcd(N,\varphi(N))=1\).

## 6. Scope

The integer \(k\) is fixed before the input grows. The theorem assumes
exactly \(k\) distinct prime factors and the numeric value
\(\varphi(N)\). It does not assume or compute the factorization of
\(\varphi(N)\), and it does not cover arbitrary \(\omega(N)\), repeated
prime powers, a Carmichael-value oracle, or unassisted factoring.
