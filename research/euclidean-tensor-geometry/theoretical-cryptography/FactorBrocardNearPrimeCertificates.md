# Short-prime certificates for the Brocard–Ramanujan equation

Let \(W(X,H)\) count the integers \(X<n\le 2X\) for which there exists an
odd prime \(p=n+r\), \(2\le r\le H\), satisfying
\[
                         \left(\frac{n!+1}{p}\right)=-1 .
\]
Such a prime certifies that \(n!+1\) is not a square.

**Theorem.** For each fixed \(0<c<1/8\), uniformly for integers
\(2\le H\le c\log X/\log\log X\), as \(X\to\infty\),
\[
                       W(X,H)=(1+o(1))\,\frac{(H-1)X}{2\log X}.    \tag{1}
\]
The number of \(n\) certified by at least two different offsets is
\(O(XH^2/(\log X)^2)\). If \(H\to\infty\), conditional on having a
certificate in this range, the least witnessing offset divided by \(H\)
converges in distribution to uniform on \([0,1]\).

The contribution is a count of **local certificates with nearby prime moduli**.
For example, at least \((c/2+o(1))X/\log\log X\) integers in the dyadic
interval have such a certificate with \(p-n\le c\log X/\log\log X\).
The underlying Wilson test was used by
[Helou–Haddad, Lemma 1.1](https://doi.org/10.1007/s11139-008-9139-8)
to find infinite excluded families. This note does not replace
[Berend–Osgood's density-zero theorem](https://www.sciencedirect.com/science/article/pii/0022314X9290020P)
or [Bui–Pratt–Zaharescu's power-saving bound](https://arxiv.org/abs/2204.08423)
on the number of actual solutions. It does not recheck a finite
computational search bound, and does not prove all nonsolutions have close
certificates.

## 1. The characters and their multiplicities

If \(p=n+r\) is prime and \(2\le r<p\), then Wilson's theorem gives
\[
                  n!\equiv\frac{(-1)^r}{(r-1)!}\pmod p .
\]
Set \(a_r=(r-1)!\) and \(A_r=a_r(a_r+(-1)^r)\).
It follows by multiplication by \(a_r^2\) that
\((\frac{n!+1}{p})=(\frac{A_r}{p})\).
The two positive factors of \(A_r\) are coprime and consecutive.
They cannot both be squares, so \(A_r\) is not a square.
Write \(D_r>1\) for its positive squarefree part. It defines a
nonprincipal primitive quadratic character \(\chi_r\), with
conductor equal to the positive fundamental discriminant \(D_r\)
if \(D_r\equiv 1\pmod4\), and \(4D_r\) otherwise.

Fix \(c<1/8\) and choose \(2c<\delta<1/4\).
For \(Q=X^\delta\) and the indicated range of \(r\),
\[
          \log(4A_r)\le \log 8+2(r-1)\log(r-1)
                  \le (2c+o(1))\log X<\log Q .
\]
Here the bound also covers \(r=2\). Thus \(q_r\le Q\), and
\(A_r<X\), so no prime in the relevant dyadic interval divides even
the square part of \(A_r\). At these primes the symbol agrees with \(\chi_r\).

The crucial arithmetic fact is
\[
           M(H):=\max_D\#\{2\le r\le H : D_r=D\}=o(H).       \tag{2}
\]
For this, suppose \(r<s\le 4r/3\), with \(r\) sufficiently large.
If a prime \(\ell\) lies in \([r/2,(s-1)/2]\), then \(\ell\le r-1\)
and \(2\ell\) is the only multiple of \(\ell\) in \([r,s-1]\).
Indeed \(\ell<r\), \(2\ell\) lies in the interval, \(3\ell>s-1\),
and \(v_\ell(2\ell)=1\). Since \(\ell\mid a_r,a_s\), it divides
neither \(a_r+(-1)^r\) nor \(a_s+(-1)^s\).
The valuations \(v_\ell(A_r)\) and \(v_\ell(A_s)\) consequently
have opposite parity, proving \(D_r\ne D_s\).

Fix \(0<\eta<1\) and partition \([\eta H,H]\) into a bounded number
(depending on \(\eta\)) of intervals with upper endpoint at most
\(4/3\) times the lower endpoint. Within each such interval, two offsets
of the same square class must differ by \(o_\eta(H)\), uniformly:
by the prime number theorem, any subinterval of
\([\eta H/2,H/2]\) having length at least \(\varepsilon H\)
contains a prime for all sufficiently large \(H\) in terms of
\(\eta,\varepsilon\). This follows directly by subtracting the prime
number theorem at the two endpoints, uniformly bounded below by
\(\eta H/2\). Thus each class occurs \(o_\eta(H)\) times above
\(\eta H\), and at most \(\eta H\) times below. Letting \(\eta\downarrow0\)
proves (2). For positive \(D\), the fundamental discriminant
determines \(D\) uniquely; hence (2) is also the maximum multiplicity
of any of the primitive characters in our list.

## 2. Mean cancellation at prime arguments

We show
\[
                 \sum_{2\le r\le H}\left|
                     \sum_{X<p\le 2X}\chi_r(p)
                   \right|=o(HX/\log X) \qquad(H\to\infty).      \tag{3}
\]
We use the original log-free density estimate of
[Jutila, *On Linnik's constant*, Theorem 1, (1.8)](https://www.mscand.dk/article/download/11701/9717):
for primitive characters of conductor at most \(Q\), the total number of
zeros with real part at least \(\sigma\) and \(|\operatorname{Im}\rho|\le T\)
is
\[
          N_Q(\sigma,T)\ll_\epsilon
                     (Q^2 T)^{(2+\epsilon)(1-\sigma)}
            \qquad (4/5\le\sigma\le1,\ T\ge1).                   \tag{4}
\]
It counts the possible exceptional real zero as well.

Put \(T=(\log X)^2\). Choose \(\epsilon>0\) so that
\((4+2\epsilon)\delta<1\). Then for some fixed \(b<1\) and all
sufficiently large \(X\), the right side of (4) is \(O_\epsilon(X^{b(1-\sigma)})\).
Summing \(X^{\beta-1}\) over all high-real-part zeros in this family gives
\[
 \begin{aligned}
 \sum_{\chi\ {\rm primitive},\ \operatorname{cond}\chi\le Q}
       \ \sum_{\substack{\rho\ {\rm of}\ L(s,\chi)\\
                   \beta\ge 4/5,\ |\gamma|\le T}}
                  X^{\beta-1}
 &=
 X^{-1/5}N_Q(4/5,T)\\
 &\quad +\log X\int_{4/5}^1 X^{\sigma-1}N_Q(\sigma,T)\,d\sigma
 =O_\epsilon(1).                                               \tag{5}
 \end{aligned}
\]
The equality follows from writing each weight as its value at \(4/5\)
plus the integral of its derivative. The constant in (5) need not be
small; (2) will absorb it.

Let \(w\) be any fixed smooth function compactly supported in
\((0,\infty)\) and let \(\widehat w\) denote its Mellin transform.
For a nonprincipal primitive character \(\chi\) of conductor \(q\),
Mellin inversion and the logarithmic derivative of \(L(s,\chi)\) give
\[
 \sum_{m\ge1}\Lambda(m)\chi(m)w(m/X)
      =-\sum_\rho X^\rho\widehat w(\rho)
         +O_w(1+X^{-1/2}\log(2q)).                              \tag{6}
\]
Here \(\Lambda\) is the von Mangoldt function and the sum runs over
nontrivial zeros with multiplicity. To see the stated uniform error,
shift the integral of \(-L'/L(s,\chi)\widehat w(s)X^s\) from
\(\operatorname{Re}s=2\) to \(-1/2\). This crosses the nontrivial zeros
and potentially the trivial zero at 0, whose contribution is bounded.
The functional equation bounds the logarithmic derivative on the new
line by \(O(\log(q(2+|t|)))\), and \(\widehat w\) decays faster than any
fixed power of \(|t|\) on the whole strip. Horizontal lines may be
taken a reciprocal logarithmic distance away from zero ordinates,
by the standard unit-interval zero count
\(O(\log(q(2+|t|)))\), so the horizontal integrals vanish; the zero
sum in (6) converges absolutely. These analytic facts for Dirichlet
\(L\)-functions are also recorded in
[Davenport, *Multiplicative Number Theory*](https://doi.org/10.1007/978-1-4757-5937-0).

For \(q\le Q\), low-real-part zeros \(\beta<4/5\) with
\(|\gamma|\le T\) contribute
\(O_w(X^{4/5}T\log(q(T+2)))=o(X)\) per character, by the local count.
Zeros with \(|\gamma|>T\) contribute
\(O_w(X T^{-2}\log(q(T+2)))=o(X)\) per character, by the same
count and Mellin decay of order at least 3. The remaining terms
summed in absolute value over our \(H-1\) offsets are
\[
                     O_w(X\,M(H))=o(HX)
\]
by (5) and boundedness of \(\widehat w\) on
\(4/5\le\operatorname{Re}s\le1\).
No character is omitted from this estimate to remove an exceptional
zero. Its total contribution is covered by (5) and its repetitions
by (2).

Prime powers \(m=p^j,\ j\ge2\) with \(m\) in the support contribute
\(O_w(\sqrt X(\log X)^2)\) per character. For prime terms in a fixed
compact subinterval of \((0,\infty)\) after division by \(X\),
replacing \(\log p\) by \(\log X\) costs \(O_w(X/\log X)\) per
character by the ordinary prime number theorem. Thus the smoothed
version of (3) follows after dividing by \(\log X\).
For the sharp indicator of \((1,2]\), choose smooth weights that
agree with it outside two arbitrarily small fixed neighborhoods of 1
and 2, with values in \([0,1]\) and compact support.
The ordinary prime number theorem bounds the contribution of these
neighborhoods to the average error, uniformly in \(\chi\), by a
constant times their total width times \(HX/\log X\).
Letting that width tend to zero proves (3). If \(H\) stays bounded,
the ordinary prime number theorem in fixed arithmetic progressions gives
the corresponding cancellation for each of these finitely many characters.

## 3. Counting certificates and avoiding double counts

For each \(r\), the primes for \(X<n\le2X\), \(p=n+r\), lie
in \((X+r,2X+r]\). Replacing this by \((X,2X]\) changes at most
\(O(H)\) terms per offset. This is \(o(X/\log X)\) uniformly.
Since at these primes \(\chi_r(p)\) never vanishes,
\(\mathbf 1_{\chi_r(p)=-1}=(1-\chi_r(p))/2\).
Equation (3) and the ordinary prime number theorem show that the count
of witnessing pairs \((n,r)\) is
\[
                        (1+o(1))\frac{(H-1)X}{2\log X}.
\]
The bounded-\(H\) argument and the \(H\to\infty\) argument together give
uniformity: any sequence contradicting uniformity would have a subsequence
with \(H\) fixed or tending to infinity.

For two distinct offsets the underlying integers \(n+r,n+s\) must
both be prime. The upper-bound sieve bounds the count for \(0<h=|r-s|\le H\) by
\[
            \ll \frac{X}{(\log X)^2}
                   \prod_{\substack{\ell\mid h\\\ell>2\ {\rm prime}}}
                                  \left(1+\frac1{\ell-2}\right). \tag{7}
\]
For odd \(h\) the count is zero in our range. To get the required
**uniformity** for even \(h\), sieve the product of the two forms.
For squarefree \(d\) the number of \(n\) with \(d\) dividing the product
is \(X\nu(d)/d+O(\nu(d))\), where \(\nu\) is multiplicative with
\(\nu(\ell)=1\) for \(\ell\mid h\) and 2 otherwise. The dimension-two
upper sieve axiom holds with absolute constants: for \(\ell>2\),
\((1-\nu(\ell)/\ell)^{-1}\le (1-2/\ell)^{-1}\), and its ratio
to \((1-1/\ell)^{-2}\) is \(1+O(1/\ell^2)\) at the worst value
\(\nu=2\). Mertens's theorem supplies the usual logarithmic ratios,
and \(\ell=2\) has \(\nu=1\). Apply the upper estimate of the
[fundamental sieve lemma, Koukoulopoulos, Theorem 19.1](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf),
with cutoff \(y=X^{1/20}\) and level \(D=X^{1/2}\).
Its error is \(O(\sum_{d\le D}2^{\omega(d)})=O(X^{1/2}\log X)\).
All primes counted in (7) are larger than \(y\). The sieve product
is bounded by a dimension-two Mertens product times
\(\prod_{\ell>2,\ \ell\mid h}(1+1/(\ell-2))\), by taking the
ratio of each exceptional odd factor to \(1-2/\ell\).
This proves (7) with an absolute constant, without extrapolating
a fixed-offset asymptotic. Its average for \(1\le h\le H\) is bounded:
expand the product over squarefree divisors, sum over \(h\), and
bound by the convergent product
\(\prod_{\ell>2}(1+1/(\ell(\ell-2)))\).
There are at most \(H\) pairs of offsets per difference. So the total
number of pairs \((r,s)\) witnessing the same \(n\), counted over
all \(n\), is \(O(XH^2/(\log X)^2)\).
This is negligible relative to the pair main term because
\(H/\log X=O(1/\log\log X)\).
The first two Bonferroni inequalities now prove (1) and the stated
multiple-witness bound.

Finally, fix \(0<t\le1\) and apply (1) to \(\lfloor tH\rfloor\)
and to \(H\) itself. Their ratio tends to \(t\), which is exactly
the limiting cumulative distribution of the minimum offset divided by \(H\).
The case \(t=0\) gives zero directly.

The [integer replay](verify_factor_brocard_near_prime.py) tests the Wilson
identity, the square-class separator, and the union and overlap combinatorics
on finite examples. It does not test or replace the analytic density input.
