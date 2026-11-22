# A whole-range small-factor deletion in the original giant remainder

Fix an individual even \(N\), a compact central interval \(J\Subset(0,1)\),
and fixed \(1\le a<b<\infty\). Put
\[
L=\log N,\qquad \ell=\log L,\qquad H=\ell^4,\qquad S=e^H,\qquad
Z=e^{\ell^3}.
\]
For real \(\tau\in[a,b]\) let \(B_\tau=N/S^\tau\), \(T_\tau(y)=y/B_\tau\),
and retain the literal sharp score
\[
Q_{\tau,y}(m)=\sum_{\substack{d\mid m\\d<T_\tau(y)}}\mu(d).
\]
In all sums below \(x,r\) are genuine primes, \(x\in NJ\),
\(y=N-x=rm\), and \(m>1\). Write \(\mathfrak S(N)\) for the usual
binary singular series. The small-factor predicate is exactly
\(P^-(m)\le Z\); since all retained \(r\)'s are much larger than \(Z\),
it is also \(P^-(y)\le Z\).

**Theorem.** Given \(A>0\), take sufficiently large fixed \(C,D_A\) and
set
\[
U_0=\frac{\sqrt N}{S^bL^C},\quad
R=\left\lceil\frac{D_A\ell}{\log\ell}\right\rceil,\quad
E=Z^{R+1},\quad U_1=U_0/E .
\]
Uniformly in \(\tau\in[a,b]\), at every sufficiently large even \(N\),
\[
 \sum_{\substack{U_1<r\le B_\tau\\P^-(m)\le Z}}
        (\log x)(\log r)Q_{\tau,y}(m)=O_A(NL^{-A}).                 \tag{1}
\]
No radical restriction is imposed. This uses the complete prime-mark
range, not an arbitrary \(r\)-subinterval. In particular (1) cannot
be inserted into individual \(r\)-slices.

For any fixed nonnegative \(w\in C_c^\infty((a,b))\) of integral one
write \(\overline Q_y(m)=\int w(\tau)Q_{\tau,y}(m)\,d\tau\). Then the
complete **smoothed** score with the same small-factor predicate has
the corresponding deletion at the **unmodified common cutoff**:
\[
 \sum_{\substack{r>U_0\\P^-(m)\le Z}}
       (\log x)(\log r)\overline Q_y(m)
     =O_{A,w,J,a,b}\!\left(\frac{N\mathfrak S(N)}
                                  {\ell\log\ell}\right).           \tag{2}
\]
The right side does not assert arbitrary-log precision for this
cutoff restoration. The upper gate \(r\le B_\tau\) can be
omitted in an averaged score at \(m>1\), since the complete divisor
sum is zero when \(r>B_\tau\). In (1) one may use the giant reduction
with \(U_1\) instead of \(U_0\); the calibration remains the original
\(|J|N\mathfrak S(N)\). In (2) the calibration is already the same as
in [the averaged giant identity](SmoothedTerminalQuotients.md).
Neither statement estimates the whole remaining rough score or
implies a binary representation.

## 1. Exact complete prefixes with forced divisibility

Discard \(x\mid N\) throughout at \(N^{o(1)}\) cost with the actual
divisor-power envelopes. Hence \(y\) and all its divisors are target
units. Let \(e>1\) be squarefree, supported on primes \(\le Z\), with
\(\omega(e)\le R\) and \((e,N)=1\). Impose \(e\mid y\); if \((e,N)>1\)
there are no retained terms. We sum the resulting bounds with the
actual alternating coefficients of all such \(e\).

Use the log-divisor identity and the complete small-mark convolution
of [the original giant reduction](../giant_prime_divisor_remainder/Proof.md),
§2, on the restricted source \(e\mid y\). In the complementary upper
sum \(b'>B_\tau\), write \(n=y/b'<T_\tau(y)\). The log-divisor weight is
\(\mu(n)\log(y/n)\), and the genuine class imposed on \(x\) is
\(N\bmod[e,n]\). In the small-mark upper sum take \(d\mid b'\),
\(d\le U_1\) with exact weight \(\Lambda(d)\). Its class is
\(N\bmod[e,dn]\), since the condition from \(d,n\) is the *product*
\(dn\mid y\). Both classes are reduced and
\[
                  [e,dn]\le E U_1 S^b=\sqrt N/L^C .
\]
Strict upper endpoints in \(n<T_\tau(y)\) are real interval endpoints
of the \(x\)-sum. The log weight has supremum and total variation
\(O(L)\) on the central interval. Thus ordinary maximal-prefix
Bombieri–Vinogradov and partial summation apply. The number of
\((e,d,n)\) yielding any one modulus \(q=[e,dn]\) is at most
\(\tau(q)^3\), because each of \(e,d,n\) divides \(q\);
the unmarked case is included by \(d=1\). With all three weights
included, split at \(\tau(q)^3\le L^{C'}\), use BV of increased
accuracy on that part, and use the trivial \(O(NL^2/q)\)
discrepancy and fixed-order divisor moments on the other part.
This pays the sum of BV errors over all \(e,d,n\) with arbitrary
fixed log saving. Prime powers on the source and discarded source
nonunits are negligible with these grouped divisor envelopes.

Here is the exact local model. Put \(e_0=e/(e,d)\) and
\(D=[e,d]\). Write a contributing squarefree \(n=u n'\) by allocating
to \(u\mid e_0\) all its primes in \(e_0\); then
\((n',e_0N)=1\), \(\mu(n)=\mu(u)\mu(n')\), and
\[
                          [e,dn]=D n'.                           \tag{3}
\]
At a prime in \(e_0\), its occurrence in \(u\) does not change the
least common multiple. At a prime \(p\mid(e,d)\), the exact exponent
of \(p\) in \(d\) is at least one; a factor \(p\) in \(n'\) raises it
by one, giving the \(1/p\) ratio of reciprocal totients (hence the
local factor \(1-1/p\) in the signed harmonic). Formula (3) also
retains the true unit masks.

The signed tail estimates (5) in the original reduction apply with
target mask \(Ne_0\le N^2\), and auxiliary \(D\), at every real
\(T_\tau(y)/u\gg_J S^a/E=S^{a-o(1)}\). Their proof of uniformity via
the finite target-prime product works at this length, since
\(\log(T_\tau/u)\gg H\). In particular the signed sum
\[
                   \sum_{\substack{n'<T_\tau/u\\(n',Ne_0)=1}}
                          \frac{\mu(n')}{\varphi(Dn')}
\]
is \(O_A(L^{-A}/\varphi(D))\) after increasing the accuracy. This
proves the required zero main for the marked upper sum, regardless
of whether \(e_0=1\). If \(d=1\), then \(e_0=e,D=e\) and
\(\varphi(Dn')=\varphi(e)\varphi(n')\). The log weight is
\(\log(y/u)-\log n'\). Its first term multiplies a zero signed
harmonic, and the second tends to a constant independent of \(u\),
divided by \(\varphi(e)\), by the first logarithmic moment (5).
This constant vanishes on summing with
\(\sum_{u\mid e}\mu(u)=0\). Hence the unmarked upper sum also has
zero main for each nontrivial \(e\).

These model errors can indeed be summed before the \(x\)-integral.
One has \(\sum_e\tau(e)/\varphi(e)\ll(\log Z)^2\) by the positive
squarefree Euler product on odd primes. Further, uniformly in \(e\),
\[
 \sum_{d\le U_1}\frac{\Lambda(d)}{\varphi([e,d])}
   \ll \frac{L+\log e}{\varphi(e)} .
\]
For each prime power with \(p\nmid e\) use its ordinary reciprocal
totient; for \(p\mid e\) sum the true factors \(p^{-j+1}\log p\)
over \(j\ge1\). The extra divisor factor from the choices of \(u\)
is at most \(\tau(e)\). Consequently the summed model errors retain
arbitrary-log precision.

On the complete divisor uses of these convolutions, the log weight
gives \(\Lambda(y)\); on \(e\mid y\), \(e>1\) with factors \(\le Z\),
there are no genuine prime \(y\asymp_J N\), and prime powers cost
\(N^{1/2+o(1)}\) in total, also after summing the bounded divisor
envelopes from \(e\). The complete small-mark convolution is
identically zero since \(y>U_1\). Subtract the two evaluated upper
sums from their complete sums. In the lower prefix \(b'\le B_\tau\),
their difference has only marks \(d>U_1\), with coefficient \(\Lambda(d)\).
Their nonprime powers cost \(N^{3/4+o(1)}\): count the \(O(N/d)\)
multiples per power and then sum \(1/d\) over prime powers of
exponent at least two above \(U_1=N^{1/2-o(1)}\), all other
multiplicities being \(N^{o(1)}\). For each remaining true prime mark
\(r>U_1\), setting \(b'=rt\) gives the literal short divisor
factor \(-Q_{\tau,y}(m)\) by complementation at \(m=y/r>1\),
with the weak lower-prefix and strict \(Q_{\tau,y}\) boundaries.
All of these comparisons remain valid with an \(e\)-weight
of absolute value at most one per divisor, or with no \(e\)-weight.
In the unrestricted case the unmarked upper main instead retains
the familiar \(|J|N\mathfrak S(N)\); this verifies the stated
unrestricted calibration also at \(U_1\).

## 2. Exact small-factor predicate to arbitrary-log precision

At an integer \(y\), the alternating sum over nontrivial squarefree
\(e\mid y\), all prime factors \(\le Z\), of degree at most \(R\)
approximates \(1_{P^-(y)\le Z}\) with pointwise error at most
\[
             D_R(y)=\binom{\#\{p\le Z:p\mid y\}}{R+1}.
\]
The true giant score has at most a fixed divisor-power envelope
\(L^2\tau(y)^2\) on each source row. To pay the Boolean error,
write \(D_R(y)^2\) as a sum over two actual product labels, and count
the \([e,f]\)-multiples among \(1\le y\le N\) by \(N/[e,f]\).
For union degree \(j\), each prime is in the first label, the second,
or both. Thus by Cauchy and ordinary divisor moments it suffices
that
\[
 \frac1N\sum_{y\le N}D_R(y)^2
   \le \sum_{j=R+1}^{2R+2}\frac{(3\sum_{p\le Z}1/p)^j}{j!}
   \ll_A L^{-C_A},
\]
with \(C_A\) as large as desired. This follows from
\(\sum_{p\le Z}1/p=O(\log\ell)\) and
\(R\asymp D_A\ell/\log\ell\): once \(N\) is large the term ratio
is \(O((\log\ell)^2/\ell)\), and the initial term is
\(\exp(-\Omega(D_A\ell))\). Increase \(D_A\) to absorb all
weights and the required accuracy. The true aggregate over these
alternating terms was estimated in §1, and the Boolean remainder
is paid on the actual arithmetic rows, proving (1).

## 3. Absolute restoration of the common lower mark after smoothing

Take \(\tau\) against the fixed weight \(w\). Put \(W=S^b\).
For every physical central \(y<N\), a divisor containing a prime
\(>W\) cannot pass any threshold \(T_\tau(y)\). Thus in the smooth
Fourier formula of [the averaged identity](SmoothedTerminalQuotients.md),
§2, truncate the prime product **exactly before integration**:
\[
\overline Q_y(m)=\frac1{2\pi}\int_{\mathbb R}\widehat F(\xi)
 e^{i\xi\log(N/y)/H}
 \prod_{\substack{p\mid m\\p\le W}}(1-e^{i\xi\log p/H})\,d\xi ,
                                                                  \tag{4}
\]
where \(F(t)=\int_{\tau>t}w(\tau)d\tau\) on \(t\ge0\), extended
smoothly with compact support to negative arguments. The extension
does not change any true \(t=\log(dN/y)/H>0\). All valuations are
retained since the Möbius expansion is squarefree-supported.
Write the entire \(W\)-smooth part of \(m\) as \(h\) (with all
its powers), and \(m=h v\) with \(P^-(v)>W\).
The product in (4) depends only on \(h\).
The small-factor indicator in (2) retains \(P^-(h)\le Z\).

Fix a true prime \(U_1<r\le U_0\) and a target-unit \(h\le N^{.01}\).
We need only an upper for the actual prime
\(x=N-rhv\) with \(x\in NJ\), over the actual rough \(v\)'s.
The length is \(O(N/(rh))\), of order at least \(N^{.48}\).
Use Selberg's positive upper sieve with squarefree support
\(\mathcal D=N^{.01}\), sifting primes through
\(Q=\mathcal D^{1/20}>W\). At \(p\le W\) sift both \(v\) and
\(x\); there are two forbidden roots off \(hN\), and exactly
one at \(p\mid hN\) (including \(p=2\), since \(N\) is even).
The prime \(r\) is bigger than \(Q\). At \(W<p\le Q\) sift only
\(x\); its coefficient \(rh\) is a unit and there is exactly one
root, including when \(p\mid N\). The truncated local product
is at most a constant times
\[
 \frac{\mathfrak S(N)c(h)}{H L},
 \qquad c(h)=\prod_{\substack{p\mid h\\p>2}}\frac{p-1}{p-2}.
\]
Indeed relative to \(\prod_{p\le Q}(1-1/p)\prod_{p\le W}(1-1/p)\)
the two-root factors at \(p\le W\) give precisely the binary
corrections, with the extra \((p-1)/(p-2)\) at \(p\mid h\);
the omitted non-target corrections beyond \(W\) have a bounded
inverse product, and omitted target corrections only increase
\(\mathfrak S(N)\).

For clarity the elementary floor reserve is as in §3 of the
original giant reduction: \(\nu(p)\le2\), so in the independent
Selberg denominator product on \(p\le Q\) the mean of \(\log d\)
is \(\sum_{p\le Q}(\nu(p)/p)\log p\le (2+o(1))\log Q\).
Markov retains a fixed fraction below \(d\le\mathcal D\);
the standard bounded Selberg coefficients give floor error
\(O(\mathcal D^2L^2)\) by \(\nu([d,e])\le\tau(d)\tau(e)\).
This is absorbed uniformly by the main upper at the stated
length. Every true \(x\) exceeds \(Q\). Restoring \(\log x\)
therefore gives the bound
\[
                 \ll \frac{N\mathfrak S(N)c(h)}{rhH}
                                                                  \tag{5}
\]
on the fixed \((r,h)\)-row.

For \(h>N^{.01}\), the literal count of possible positive \(v\)
is at most \(N/(rh)\) without a \(+1\), and use \(\log x\le L\).
With the Fourier factor included, its summed \(h\)-harmonic is
\(O(e^{-.01L/H}(2+|\xi|)^{C_b})\), by Rankin with exponent \(1/H\)
and the Euler product at \(\sigma=1-1/H\) in §2 of the averaged
identity. This handles all large-\(h\) tails without any
unproved prime distribution.

Finally at \(\sigma=1\), mark an actual \(p\le Z\) in the positive
Euler harmonic for \(h\), including its full valuation:
\[
 \sum_{\substack{P^+(h)\le W\\P^-(h)\le Z}}
       \frac{c(h)}h\prod_{p\mid h}|1-e^{i\xi\log p/H}|
       \ll_b \frac{|\xi|}{\ell}\,(2+|\xi|)^{C_b}.
\]
The marked local term is bounded by
\(O(|\xi|H^{-1}\sum_{p\le Z}\log p/p)=O(|\xi|/\ell)\);
the other factors are exactly bounded by the same positive
Euler product. The rapidly decreasing \(\widehat F\) thus
pays the entire absolute Fourier integral uniformly.
Multiplying (5) by \(\log r\) and summing over true
\(U_1<r\le U_0\) costs \(\sum\log r/r=O(\log E+1)\), by
fixed-ratio prime upper bounds. Since \(\log E/H=O_A(1/\log\ell)\),
the whole omitted strip with the physical small-factor mask is
\[
 O_{w,A,J,a,b}\!\left(\frac{N\mathfrak S(N)}{\ell\log\ell}\right).
\]
Subtract this strip from the \(\tau\)-averaged (1). This gives (2)
at the exact common cutoff, without importing a sharp per-band
statement or changing the true prime variables.

