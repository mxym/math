# Wide-profile finite-angle reduction for the actual joint giant score

Let \(N\) be even, \(L=\log N\), and \(J\Subset(0,1)\)
a fixed nondegenerate interval. Put \(x\in NJ\),
\(y=N-x\), \(M_N=|J|N\mathfrak S(N)\), and retain the
actual target units \((x,N)=1\).
For a fixed real smooth compactly supported profile \(F\)
on \([0,\infty)\) define the physical score
\[
 P_F(n)=
 \sum_{\substack{r\mid n,\ r<n\\ r\ {\rm prime,\ allowed}}}
   (\log r)\sum_{d\mid n/r}\mu(d)
            F\!\left(\frac{\log(dN/n)}L\right),
 \qquad 1<n<N .
 \tag{1}
\]
The allowed set in this sum may be any set of actual
prime marks; the same convention applies separately to
\(P_G\). In particular it may be a true fixed-power
window with real endpoints. This note places **no small
support condition** on \(F,G\).

**Theorem.** The actual paired magnitude
\[
             \sum_{\substack{x\in NJ\\(x,N)=1}}
                          |P_F(x)P_G(y)|
\]
is \(O_{F,G,J}(M_N)\), uniformly in the allowed marks.
For every fixed \(D>1\), the same weighted sum on rows
with \(\max(\omega(x),\omega(y))>K\) is
\(O_{F,G,J,D}(D^{-K} M_N)\). For any sufficiently
small fixed \(\eta>0\), the weighted sum on rows with
\(P^-(xy)\le N^\eta\) is \(O_{F,G,J}(\eta M_N)\) for
large \(N\), with a constant independent of \(\eta\).
If a mask changes only on prime marks in fixed interior
angular collars of width \(\delta_N\to0\), its change
in the actual paired sum is \(o(M_N)\). In this statement
a collar at \(t\in(0,1)\) is
\(\{r:|\log r/L-t|\le\delta_N\}\); finitely many fixed
interior values are allowed.

Consequently, for any fixed accuracy, the signed paired
sum reduces with arbitrarily small error at scale \(M_N\)
to actual rows with \(x,y\) squarefree, all their prime
factors \(>N^\eta\), and both ranks at most a fixed \(K\).
If the mark masks are fixed angular interval conditions
at interior endpoints (also allowing moving \(o(1)\)
collars there), the resulting score on the retained rows
may use their genuine **own-log** factor angles.
No signed distribution on these finite-angle cells,
positivity of the original paired sum, or Goldbach
representation follows. This extends the positive-tail
reduction in [the narrow joint theorem](JointGiantFiniteRank.md),
not its reciprocal-sum proof. The same conclusions apply
with one leg replaced by the genuine \(\Pi(n)=1_{n\ {\rm prime}}\log n\),
with the tails and mark comparisons on the composite-score leg.

## 1. An envelope that keeps the real mark, including its valuation

Use any fixed smooth compact extension of \(F\) to the
real line. For a prime \(p\le N\), write
\[
 \theta_p=\log p/L,\quad
 A_\xi(p)=|1-e^{i\xi\theta_p}|,\quad
 w_\xi(p)=A_\xi(p)+\theta_p,\quad
 W_\xi(n)=\prod_{p\mid n}w_\xi(p).
\]
Fourier inversion bounds the inner score of (1), for
fixed \(r\), by the integral of
\(|\widehat F(\xi)|\prod_{p\mid n/r}A_\xi(p)\), up to the
fixed Fourier normalization; the real spatial phase
has modulus one. If \(v_r(n)=1\), the normalized log
weight \(\theta_r\) times this divisor envelope is
one of the degree-one terms in \(\prod_{p\mid n}(A_\xi(p)+\theta_p)\).
If \(v_r(n)\ge2\), the divisor envelope retains all
primes of \(n\), and the total \(\theta_r\) over these
repeated marks is at most \(\sum_{p\mid n}\theta_p\le1\).
These repeated marks are therefore paid by the
degree-zero term of the same product. Thus
\[
                 |P_F(n)|\ll
              L\int_{\mathbb R}|\widehat F(\xi)|W_\xi(n)\,d\xi .
                 \tag{2}
\]
No artificial mark is used in the score, and this bound
does not require squarefreeness. It is uniform even
under a restriction to any subset of actual mark choices,
or under bounded multipliers on their terms.

## 2. Corrected polynomial-value sieve envelope, with one extracted prime

Use [Henriot's corrected Theorem 5](https://doi.org/10.1017/S0305004114000280),
with the definitions and growth class in
[the original paper, §2](https://arxiv.org/abs/1102.1643).
We give the local check rather than allow an unspecified
factor at the discriminant. Fix \(D\ge1\). Use the
nonnegative multiplicative first-coordinate function
with value \(D w_\xi(p)\) at every \(p^j\), \(j\ge1\),
unless \(p\mid N\), where it is zero. Use the analogous
second-coordinate function with \(D w_\zeta(p)\).
For \(p>N\) one may cap \(\theta_p\) at \(1\) in these
definitions. Each weight is at most \(3D\).
The two-variable product belongs uniformly to
Henriot's class \(\mathcal M_2(A,B,\epsilon_*)\):
take \(A=3D\), and for any chosen fixed \(\epsilon_*>0\)
absorb the finitely many primes \(p^{\epsilon_*}<3D\)
into \(B\), with at most two entries per prime.
The bound \(B(n_1n_2)^{\epsilon_*}\) and the \(A\)-bound
then hold under the required product coprimality.
There is no positive lower bound assumption on these
weights, and the corrected upper theorem permits zeros.

For the unmarked upper bound use the two primitive
linear forms \(v,N-v\) on \(v\in NJ\).
For the upper bound with a fixed actual \(p\mid x\),
take \(p\nmid N\), set \(x=pv\), use \(v,N-pv\),
and replace the value at **every** \(p^j\) of the
first weight by \(1\). Extract the single positive
factor \(D w_\xi(p)\) outside. This restores the exact
original multiplicative weight also if \(p^2\mid x\).
For this second case assume \(p\le N^{1-\kappa}\),
with any fixed \(\kappa>0\). The parameter scale
is \(X\asymp_J N/p\), which is polynomially large.
The form \(N-pv\) is primitive because \(p\nmid N\).
The product polynomial has degree two and norm \(O(N)\);
take the theorem's fixed coefficient-size exponent
strictly less than \(\kappa\) and its short-interval
exponent, for instance, \(1/2\).
Split the fixed relative interval into boundedly many
pieces if needed to meet the theorem's upper length
condition. Choose \(\epsilon_*\) as required there.
All constants are uniform in \(p,N,\xi,\zeta\) on
these ranges. The unmarked case has the same proof with
\(X\asymp_J N\).

The theorem's initial root product, at primes
\(\ell>2\), uses one root if \(\ell\mid N\), two
otherwise, except that at the extracted prime \(p\)
there is one root. This last change costs a bounded
factor; \(p>2\) because \(N\) is even and \(p\nmid N\).
Mertens and the singular-series factors give
\[
      \prod_{2<\ell\le X}(1-\nu(\ell)/\ell)
                      \ll_{\kappa,J}\frac{\mathfrak S(N)}{L^2}.
\]
The non-target tail beyond \(X\) is summable and the
target tail is at most \(O(L/X)\); the factor at 2
is absorbed in the constant.

In the nonnegative finite sum of corrected Theorem 5,
extend the allowed tuples to their independent Euler
product over \(\ell\le X\). This uses the corrected
exact-valuation density from (0.1)–(0.2) of the erratum.
At \(\ell\mid N\) all nonzero valuations have weight
zero. At \(\ell\nmid Np\) the two roots are distinct;
for either form, valuation \(j\ge1\) and valuation
zero on the other has density
\((1-1/\ell)\ell^{-j}\).
Simultaneously positive valuations are impossible.
Thus the local weighted factor is exactly
\(1+D(w_\xi(\ell)+w_\zeta(\ell))/\ell\) in the extended
product. At the extracted prime \(p\) only the first
form has a root, and its redefined factor \(1+1/p\)
is uniformly bounded (if \(p>X\), there is no such
factor in the product). This check explicitly includes
the prime dividing a leading coefficient. It avoids
any additional target-prime multiplier.

For \(0<u\le N\), uniformly in \(N,\xi\),
\[
             \sum_{\ell\le u}\frac{w_\xi(\ell)}{\ell}
                         \ll 1+\log(2+|\xi|).
 \tag{3}
\]
For the phase term split at \(N^{1/(1+|\xi|)}\),
use \(A_\xi(\ell)\le|\xi|\log\ell/L\) below it,
and \(A_\xi(\ell)\le2\) with Mertens above it.
If the cutoff falls below 2, the full prime sum
satisfies the same bound. The additional term is
bounded by \(\sum_{\ell\le N}\log\ell/(\ell L)\ll1\).
Henriot and (3) now give the two positive inequalities
\[
 \begin{split}
 \sum_{\substack{x\in NJ\\(x,N)=1}}
           D^{\omega(xy)} W_\xi(x) W_\zeta(y)
 &\ll_{J,D}\frac{M_N}{L^2}
            (2+|\xi|)^{C_D}(2+|\zeta|)^{C_D},\\
 \sum_{\substack{x\in NJ,\ (x,N)=1\\p\mid x}}
           W_\xi(x) W_\zeta(y)
 &\ll_{J,\kappa}\frac{M_N}{pL^2} w_\xi(p)
             (2+|\xi|)^C(2+|\zeta|)^C
                \quad(p\le N^{1-\kappa},\ p\nmid N).
 \tag{4}
 \end{split}
\]
For the first, \(\omega(xy)=\omega(x)+\omega(y)\) on
target units. The second has the corresponding
reflected version. All primes summed and extracted
in (4) are factors of the original physical integers.

## 3. Tails and own angular coordinates

Insert (4) into (2) twice and use Schwartz decay of
the fixed transforms. The first line with \(D=1\)
gives the overall absolute bound, and the line with
\(D>1\) gives the high-rank loss.
For a tiny factor \(p\le N^\eta\) use the second line
with a fixed \(\kappa\) as \(\eta\) varies over, say,
\((0,1/4]\). Sum the marked bound over the actual
tiny primes. Its extra factor is
\[
 \sum_{p\le N^\eta}w_\xi(p)/p
                    \ll \eta(1+|\xi|),
\]
by the log-weighted prime harmonic. For a collar at
fixed \(t\in(0,1)\), choose a fixed \(\kappa<1-t\).
Since \(w_\xi(p)\le3\), its marked loss is
\(O_{J,F,G,t}((\delta_N+L^{-1})M_N)\),
by the ordinary reciprocal-prime difference between
the two real endpoints. Applying (2) to the difference
of the two mark masks is legitimate: the same envelope
is supported on rows containing at least one such
actual prime factor. A fixed endpoint approached at
rate \(o(1)\) therefore needs no prime law in short
intervals. A cutoff near zero is already covered by
the tiny-factor estimate, and at angle \(1\) no mark
\(r<n\) survives once its true cofactor has a factor
\(>N^\eta\).

For any fixed desired accuracy, choose \(K\) and
then \(\eta\) to make the absolute rank and tiny
losses that small. After this positive lower floor,
remove actual \(p^2\mid x\) or \(p^2\mid y\) with
\(p>N^\eta\). Their number is \(O(N^{1-\eta})\);
each original score is bounded by \(L\) times a
fixed divisor power, so the absolute weighted loss is
power-small by the ordinary divisor moments and
Cauchy–Schwarz. All remaining ranks are true
squarefree ranks.

For the own-log comparison the number of bilateral
rough target-unit rows is \(O_{\eta,J}(M_N/L^2)\).
This follows from the same corrected-theorem argument
with value \(1\) at powers of primes \(>N^\eta\)
not dividing \(N\), and value zero at all others.
The remaining Euler product is
\(\ll \exp(2\sum_{N^\eta<p\le N}1/p)\ll_\eta1\).
Thus on fixed-rank rows a per-row \(O_{F,G,J,K}(L)\)
error is \(o(M_N)\).

For a squarefree composite \(n\) on those rows, write
its true prime-factor angles as \(u_i=\log p_i/\log n\).
At fixed \(J\) the difference between \(u_i\) and
\(\log p_i/L\) is \(O_J(1/L)\). After paying the mark
collars, \(P_F(n)/L\) can be replaced at per-row
\(O_{F,J,K}(1/L)\) cost by the finite-angle value
\[
    \sum_{i\ {\rm allowed}} u_i
                \sum_{A\subseteq [k]\setminus\{i\}}
                   (-1)^{|A|} F\!\left(\sum_{j\in A}u_j\right),
 \tag{5}
\]
with \(k=\omega(n)\); use value zero on a prime row.
This follows from the uniform \(O_J(1/L)\) spatial
shift, the bounded derivative of the fixed profile,
and the fact that at most \(2^K K\) terms occur.
The count just proved pays the corresponding product
error \(O(L)\). Formula (5) leaves a genuinely signed
finite-angle sum on **actual** reflected integers.

For a true prime opponent, replace its envelope in
(4) by \(L\) times the multiplicative indicator of
\(N^{1/4}\)-rough target units. It bounds \(\Pi(n)\)
on the same central interval. The Euler harmonic
of this new second weight is \(O(1)\) by Mertens,
so the entire argument applies without an extra
log factor; the opposite leg itself is still the
literal prime in the retained signed sum.
