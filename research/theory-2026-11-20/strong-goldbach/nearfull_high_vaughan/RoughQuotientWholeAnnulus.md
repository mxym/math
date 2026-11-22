# The whole true rough-quotient annulus in the giant score

Fix \(C_0>1\), \(B_0>0\) and a fixed nondegenerate compact
central interval \(J\subset(0,1)\). Use the literal two-prime
giant score of [TinyMOriginalGiant.md](TinyMOriginalGiant.md):
\(x+mr=N\), \(x,r\) genuine primes, \(x\in NJ\),
\(r\in[N/S^{C_0},N/S]\),
\(S=\exp(\ell^4)\), \(\ell=\log\log N\),
\(T_y=yS/N\) for \(y=N-x\), and
\(Q_y(m)=\sum_{d\mid m,\ d<T_y}\mu(d)\).
All results here are at individual even \(N\) with
\(\operatorname{rad}(N)\le(\log N)^{B_0}\).

**Theorem.** There are fixed \(c,\kappa,\delta_0>0\), with
\(1+2\delta_0<C_0\), such that for each fixed
\(0<\delta\le\delta_0\) the original signed score on the entire
literal cohort
\[
         S^{1+\delta}\le m\le S^{1+2\delta},
          \qquad P^-(m)>z_\delta:=S^{4\delta}                  \tag{1}
\]
equals
\[
\begin{split}
 &|J|N\mathfrak S(N)
   \left\{\rho\!\left(\frac{1+\delta}{4\delta}\right)
                -\rho\!\left(\frac{1+2\delta}{4\delta}\right)\right\}\\
 &\hspace{23mm}+O\!\left(N\mathfrak S(N)\delta^\kappa\right)
                              +o_\delta(N\mathfrak S(N)),       \tag{2}
\end{split}
\]
where \(\rho\) is the Dickman function. In particular the
normalized limsup of the absolute score tends to zero as
\(\delta\downarrow0\) **after** taking the \(N\) limit.
The Dickman difference is \(O(\exp(-c\delta^{-1}\log(1/\delta)))\).
This controls both actual prime and all actual composite
\(m\)'s in (1), with no bank condition in the result. It is not
an \(o(\delta N\mathfrak S(N))\) estimate at the scale of the
prime-\(m\) debit, and does not price \(P^-(m)\le z_\delta\).
The two populations of
[TrueCompositeQuotientCredit.md](TrueCompositeQuotientCredit.md)
are included, not additional signed credits.

## 1. Literal simplification and actual successful banks

For sufficiently large \(N\) after fixed \(\delta\), all \(m\)
in (1) give \(r=y/m\) within the literal giant interval
whenever \(r\) is an integer: \(1+\delta\) and \(1+2\delta\)
are strictly within its two power endpoints in \(S\).
In particular \(m>T_y\), since \(r<N/S\).
Every proper divisor of \(m\) is at most
\(m/P^-(m)<S^{1-2\delta}<T_y\), uniformly on the central
support. Therefore
\[
                             Q_y(m)=-\mu(m)                  \tag{3}
\]
even for nonsquarefree \(m\). No approximation to the
\(Q_y\) cutoff is needed. Also \((m,N)=1\) because
\(z_\delta\) eventually exceeds every fixed power of
\(L=\log N\). The actual affine local factor from
[the whole-window estimate, §2](TinyMWholeWindows.md) is
\(c(m)=\prod_{p\mid m}(p-1)/(p-2)=1+O_\delta(z_\delta^{-1})\),
since the number of prime factors is \(O_\delta(1)\).

Choose the fixed color count \(K\) large enough for a prescribed
fixed log saving in the geometric comparison of
[TrueCompositeQuotientCredit.md, §1](TrueCompositeQuotientCredit.md).
Here \(K\) is independent of \(\delta\). Put
\[
 \alpha_i=\tfrac12+\frac{K-i+1}{4K}\quad(1\le i\le K),\qquad
 J_\delta=\left\lfloor\frac{\log(1/\delta)}{16K\log 3}\right\rfloor .
\]
In family \(j\), \(0\le j\le J_\delta\), take color \(i\) to
consist of the actual primes \(1\bmod4\) in
\[
     [S^{t_{ij}},S^{2t_{ij}}],\qquad t_{ij}=3^j\delta^{\alpha_i}.
\]
For sufficiently small fixed \(\delta\), these colors are
pairwise disjoint both within and between families. Indeed the
ratio between the largest scale of color \(i\) and the smallest
scale of color \(i+1\), in \(\log_S p\) units, is at most
\(2\delta^{3/(16K)}\); for the same color the successive ratio
of starting scales is \(3\). The geometric requirement
\(10\sum_{\nu<i}(2t_{\nu j})<t_{ij}\) follows from the ratio
\(\delta^{1/(4K)}\) in a single family. Every prime in the
alphabet exceeds \(z_\delta\) and is at most \(S^{2\delta^{1/2}}\).
For all sufficiently large \(N\) after \(\delta\), the reciprocal
mass of every color is in \([1/4,1/2]\) by the prime harmonic
law in the fixed progression \(1\bmod4\). There are
\(\asymp_K\log(1/\delta)\) families.

Let \(E_\delta(m)\) indicate a real family whose colors are
all hit by actual factors of \(m\); use its first hit when
extracting. Replace the left genuine prime \(x\) by rough
\(\Lambda(x)\), at \(Z=\exp(L^{.24})\) and with exact
Vaughan cutoffs \(N^{.10},N^{.10}\), as in §2 of the cited
geometric comparison. All prime factors of \(m\) are below
\(Z\), and the two source Type II factors are \(Z\)-rough.
On the covered part extract one true prime per color into
\(w\mid m\), with the normalized reciprocal hit allocation,
and put \(m=w m'\). First remove the actual bank squares
\(p^2\mid y\), then \(\mu(m)=(-1)^K\mu(m')\) and the roughness
constraint in (1) is the same on \(m'\). Earlier family events
are unchanged. Restoring squared rows after opening, with no
selected-tag gcd mask in the residual, is harmless: an altered
row still has \(w\mid m\mid y\) and an actual \(p^2\mid y\).
The primes in these banks are larger than every fixed power
of \(L\), so their multiple count and fixed crossed divisor
moments pay arbitrary logs.

The other factor is the actual residual \(b=m'r\), with its
true logarithmically weighted giant prime \(r\), the genuine
\(-(-1)^K\mu(m')\), the exact rough/family masks, and reciprocal
hit weights. All fixed \(m\)-window cutoffs are separated by
the usual one smooth Mellin integral on \(w m'\); smoothing
is paid by actual divisors \(m\mid y\) as in the cited proof.
There is no tag-dependent \(Q_y\) score left because of (3).
The residual coefficient is \(O(L\tau(b)^{O(1)})\) uniformly
on \(b\ll N/Y\), and its square norm is
\(O((N/Y)L^{O(1)})\), by literal divisor moments and bounded
archimedean factors. At small radical, the uniform long
\(\mu\)-character bound and the restricted Bessel Gram
supply the full projected major bound. The geometric
minor comparison and Cauchy give arbitrary fixed log
saving on this covered Type II sum.

The two Type I terms use **true** \(r\)-prime BV at scale
\(N/m\) in the actual moduli \(q=a f e\), with the precise
unit class \(N\bar m\bmod q\). The derivative calculation
in [TrueCompositeQuotientCredit.md, §2](TrueCompositeQuotientCredit.md)
applies at each \(m\): primes of \(mN\) only meet the small
roughness label \(e\), and the signed model is exactly
\(|J|N\mathfrak S(N)c(m)/m\) times the outer coefficient.
This calculation did not require \(m\) to consist of a
complete tag: its needed hypotheses were that \(m\) is a
target unit and all its prime factors are below \(Z\).
Here the outer coefficient is the bounded
\(-\mu(m)E_\delta(m)1_{P^-(m)>z_\delta}\) in (1).
The error is summed by \(\sum_m1/m=O(\ell^4)\), not by
the number of \(m\)'s. Thus the signed covered score is
\[
 -|J|N\mathfrak S(N)
  \sum_{\substack{m\text{ in }(1)\\E_\delta(m)=1}}
                \frac{\mu(m)c(m)}m +O_\delta(NL^{-D})          \tag{4}
\]
for a fixed prescribed \(D>0\) with the initial \(K\)
sufficiently large. Constants in log-saving/limit errors
are allowed to depend on \(\delta\); the fixed \(K\) is
selected before \(\delta\).

## 2. A conditional rough **integer** bound for the actual misses

Let \(F(m)=1-E_\delta(m)\). The reciprocal mass of actual
integer \(m\)'s in (1) with \(F(m)=1\) satisfies
\[
                  \sum_{m\text{ in }(1)}\frac{F(m)}m
                         \ll \delta^\kappa+o_\delta(1).        \tag{5}
\]
To see this, expand the Boolean failure product as a signed
sum of separable avoidance patterns on the bank primes, with
at most \((1+2^K)^{1+J_\delta}\le\delta^{-C_K}\) terms.
Each avoidance indicator is replaced by its signed
Bonferroni sum up to degree \(R\), with error bounded by the
positive degree-\(R+1\) divisor count on its exact alphabet.
Add all of these positive errors to the signed approximation.
This gives a pointwise **nonnegative upper** \(P(m)\ge F(m)\),
supported in squarefree bank divisors \(b\mid m\) of degree
at most \(R+1\); its coefficients, with multiplicity, have
only the fixed \(\delta^{-C_K}\) pattern loss.

The total reciprocal mass of the bank primes
is \(O_K(\log(1/\delta))\). Choose
\(R=\lceil C'_K\log(1/\delta)\rceil\) with a sufficiently
large fixed \(C'_K\). In the independent integer local model,
the difference between the mean of \(P\) and that of \(F\)
is at most twice the pattern count times the
degree-\(R+1\) reciprocal tail, hence \(O(\delta^{10})\).
In this model each disjoint family succeeds with
probability at least \(b_K=(1-e^{-1/4})^K>0\).
The independent failure mass is therefore
\(O(\delta^\kappa)\) for some fixed \(\kappa>0\),
which we may take \(<1\).

Apply the nonnegative dimension-one upper beta sieve
\(\Lambda^+(m)\ge1_{P^-(m)>z_\delta}\) with support
\(d\le S^{.1}\) and prime alphabet \(p\le z_\delta\).
The sieve ratio \(.1/(4\delta)\) is large for all
sufficiently small \(\delta\), so
\(\sum_d\lambda_d^+/d\ll1/\log z_\delta\)
with a constant uniform in such \(\delta\).
Multiply by \(P(m)\), which is a positive upper regardless
of the signs of its opened coefficients. The bank primes
are strictly above \(z_\delta\), so \(b,d\) are coprime,
and every combined modulus is the true product \(bd\).
For sufficiently small fixed \(\delta\),
\(b\le S^{2(R+1)\delta^{1/2}}\le S^{.1}\).
Thus counting the \(bd\)-multiples in the real interval
\([M_-,M_+]=[S^{1+\delta},S^{1+2\delta}]\) with weight
\(1/m\) has the main
\(\log(M_+/M_-)/(bd)\), and its \(O(1/M_-)\) floor,
summed over all \(d,b\) and patterns, is
\(O_\delta(S^{.2}/M_-)\).
The product of the two main densities includes
\(1/\log z_\delta\) times \(O(\delta^\kappa)\).
Since \(\log(M_+/M_-)=\delta\ell^4\) and
\(\log z_\delta=4\delta\ell^4\), this proves (5).
In particular this argument bounds the missed harmonic
**conditional on actual roughness**; an unconditional
bank-failure density alone would not suffice.

At fixed actual \(m\), use the genuine two-affine-prime upper
sieve of TinyMWholeWindows with \(y\) in the full compact
interval. Its bound is \(O(N\mathfrak S(N)c(m)/m)\),
and \(|Q_y(m)|\le1\) here by (3).
Since \(c(m)=1+o_\delta(1)\), (5) controls the true original
missed signed score by \(O(N\mathfrak S(N)\delta^\kappa)
+o_\delta(N\mathfrak S(N))\), and the same bound replaces
the restricted harmonic in (4) by the entire actual harmonic.

## 3. Evaluation of the ordinary signed rough harmonic

Put \(\eta=4\delta\). The signed harmonic of the genuine
squarefree \(m\)'s in (1), weighted by \(\mu(m)/m\), converges
at each fixed \(\delta\) to the mass of the measure
\[
                \exp_*(-\nu_\eta),\qquad
               \nu_\eta(dt)=1_{t>\eta}\frac{dt}{t},
\]
on \([1+\delta,1+2\delta]\).
Indeed the number of possible prime factors in this interval
is finite at fixed \(\delta\). For rank \(k\) open its \(k\)
true distinct primes and divide by \(k!\). Repeated primes
cost \(O_\delta(\sum_{p>z_\delta}p^{-2})\).
By reciprocal PNT the \(k\)-fold product of actual prime
measures in \(t_i=\log_S p_i\) converges to the product
of \(dt_i/t_i\) on their compact supports. The product cuts
are the literal interval of \(\sum_i t_i\), whose boundaries
have zero Lebesgue measure. The sign is \((-1)^k\), giving
exactly this finite-rank convolution expansion. The factor
\(c(m)=1+o_\delta(1)\) does not change the limit.

For completeness let \(\rho(t)=0\) on \(t<0\), \(1\) on
\(0\le t\le1\), and \(t\rho'(t)=-\rho(t-1)\) on \(t>1\),
the Dickman function. The Laplace transform
\(R(s)=\int_0^\infty e^{-s t}\rho(t)\,dt\) for \(s>0\)
satisfies \(sR(s)=\exp(-\int_s^\infty e^{-v}dv/v)\).
This follows by integrating the differential equation
by parts and using \(sR(s)\to1\) as \(s\to\infty\).
Hence the signed measure
\(\delta_0(dt)+\eta^{-1}\rho'(t/\eta)\,dt\)
has the same Laplace transform as \(\exp_*(-\nu_\eta)\).
The latter has finite exponentially weighted variation
for every \(s>0\), so Laplace uniqueness applies.
The annular mass is thus
\(\rho((1+2\delta)/\eta)-\rho((1+\delta)/\eta)\).
The sign in (4) is its negative, as in (2).
The positive decreasing Dickman function has
\(u\rho(u)=\int_{u-1}^u\rho(v)\,dv\) on \(u>1\), and
therefore \(\rho(u)\le1/\lfloor u\rfloor!\), giving
the stated decay. Together with (4) and (5) this proves
(2) with fixed \(K\), then fixed \(\delta\), then \(N\)
large. Neither moving \(\delta\) with \(N\) nor a
prime-debit-scale signed asymptotic is asserted.
