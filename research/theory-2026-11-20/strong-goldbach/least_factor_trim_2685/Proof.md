# Trimming the actual semiprime cohort: a central rough Chen bound at .2685

Let \(N=2x\) tend to infinity through even integers, \(L=\log x\),
and \(J=xJ_0\), for any fixed interval of positive length
\(J_0\subset[1,4/3]\). Write \(P=N-y\),
\(M=|J|\mathfrak S(N)\), with the usual Goldbach singular series.
Throughout, \(P\) is a genuine prime. Let \(G=G_J(N)\) count the
rows \(y\in J\) with \(y\) prime, and \(D_2(a)=D_{2,J}(a;N)\)
the rows where \(y\) is the product of two distinct primes both
exceeding \(x^a\), in each case with weight \((\log P)(\log y)\).

**Pointwise lower.** For every sufficiently large even \(N\),
\[
 G+D_2(.2685)>.0047 M,\qquad G+D_2(.2686)>.0030M.              \tag{1}
\]
The exponents are in units of \(x=N/2\); any fixed strictly
smaller exponent in units of \(N\) follows. If a target has no
prime pair, these are lower bounds on genuine squarefree
semiprimes in every fixed such central interval, not a
conclusion that the prime-pair term is positive.

For a signed test at \(a=.2685\), let \(D_w(a)\) be \(D_2(a)\)
with the additional angular weight
\(w(s,t)=4\log s\log t/(\log y)^2\) on \(y=st\).
The same proof gives
\[
                        G+D_w(.2685)>.0037M.                 \tag{2}
\]
In particular, the still unproved same-target upper
\(D_w(.2685)-G\le .0035M\) would imply \(G>.0001M\).
The dyadic mean of this **actual signed difference**, with
denominator \(\sum M\), tends to \(-.074\), not to its
necessary positive value at a hypothetical bad target.
The mean does not establish the required pointwise upper.

## 1. Start the true rough lower at .252

Use the audited packing in
[the previous central rough lower](../central_rough_chen_2663/Proof.md),
equations (2)–(4), with final threshold \(a_0=.252=63/250\).
That proof starts at \(\beta=25/224\) and proves a lower
for the whole rough set. It is valid before the numerical
endpoints .265/.2663: the forced-prime intervals of (4)
can simply be stopped at .252. No point of the ordinary-BV
branch at \(t\ge .254\) occurs in the present application.
The actual full modulus at a forced label \(p_1\) is
\(p_1de\), where \(d,e\) are the large/small sieve banks;
both the ordered residual square-prefix tests before
adjoining \(p_1\) and the **first** square \(p_1^2\) are
paid at the literal moving reduced residue \(N\). Stopping
earlier does not introduce a new marked distribution
hypothesis. The fixed spatial prefixes \(N-J\) and the
same Goldbach local density are retained.

More precisely put
\[
\begin{gathered}
 d_0=.5557,\quad \theta=7/32,\quad A_*=1.00001,\quad s_*=.00005,\\
 \eta(t)=\min\{(1+t)/2,\ 1-(A_*\theta+3t)/2\}-s_*,
 \quad R(t)=\eta(t)-t,\quad \rho(t)=\min(t,R(t)/3).
\end{gathered}
\]
With the usual one-dimensional linear-sieve functions \(f,F\),
the resulting lower is
\[
 \sum_{\substack{y\in J,\ N-y\ {\rm prime}\\P^-(y)>x^{a_0}}}
          (\log P)(\log y)\ \ge\ (b-H-o(1))M,                 \tag{3}
\]
where
\[
 b=\frac{e^{-\gamma}}{\beta}f(d_0/\beta),\qquad
 H=\int_{\beta}^{a_0}
       \frac{e^{-\gamma}F(R(t)/\rho(t))}{t\,\rho(t)}\,dt .
\]
As in the inherited proof, the lower limit means an
arbitrarily small fixed tolerance in the packing, bank and
mesh before the large-\(N\) limit. The term \(\log y=L+O(1)\)
in central \(J\) can replace \(L\) relatively in the
nonnegative count. If \((P,N)>1\), then \(P\mid N\) and
\(P\ge 2x/3\), so the omitted actual rows have mass
\(O(L^2)=o(M)\).

A \(y\) in (3) has at most three prime factors with
multiplicity, since \(4a_0>1\). The number here with a
square factor \(r^2\) is \(O(x^{1-a_0}+\sqrt{x})\), by
opening \(x^{a_0}<r\le\sqrt{4x/3}\); the weighted loss is
\(o(M)\). Squarefree rank three contributes at most
\[
 (3.446\, I_3(a_0)+o(1))M,\qquad
 I_3(a_0)=\int_{a_0}^{1/3}
          \frac{\log((1-2u)/u)}{u(1-u)}\,du .                 \tag{4}
\]
This is the already proved
[3.446 actual angular upper](../angular_prime_first_composite/Proof.md),
applied to a **genuine three-prime product** and its
actual prime opponent \(N-y\). Its normalization in the
larger common interval \(I=[N/3,2N/3]\) is
\(|I|\mathfrak S(N)\) times an ordinary source profile
average on \(I\), so restricting to fixed \(J\) gives
the factor \(|J|/|I|\) in this average and hence \(M\).
The angular density of the three ordered true prime
factors, after the middle-angle integration, is the one
shown in (4). Labels above \(x^{a_0}\), or the same log
threshold divided by \(\log N\) or \(\log y\), have a
common limiting boundary; one may sandwich each upper
using a fixed angular collar, then shrink it after the
large-\(N\) limit. All coordinates stay in a fixed compact
subset of positive exponents, with null boundaries.
No upper on shrinking spatial intervals is used.

Equations (3)–(4) prove
\[
             G+D_2(a_0)\ge(b-H-3.446 I_3(a_0)-o(1))M.        \tag{5}
\]

## 2. One additional, disjoint deletion

For any fixed \(a_1>a_0\) in (1), the exact difference
\(D_2(a_0)-D_2(a_1)\) counts a **genuine semiprime** \(y=st\)
with \(s<t\), \(x^{a_0}<s\le x^{a_1}\), and **the same
genuine prime** \(P=N-y\). It is disjoint from every row
deleted in (4). In fact \(t\ge x^{1-a_1}\), so no equal
factor or factor-order boundary is present in this trim.

Apply the 3.446 upper now with true rank two, same spatial
\(J\) and same two log weights. The ordinary profile mass is
\[
 \Delta I_2(a_0,a_1)
       =\int_{a_0}^{a_1}\frac{du}{u(1-u)}
       =\log\frac{a_1(1-a_0)}{a_0(1-a_1)} .                  \tag{6}
\]
Indeed fix the smaller prime and use PNT in the longer
factor \(t\), of size \(x/s\); multiplying by \(\log y\)
gives \(1/(1-u)\) in its relative density, and summing
\(1/s\) over genuine smaller primes gives \(du/u\).
This is the source normalization of the upper; it is
**not** used as an equality for the actual prime-opponent
count. Sharp spatial or angular interiors can be enclosed
by the fixed Jordan envelopes allowed in that upper.
Target nonunit product labels have power-small harmonic
mass: each \(r\mid N\) in these profiles is of fixed
polynomial size, and on the actual prime-opponent rows
it would require the same already negligible \(P\mid N\).
Replacing \(\log N\) by actual \(\log P,\log y\) is
uniformly relative \(1+O(1/L)\) on all counted positive
rows.

Thus
\[
 G+D_2(a_1)\ge
 \bigl[b-H-3.446\{I_3(a_0)+\Delta I_2(a_0,a_1)\}-o(1)\bigr]M . \tag{7}
\]
There is no second triprime charge at \(a_1\), nor
subtraction of a model as if it were an actual count.

The standalone [rational certificate](check.py) bounds
\(b\) from below and the two integrals and logarithm from
above, using the sieve delay equations and the same
junctions \(t_0=(1-2s_*)/7,\ t_m=(1-A_*\theta)/4\) from the
previous central proof. In the interval above \(t_m\)
the elementary primitive for \(2/[t(A-Bt)]\) is used only
up to \(a_0\), with \(A=1-A_*\theta/2-s_*,B=5/2\).
Its certified lower enclosure for \(b-H-3.446I_3(a_0)\)
is greater than .3001; the lower enclosures in (7)
are greater than .0047 at .2685 and .0030 at .2686.
The exact certificate verifies the strict comparisons
with rational numbers, not with rounded displayed
decimals. Choose the fixed approximation tolerances
inside those strict margins. This proves (1).

## 3. The weighted parity input and its actual normalization

Since \(u=\log s/\log y\) is between \(a_1-O(1/L)\) and
\(1/2\), one has \(w(s,t)\ge4a_1(1-a_1)-O(1/L)\).
The prime atom has weight 1, at least this coefficient.
At .2685 the certificate, multiplying its rational
lower enclosure in (7) by \(4a_1(1-a_1)\), gives a strict
lower enclosure larger than .0037 (with margin). This
proves (2).

Writing \(\Lambda\) for the von Mangoldt function, the
exact signed sum at \(a_1=.2685\) is
\[
 T_w=D_w(a_1)-G
   =\sum_{\substack{y\in J,\ P=N-y\ {\rm prime}\\
             y\ {\rm squarefree},\ P^-(y)>x^{a_1}}}
        (\log P)\left\{\frac{2(\Lambda*\Lambda)(y)}{\log y}
                       -\Lambda(y)\right\}.                 \tag{8}
\]
The bracket is \(-\log y\) on primes,
\(4\log s\log t/\log y\) on true semiprimes, and zero on
true triprimes. No extra largest-factor gate is required.
On this exact support every \(d\mid y,\ d<\sqrt y\) is 1
or prime, since \(2a_1>1/2\). The Dirichlet identity
\(\mu*(\log)^2=\Lambda\log+\Lambda*\Lambda\), where
\((\log)^2(n)=(\log n)^2\), makes the bracket in (8)
also equal to
\[
 \frac{2}{\log y}\!
    \sum_{\substack{d\mid y\\d<\sqrt y}}
       \{\mu(d)(\log(y/d))^2+\mu(y/d)(\log d)^2\}
             -3\Lambda(y).
\]
Squarefree central \(y>1\) has no fixed divisor at
\(\sqrt y\). The complementary \(\mu(y/d)\) retains the
actual parity; its distribution in the true prime-opponent
row is not being asserted.

For the stated mean, average \(N=2n,\ X\le n\le2X\).
The standard positive divisor expansion of \(\mathfrak S\)
gives mean 2 on the even lattice (the convergent mean
Euler product cancels the odd twin-prime factor), so
\(\sum M\sim3|J_0|X^2\). This is the area of
\(2X\le P+y\le4X,\ 2y/(P+y)\in J_0\). In the independent
PNT on these genuine prime or prime-product labels,
the target is automatically even; there is no second
parity factor. Approximate the fixed spatial polygon
by rectangles. The prime-pair angular multiplier is 1;
the genuine semiprime average in (8) is
\[
 \int_{a_1}^{1/2}\frac{4u(1-u)}{u(1-u)}\,du
    =4(1/2-a_1)=.926 .
\]
The endpoints expressed in \(\log x,\log y,\log X\)
differ by \(O(1/\log X)\); bounded angular integrands
and fixed collars justify the limit in (6) and here.
Consequently \(\sum T_w/\sum M\to-.074\). The unweighted
difference has mean \(\log((1-a_1)/a_1)-1\in(.0022,.0023)\).
These genuine averages establish feasibility of the
one-sided tests only, not their validity for each target.

## Comparison

The closest roughness-specific primary preprint found is
[Ratliff, v2, May 25 2026](https://zenodo.org/records/20377091),
which claims a threshold just above .2665 using a
one-start Buchstab branch and a different switched
triprime bound; it records .2667 conditionally. We do not
import either claim or its switched marked factorization.
Here the new step is the physical semiprime trim (6)
after the separately justified fixed-interval rough
count and triprime upper at .252. The \(r\le q^{.9}\)
condition of [Li–Liu, v2](https://arxiv.org/abs/2606.05224v2)
concerns the relative *upper* size of a surviving smaller
factor in a representation \(N=p+rq\), not its positive
lower-exponent threshold. [Chan, November 6, 2026](https://aixiv.online/abs/2611.00586)
claims the stronger relative upper restriction \(r\le q^{.75}\),
also a different restriction. The recent [restricted Chen sieve of
Pham Van Khanh](https://www.preprints.org/manuscript/202611.0694)
separates its explicit positive model from a high-modulus remainder;
its corresponding transfer is conditional pointwise or unconditional
on average, not the fixed-target assertion (1). No priority claim
or use of these newer preprints as inputs is intended.
