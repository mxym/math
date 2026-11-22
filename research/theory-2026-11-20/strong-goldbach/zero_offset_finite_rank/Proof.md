# Zero-offset, finite-rank composite tests at a prescribed Goldbach target

Let \(N=2x\) be even, \(L=\log x\), and \(J=xJ_0\) for a fixed
nondegenerate interval \(J_0\subseteq[1,3/2]\). In every paired sum let
\(P=N-y\) be an ordinary prime. Write
\[
 {\cal G}_J(N)=\sum_{\substack{y\in J\\ y,\,N-y\ {\rm prime}}}
                    \log y\,\log(N-y)
\]
and write \(\mathfrak S(N)\) for the usual positive Goldbach singular factor
in the [direct fixed-target identity](../direct_goldbach_composite_gap/Proof.md).

Fix \(0<\gamma<\theta<1/2\) and \(g\in C^\infty([0,\infty))\),
equal to \(1\) on \([0,\gamma]\) and to \(0\) on \([\theta,\infty)\).
A nonincreasing \(g\) with values in \([0,1]\) is permitted but not needed.
Define the literal short Möbius score
\[
       S_g(y)=\sum_{d\mid y}\mu(d)g(\log d/L).
\]
The composite score on squarefree \(y\) is \(-\log y\,S_g(y)\).
There is **no** lower bound assumed for any true prime pair or for any
remaining composite angular sum.

**Theorem.** For every \(A>0\), uniformly in the prescribed even \(N\),
\[
 {\cal G}_J(N)=
 -\sum_{\substack{y\in J\ {\rm squarefree\ composite}\\N-y=P\ {\rm prime}}}
     \log P\,\log y\,S_g(y)
       +O_{g,A}(xL^{-A}).                                           \tag{1}
\]
There is a fixed absolute integer \(D\ge2\) such that the absolute
weighted cost of composite rows of rank \(\omega(y)\ge K\), with
\(K\ge D+1\), is
\[
       O_g(2^{-K}x\mathfrak S(N))+O_{g,A}(xL^{-A}).                 \tag{2}
\]
For every \(0<\sigma\le1/2\), uniformly even in \(\sigma\), the absolute
weighted cost of composite rows with \(P^-(y)<x^\sigma\), on **all**
ranks, is
\[
       O_g(\sqrt{\sigma}\,x\mathfrak S(N))+O_{g,A}(xL^{-A}).          \tag{3}
\]
The weights in (2) and (3) are \(\log P\,\log y\,|S_g(y)|\).
These are true sums at the original \(N\); no synthetic prime
weights, conditional zero-free hypotheses, or averaging over \(N\)
are used. There is no moving cutoff at the square root.

Consequently, first prescribe any accuracy \(0<\xi<1\); next fix
\(K\ge D+1\) with \(C_g2^{-K}<\xi/3\), and \(\sigma>0\) with
\(C_g\sqrt{\sigma}<\xi/3\), using a common uniform constant in (2) and
(3). Then for all sufficiently large \(N\), the signed sum in (1)
restricted to \(2\le \omega(y)<K\) and all factors at least
\(x^\sigma\) differs from \({\cal G}_J(N)\) by at most
\(\xi x\mathfrak S(N)\). In particular a lower bound for this
specific signed sum **larger** than that error would suffice.
Neither this inequality nor any positive lower bound for
\({\cal G}_J(N)\) is proved here.

## 1. Where the zero offset comes from

The short scoring kernel can be obtained as a particularly safe
specialization of the [all-small completion](../direct_many_small_renormalization/Proof.md):
choose \(\theta<\epsilon\) and use the same complementary smooth short
weight \(g(\log b/L)\) on both short variables. The raw short variable
is \(b=d\); the free short variable is \(b=cs=y/a\).
On its support every prime factor of \(c\) is below \(C_y=y/x^{1-\epsilon}\),
so the whole \(\mu_2\) cofactor sum is present. Writing
\(\ell_0(n)=\log n\) and \(\mu_2=\mu*\mu\), the exact convolution identity
\[
       (\mu_2*\ell_0)(b)=-\mu(b)\log b
\]
follows by differentiating \(1/\zeta(s)\), or from
\(\ell_0=1*\Lambda\) and \(\mu*\Lambda=-\mu\log\).
Thus raw-long plus completed free is exactly
\(\Lambda(y)-\log y\,S_g(y)\). This identity has no approximation,
balance assumption, or squarefree restriction. We now use it directly,
without needing any old analytic calibration or roughness mask.
For a prime \(y\in J\), \(S_g(y)=g(0)-g(\log y/L)=1\), so its
score \(\Lambda(y)-\log y\,S_g(y)\) is identically zero on that row.

## 2. Actual squarefree progression transfer

It suffices to prove the whole short-model cancellation
\[
 T=\sum_{\substack{y\in J\\N-y=P\ {\rm prime}}}
       \log P\,\log y\,\mu(y)^2 S_g(y)\ll_{g,A}xL^{-A}.              \tag{4}
\]
Indeed the terms where \(y\) is prime give exactly \({\cal G}_J(N)\).
Discard \(P\mid N\) here and below: there are \(O(1)\) primes of \(N\)
in \([x/2,x]\), and \(|S_g(y)|\le \|g\|_\infty\tau(y)=x^{o(1)}\)
on these rows. Thereafter \((N,y)=1\).
Also \(y\) is odd, since the actual opposite prime in this interval
cannot be \(2\) for large \(x\).

Open \(\mu(y)^2=\sum_{e^2\mid y}\mu(e)\), taking only
\(e\le x^\rho\), with \(0<\rho<(1/2-\theta)/2\) fixed.
Large square divisors occur for at most
\(\sum_{x^\rho<e\le\sqrt{1.5x}}\lfloor1.5x/e^2\rfloor
 \ll x^{1-\rho}\) integers; all relevant divisor multiplicities
and logarithmic weights are \(x^{o(1)}\). The truncated short
variable satisfies \(d\le x^\theta\).
The exact modulus for the true prime progression is
\[
                    q=[d,e^2]\le x^{\theta+2\rho}<x^{1/2},
\]
not \(de^2\) when factors are shared. The residue is the actual unit
\(N\bmod q\), since \((de,N)=1\). For each \(q\) there are at most
\(\tau(q)^2\) choices of \(d,e\), and the bounded \(g(\log d/L)\)
and the \(\log y\) weight cost at most \(O_g(L)\) by partial summation.
Apply ordinary Bombieri–Vinogradov in its maximal-prefix form,
with \(\tau(q)^2\) absorbed by Cauchy–Schwarz, the trivial
individual \(O(xL/q)\) bound and ordinary divisor moments.
One may use the Chebyshev sum on actual primes directly; if starting
with \(\Lambda\), the discarded prime powers over the power-subroot
modulus range cost \(O(x^{1/2+\theta+2\rho+o(1)})\).
The resulting main is
\[
 \left(\int_J\log u\,du\right)
 \sum_{\substack{d\le x^\theta\\(d,N)=1}}
 \mu(d)g(\log d/L)\!
 \sum_{\substack{e\le x^\rho\\(e,N)=1}}\frac{\mu(e)}{\varphi([d,e^2])}.
                                                                    \tag{5}
\]

The \(e\)-sum can be extended to infinity here. For each squarefree
\(d\), Rankin with the \(e^{1/2}\) moment bounds the absolute tail by
\[
 \frac{x^{-\rho/2}}{\varphi(d)}
 \prod_{p\mid d}(1+p^{-1/2})
 \prod_{p\nmid d}(1+p^{1/2}/[p(p-1)])
       \ll x^{-\rho/2+o(1)}/\varphi(d).
\]
Indeed the second product converges, and in the first split at
\(p=L\), using at most \(O(L/\log L)\) factors above \(L\).
The total model loss is power-small since
\(\sum_{d\le x^\theta}1/\varphi(d)\ll L^{O(1)}\).

Put \(A_p=1-1/[p(p-1)]\). At \(p\nmid dN\) the extended \(e\)-sum
has factor \(A_p\); at \(p\mid d,\ p\nmid N\) its factor is
\[
                  \frac1{p-1}-\frac1{p(p-1)}=\frac1p .
\]
At \(p\mid N\) it is \(1\). Thus (5) is a target-uniform bounded
factor \(\prod_{p\nmid N}A_p\) times the physical integral times
\(\sum_d b_N(d)g(\log d/L)\), where
\[
 b_N(d)=\mathbf1_{(d,N)=1}\mu(d)\prod_{p\mid d}\frac{1}{p A_p}.
\]
Coefficients here are zero on nonsquarefree \(d\), and empty products
are \(1\).

We verify the last harmonic cancellation uniformly. The series of
\(b_N\) is \(\zeta(1+s)^{-1}F_N(s)\), whose correction factors are
\[
 F_{N,p}(s)=
 \begin{cases}
  (1-p^{-1-s})^{-1},&p\mid N,\\
  1+(1-1/A_p)\dfrac{p^{-1-s}}{1-p^{-1-s}},&p\nmid N.
 \end{cases}
\]
Write \(f_N(a)\) for the coefficients of \(F_N(s)\) in the variable
\(a^{-s}\). The sum of their absolute values is \(O(L^{O(1)})\):
the factors at \(p\nmid N\) converge absolutely, and the factors
at \(p\mid N\) are bounded by the reciprocal Mertens product up
to \(N\). Their absolute \(a^{1/4}\) moment is \(x^{o(1)}\).
For \(p\nmid N\), use \(1-1/A_p=O(p^{-2})\); for \(p\mid N\)
the new local factor is \((1-p^{-3/4})^{-1}\), whose product is
\(\exp(O(L^{1/4}))\) by the same split at \(L\).

The classical Mertens estimate
\(\sum_{n\le T}\mu(n)/n\ll_A (\log(2T))^{-A}\)
follows by partial summation from the classical zero-free region
bound for \(M(T)\) and the identity \(1/\zeta(1)=0\);
see, for example, the explicit primary bounds in
[Lee and Leong](https://arxiv.org/abs/2208.06141).
Convolve \(\mu(n)/n\) with \(f_N(a)\).
For \(x^\gamma\le U\le x^\theta\), split at \(a=\sqrt U\).
The below-split sum saves arbitrary log powers using the preceding
Mertens estimate and the absolute zero moment. The above-split sum
is \(O(L\,U^{-1/8}x^{o(1)})\) by the absolute \(1/4\) moment.
Thus \(\sum_{d\le U} b_N(d)\ll_{g,A}L^{-A}\) uniformly
throughout the transition. Since \(g=1\) below it and \(g=0\)
above it, partial summation gives the same estimate for the smooth
harmonic sum. Multiplication by the physical integral in (5), with
one more log power allowed, proves (4) and hence (1).

## 3. A true two-form sieve in the largest prime factor

On a squarefree composite row write its genuine primes in increasing
order \(p_1<\cdots<p_r=B\). Fix all but \(B\), and put
\(H=p_1\cdots p_{r-1}\), \(X_H=x/(2H)\).
It is enough to sieve the actual primes \(B\) and \(N-HB\) for
\(B\in[2X_H,3X_H]\), an interval of length \(X_H\).
Whenever the original box contains a row, \(B\ge3\),
\(X_H\ge B/3\ge1\), and
\(\log(2X_H)\gg \log B\ge L/r\).
Thus the uniform two-linear-form sieve bound on this box is
\[
 \#\{B\in[2X_H,3X_H]:B,\ N-HB\ {\rm prime}\}
 \ll \frac{x\,\mathfrak S(N)\,r^2}{H L^2}
       \prod_{p\mid H} C(p),\qquad C(p)=\frac{p-1}{p-2}\quad(p>2).
                                                                    \tag{6}
\]
Here the exact local root count is two outside \(NH\), and one
at \(p\mid NH\), including \(2\). The local change relative
to the singular factor is at most the displayed product
over primes of \(H\), since \((H,N)=1\). Note \(C(p)\le2\)
on the physical odd labels.
For an explicit uniform bound use a dimension-two upper beta sieve
at \(X_H^{1/100}\), level \(X_H^{1/4}\). Its bounded level-25
upper factor is absolute; its floor error
\(O(X_H^{1/4}(\log(2X_H))^{O(1)})\)
is dominated by the right scale. Both genuine primes exceed the
sifting limit. Bounded \(X_H\) are covered by increasing the
absolute constant and counting integers trivially. This proof
does not require a polynomial minimum on \(B\), a fixed \(r\),
or any spacing of the other prime labels. The same statement
with \(\log(2X_H)\) in place of \(L/r\) is the ordinary
two-form upper bound. Standard upper beta sieve weights are as in
[Koukoulopoulos, *The Distribution of Prime Numbers*, Theorem 19.1](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf).

For \(u_i=\log p_i/L\), use the physical identity
\[
 S_g(y)=(-1)^r\Delta_{u_1}\cdots\Delta_{u_r}g(0),
        \qquad \Delta_u g(v)=g(v+u)-g(v).
\]
For every \(1\le d_0\le r-1\), iterating the fundamental theorem of
calculus on the \(d_0\) smallest labels, then bounding each remaining
difference in sup norm by 2, gives
\[
         |S_g(y)|\le2^{r-d_0}\|g^{(d_0)}\|_\infty
                        \prod_{i=1}^{d_0}u_i.                     \tag{7}
\]
It is important that the differentiated labels are among the
fixed labels in (6), including when all prime factors are small.

## 4. Ordered harmonic suppression, without a rank loss

Let \(U=\log(1.5x)/L\le2\) and
\(v_p=\log(UL/\log p)\ge0\) for the admissible primes.
In any bin \([b,b+1)\) of \(v_p\) the harmonic mass
\(\sum C(p)/p\) is at most an absolute \(C\ge1\).
This follows by partial summation from the Chebyshev upper bound:
the logarithms of primes in the bin have ratio at most \(e\).
Discarding targets dividing \(N\) can only reduce the mass.

For \(n=r-1\), consider the ordered distinct prime sum of
\(\prod_{i=1}^{d_0}u_i\prod_{i=1}^n C(p_i)/p_i\); the first product
uses the \(d_0\) smallest primes, or the \(d_0\) largest \(v\)'s.
Replace the atomic measure of each prime in a bin by uniform
measure on that bin, with its same weight. Its density is now
bounded by \(C\). Every coordinate moves by at most 1, so do
the ordered coordinates; the exponential weight for the first
\(d_0\) changes by at most \(e^{d_0}\), **not** \(e^n\).
Equivalently, for occupancy \(n_b\) each bin contributes at most
\(C^{n_b}/n_b!\) in the unordered distinct-prime sum. Extending
to tuples with repetitions only increases the positive bound.
It follows, using \(n!\) symmetry or sorting the continuous variables,
that the ordered distinct-prime sum is at most
\[
 e^{d_0} C^n U^{d_0}
 \int_{0\le v_n\le\cdots\le v_1<\infty}
                      e^{-\sum_{i\le d_0}v_i}\,dv_1\cdots dv_n
            =\frac{e^{d_0} C^n U^{d_0}}
                    {d_0!\,d_0^{\,n-d_0}} .                       \tag{8}
\]
For the equality put \(w_i=v_i-v_{i+1}\), \(v_{n+1}=0\).
The absolute Jacobian is 1 and the coefficient of \(w_i\) in
\(\sum_{j\le d_0}v_j\) is \(\min(i,d_0)\).
This treats all ties within bins, without using an asymptotic for
any growing number of actual prime factors.

Combine (6)–(8), using \(\log P\,\log y\ll L^2\), and take
\(d_0=D\) when \(r\ge D+1\), with a fixed \(D>16C+2\).
The bound at rank \(r\), after absorbing constants depending on \(g,D\),
is \(O_g(x\mathfrak S(N)\,r^2(2C/D)^{r-1-D})\).
The tail over \(r\ge K\ge D+1\) proves (2), uniformly in \(K\).

If the smallest prime is below \(x^\sigma\), then the largest
\(v_1\) is at least \(\log(U/\sigma)\).
After the bin spread the condition is at least
\(\log(U/\sigma)-1\).
In the integral insert \(e^{-v_1/2}e^{v_1/2}\), bound the first
factor by \(\sqrt{e\sigma/U}\), and keep the second.
Now every gap coefficient is \(\min(i,d_0)-1/2>0\), including
the final \(i=n\). The integral is
\[
        \prod_{i=1}^n (\min(i,d_0)-1/2)^{-1}.
\]
For \(r\ge D+1\) there is still a geometric tail with ratio
\(2C/(D-1/2)\) and a uniform prefactor \(O_g(\sqrt\sigma)\).
For the finitely many \(2\le r\le D\), take \(d_0=1\) in (7)
and the same integral (each gap coefficient is \(1/2\)).
Their total is also \(O_g(\sqrt\sigma\,x\mathfrak S(N))\).
This proves (3).

## Relation to previous work and scope

The smoothing effect on ordinary moments of truncated divisor sums
is established by [Granville, Koukoulopoulos and Maynard,
(1.2) and Theorems 1.6–1.7](https://arxiv.org/abs/1606.06781).
Here the bound needed is instead an absolute tail **against the
actual opposite prime at a prescribed, comparable-sized shift**,
using upper estimates in the largest genuine factor and a zero-offset
squarefree transfer. The finite-rank score is not a new primality
criterion. We do not import fixed-shift factorization laws, such as
the [2026 Poisson–Dirichlet law for prime predecessors](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/paper.pdf)
or the [higher-order Titchmarsh conjecture preprint](https://arxiv.org/abs/2611.12756),
at shift \(-N\) and comparable scales. The reflected sequences in
[Aquila, November 2026, Proposition 9.2](https://hexagonmath.org/pdf/2611.00798v1)
match prescribed Type I and certain other low-level modeled
inputs while omitting large prime opponents; they do not furnish
the missing signed inequality on true composite values.
No priority assertion or strong Goldbach solution is made.
