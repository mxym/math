# Joint signed deletion by the complete set of genuine tiny labels

Use the same literal fixed-target, sharply gapped, all-small-completed
score \(H_z(y)=\mathcal R_{\rm gap}^{\rm all}(y)\) as in the
[least-factor deletion](../direct_completed_rough_deletion/Proof.md).
In particular \(N=2x\) is even, \(L=\log x\), \(\ell=\log L\),
\(z=x^{1/\ell^2}\), \(\delta_x=3\log\ell/\ell\),
\(R_\pm=x^{1/2\pm\delta_x}\), \(C_y=y/x^{1-\epsilon}\),
and \(J=xJ_0\) for a fixed interval \(J_0\subset[1,3/2]\).
Fix \(0<\epsilon<.005\), then let \(x\) tend to infinity.
All paired counts below use the actual prime \(P=N-y\).

Let \(Y_0=x^{.01/\ell}\), and let \(\mathcal E\) be the
set of all true primes in \((z,Y_0]\).
For each squarefree, \(z\)-rough \(y\) write
\(\mathcal E(y)=\{p\in\mathcal E:p\mid y\}\) and let
\(k(y)\) be the number of genuine prime factors below \(C_y\).

**Theorem.** Uniformly in the even target,
\[
 \sum_{\varnothing\ne T\subseteq\mathcal E}
 \left|\sum_{\substack{y\in J,\ N-y=P\ {\rm prime}\\
             y\ {\rm squarefree},\ P^-(y)>z,\ \mathcal E(y)=T}}
                      \log P\,H_z(y)\right|
       \ll_{\epsilon,J_0}\frac{x\mathfrak S(N)}{\ell}.        \tag{1}
\]
The same left side restricted to \(k(y)\ge3\) is
\(o_{\epsilon,J_0}(x\mathfrak S(N))\).
Consequently an arbitrary bounded function of the *whole actual
tiny-prime set* with value zero at the empty set can be inserted
in the many-small score at \(o(x\mathfrak S(N))\), even if the
function changes with \(N\).
There is no assertion about the physical sum of absolute row
scores inside a profile, nor about the bank-free profile.
The calculation keeps the same \(R_\pm\) in every row.

## 1. A coefficient norm and actual prime progression transfer

Use one variable \(t_p\) for each \(p\in\mathcal E\).
Use the absolute coefficient norm
\(\|\sum a_{\boldsymbol j}\boldsymbol t^{\boldsymbol j}\|_1
=\sum |a_{\boldsymbol j}|\) with its submultiplicative law.
All series in this norm below converge absolutely, and the
number of variables is finite at each \(x\). A monomial has
norm 1. Put \(f_{\boldsymbol t}(p)=t_p\) in \(\mathcal E\)
and \(f_{\boldsymbol t}(p)=1\) otherwise, with complete
multiplicativity on positive integers. Consider the polynomial
\[
 \mathcal D(\boldsymbol t)=
  \sum_{\substack{y\in J\\P=N-y\ {\rm prime}}}
       \log P\,H_z(y)f_{\boldsymbol t}(y).                    \tag{2}
\]
Testing (2) by a coefficient norm, rather than separate evaluations
at individual complex colors, is what controls joint profiles.

As in the least-factor deletion, split off the true
\(\mathcal G_J(N)\) from the \(\Lambda(y)\) atom.
Since every true \(y\) prime in \(J\) exceeds \(Y_0\), that
atom is the unchanged constant \(\mathcal G_J(N)\) and
proper powers cost \(O(x^{1/2}L^{O(1)})\) also in norm.
The two remaining terms have actual short \(z\)-rough
factor \(b\le1.5R_-\) and free variable \(a=y/b\).
For the raw term \(b=r\), while for the free term \(b=cs\)
with its coefficient \(\mu_2(c)\log s\).
The color factors exactly as \(f(a)f(b)\).
Replace \(f(a)\) by \(\prod_{p\in\mathcal E,p\mid a}t_p\).
The difference is bounded by 2 in norm and is supported
on a squareful \(z\)-rough \(y\).
By Cauchy--Schwarz, fixed divisor moments and the
\(O(x/z)\) count for these squares, the replacement costs
\(O_A(xL^{-A})\) after the true prime and score weights.

For \(B=\lceil100\log\ell\rceil\), set
\[
 T_B(a)=\sum_{\substack{d\mid a,\ d\ {\rm squarefree}\\
                         p\mid d\Rightarrow p\in\mathcal E\\
                         \omega(d)\le B}}\prod_{p\mid d}(t_p-1).
\]
The coefficient-norm error in replacing the last color
product by \(T_B(a)\) is at most the corresponding
degree-\((B+1)\) sum with constant weights \(2^{B+1}\).
Indeed apply real Taylor's theorem with integral remainder
at \(u=1\) to
\(\prod_{p\mid a,p\in\mathcal E}[(1-u)+ut_p]\).
For \(0\le u\le1\) every undifferentiated factor has norm 1
and a differentiated factor has norm 2.
The factorial Taylor denominator gives exactly the stated
next elementary symmetric bound.

Open \(P^-(a)>z\) by the upper and lower fundamental lemma
of the least-factor deletion, now with support
\(d_z\le x^{\delta_x/4}\).
For the positive Taylor-error majorant use the upper sieve.
For the signed polynomial use the upper sieve and bound
its error by the difference of the two sieves times the
absolute coefficient envelope of \(T_B(a)\).
All its color divisors \(d\) of degree at most \(B+1\)
are \(\le Y_0^{B+1}\le x^{1.01\log\ell/\ell}\) for
large \(x\), and the actual prime moduli are
\[
      bdd_z\le 1.5 x^{1/2-(3-.75-1.01)\log\ell/\ell}.
\]
They lie in ordinary BV with arbitrary logarithmic slack.
The \(z\)-smooth \(d_z\) is disjoint from \(b,d\).
The latter two may share a prime; their complete modulus
is then \(bd\), not their lcm, since the divisor \(d\)
is imposed on \(a=y/b\).
For each modulus the number of reconstructions is
at most a fixed divisor power, as are the coefficient
multiplicities and \(2^{\omega(d)}\).
The endpoint and logarithm variation uses weighted prefix
BV just as in the original direct identity.
Discard the opposite primes dividing \(N\) at a negligible
fixed divisor-moment cost; the actual residue is then the
unit \(N\bmod bdd_z\).

In the analytic main one can replace
\(\varphi(bd)^{-1}\) by \((bd)^{-1}\) with relative
\(O(L/z)\) even when \(b,d\) share primes.
All omitted target primes in \(b,d\) exceed \(z\), so
the change on restoring them is negligible by the
absolute harmonic Euler bounds.
All \(d_z\)-local factors remain exact:
the bracket's main is \(V_N(z)\) with its customary factor
\(\mathfrak S(N)V_z(1+O(L/z))\), and its discrepancy
in the difference of the two sieve models is
\(O(s_z^{-s_z/2})\) relative, \(s_z\asymp\ell\log\ell\).
These operations also work for a positive error majorant;
no conditional independence of \(a\) and \(P\) is used.

The \((B+1)\)-fold harmonic Taylor error is bounded by
\[
 \frac{(\sum_{p\in\mathcal E}2/p)^{B+1}}{(B+1)!}
      \ll \ell^{-100};
\]
here \(\sum_{p\in\mathcal E}1/p\le\log\ell+O(1)\).
The signed coefficient envelope of the truncated product
costs at most \(\prod_{p\in\mathcal E}(1+2/p)\ll\ell^2\).
The absolute harmonic envelope of either original
prime-paired short model is \(O(x\mathfrak S(N)\ell^8)\)
as in the least-factor deletion, and the extra two powers
of \(\ell\) do not affect these error estimates.
Thus the transfer and both remainder bounds above incur
\(o(x\mathfrak S(N)/\ell)\) in coefficient norm.
The density from \(a\) is now the exact polynomial
\(V_N(z)\prod_{p\in\mathcal E}(1+(t_p-1)/p)\), to this
precision: the same Taylor estimate evaluates the omitted
degrees in the independent finite residue main itself.

Let \(V_{Y_0}=\prod_{p\le Y_0}(1-1/p)\) and set
\[
 \alpha_{\boldsymbol t}
   =V_{Y_0}\prod_{p\in\mathcal E}(1-t_p/p)^{-1}.
\]
In the actual paired models just obtained, the free-variable
density can be changed to
\(\mathfrak S(N)\alpha_{\boldsymbol t}\) at negligible
coefficient norm cost.
For a single \(p\in\mathcal E\), the ratio error compared
with the old \(1-1/p\) factor is exactly
\[
 \frac{(1+(t_p-1)/p)(1-t_p/p)}{1-1/p}-1
                 =-\frac{t_p(t_p-1)}{p^2(1-1/p)} .
\]
Its norm is \(O(p^{-2})\).
The target-prime corrections contribute \(O(L/z)\) as noted,
and all products have the polylogarithmic harmonic envelope
already used. This proves the required local law on actual
prime APs at the stated norm level.

## 2. Exact colored convolution and its normalized moments

Put \(\sigma=\log Y_0/L=.01/\ell\) and \(u_p=\log p/L\).
Define \(Z_{\boldsymbol t}(w)=\prod_{p>z}
(1-f_{\boldsymbol t}(p)p^{-w})^{-1}\) for \(\Re w>1\).
Because every color prime is below the actual \(C_y\),
the exact Dirichlet series for the short free coefficient is
\[
 -Z_{\boldsymbol t}'(w)
       \prod_{z<p<C_y}(1-f_{\boldsymbol t}(p)p^{-w})^2
  =\zeta_{\ge C_y}(w)^2\,(Z_{\boldsymbol t}^{-1})'(w).
                                                                  \tag{3}
\]
This is just multiplicativity, retaining repeated factors
in the exact harmonic model even though squareful physical
rows were negligible. The raw short coefficient has series
\(Z_{\boldsymbol t}^{-1}\).

For clarity introduce the finite normalized signed measure,
with coefficients in the same normed algebra,
\[
 \nu_{\boldsymbol t}
   =\left(\prod_{p\in\mathcal E}(1-t_p/p)^{-1}\right)
      \sum_{\substack{d\ {\rm squarefree}\\p\mid d\Rightarrow
                                             p\in\mathcal E}}
            \frac{\mu(d)f_{\boldsymbol t}(d)}{d}
                 \delta_{\log d/L}.
\]
Its total mass is the constant 1.
The following uniform bounds distinguish its signed moments
from its absolute variation:
\[
 \int e^{u/\sigma}\,|d\nu_{\boldsymbol t}|_1\ll \ell^2,\qquad
 \left\|\int u^j\,d\nu_{\boldsymbol t}\right\|_1
                                  \ll_j \sigma^j \quad(j\ge0).
                                                                  \tag{4}
\]
For the first inequality bound the product of absolute factors
by
\[
 \prod_{p\in\mathcal E}\frac{1+1/p}{1-1/p}\,
      \exp\left(O\left(\sum_{p\in\mathcal E}
                          (e^{u_p/\sigma}-1)/p\right)\right).
\]
The first product is \(O(\ell^2)\), and the sum in the
exponent is \(O(1)\) by
\(\sum_{p\le Y_0}\log p/p\ll\log Y_0\).
For the signed moments use the generating function
\[
       \int e^{vu}\,d\nu_{\boldsymbol t}
            =\prod_{p\in\mathcal E}
                       \frac{1-t_p e^{v u_p}/p}{1-t_p/p}.
\]
For \(|v|\le1/\sigma\), each factor differs from 1
by norm at most \(|e^{v u_p}-1|/(p-1)\);
their sum is \(O(1)\) by the same prime harmonic log bound.
The product is bounded in norm, so coefficientwise Cauchy
integration gives the second inequality of (4).
No estimate of a single Fourier evaluation is used instead
of a coefficient sum.

Let \(M_0\) be the signed Stieltjes measure \(d\rho\) on
\([0,\infty)\), pushed forward by \(t\mapsto\sigma t\);
include the atom \(1\) at \(0\), with \(\rho=0\) on the
negative axis.
Let \(M_1\) be similarly the positive measure
\(-e^{-\gamma}t\,d\rho(t)\) pushed forward by the same map.
Thus \(M_0\) has mass 0 and \(M_1\) has mass 1.
Both have bounded absolute exponential moments at
\(1/\sigma\), by the factorial Dickman bound.
By the uniform reciprocal-prime convolution of the
least-factor deletion, the harmonic measure of
\(Y_0\)-rough \(\mu\) converges to \(M_0\) in its prefix
sums up to \(u=1\), and its \(-\mu\log\) measure
times \(V_{Y_0}\) converges to \(M_1\).
For these approximations the uniform prefix discrepancies
are \(\ll \ell^{O(1)}e^{-c\sqrt{\log Y_0}}\), including
prefix partial summation and quantitative Mertens.
The normalization \(V_{Y_0}\log Y_0=e^{-\gamma}
+O(e^{-c\sqrt{\log Y_0}})\) is used here.

By (3) and the exact separation of the finite-colored
factor, the normalized \(-\mu f_{\boldsymbol t}\log\)
harmonic kernel occurring in the free main is, to
negligible coefficient norm error against bounded
variation tests of fixed norm,
\[
 K_{\boldsymbol t}
     =M_1*\nu_{\boldsymbol t}
       -\frac{e^{-\gamma}}{\sigma}\,
                  M_0*(u\,\nu_{\boldsymbol t}).               \tag{5}
\]
Here the second term is precisely the contribution of
the logarithm of the finite-bank part, not discarded.
To justify the approximation, replace the \(Y_0\)-rough
prefix measures at each fixed bank exponent using the
uniform discrepancies just stated, and integrate against
the translated bounded-variation test by partial summation.
The remaining total variations are bounded by (4),
also for \(u\,\nu_{\boldsymbol t}/\sigma\).
The support actually queried in the finite sum is
\(u\le1\); extending the limiting measures to infinity
is harmless in (5), and their exponential tail pays for
any subsequent tail at a fixed positive exponent.

From the masses of \(M_0,M_1\) and (4), the kernel (5)
has exact mass 1, and each signed moment of order \(j\)
in coefficient norm is \(O_j(\sigma^j)\).
Indeed the signed \(i\)-th moments of \(M_0,M_1\) are
\(O_i(\sigma^i)\), while \(u\,\nu_{\boldsymbol t}\)
has its \(j\)-th signed moment \(O_j(\sigma^{j+1})\).
Its absolute fourth moment is
\(O(\ell^2\sigma^4)\), by the absolute exponential
moment in (4) and the corresponding bounds for
\(M_0,M_1\). The same exponential estimate gives
an exponentially small coefficient tail for \(u\)
above any fixed positive exponent.

In the raw short model the nonlogarithmic harmonic
factor is \(V_{Y_0}(M_0*\nu_{\boldsymbol t})\), and
it is multiplied by \(\log y\).
That convolution has exactly zero mass.
The other, logarithmic, term is \(K_{\boldsymbol t}\)
with mass 1.
The cutoff at \(u=1/2-\delta_x\) therefore changes
the first mass 0 and second mass 1 by exponentially
small amounts in coefficient norm, by the cited
tail estimates, even after the additional factor
\(V_{Y_0}\log y=O(1/\sigma)\).
So the raw principal is the constant
\(|J|\mathfrak S(N)+o(x\mathfrak S(N)/\ell)\);
it is subtracted from the real prime atom.

## 3. The free main and extraction of all label patterns

The outer positive harmonic measure from
\(\zeta_{\ge C_y}^2\) in (3) has cumulative
\(Q_\epsilon\) on the exponent scale, as in the
many-small renormalization.
Here the prefix error on the fixed compact interval
is \(O_\epsilon(L^{-1})\) (and one can use ordinary
quantitative PNT at the fixed lower exponent).
This follows by finite reciprocal-prime convolution:
the actual \(C_y\) changes \(\epsilon\) by \(O(1/L)\),
removing that width costs \(O_\epsilon(1/L)\);
prime powers affect the positive harmonic measure
by \(O_\epsilon(x^{-\epsilon})\).
Multiplying by the polylogarithmic variations in
(5) still costs \(o_\epsilon(1/\ell)\).

Thus, at the physical point \(y\), the normalized
colored free mean is the action of \(K_{\boldsymbol t}\)
on \(F_y(u)=Q_\epsilon(v_y-u)\), extended by zero for
\(u>v_y\), where \(v_y=\log(y/R_+)/L\).
This function is uniformly bounded and is \(C^4\) in a
fixed neighborhood of \(u=0\) for fixed \(\epsilon\).
One way to check the only possible transitions:
the \(j\)-prime convolution term in \(Q_\epsilon\)
starts at \(j\epsilon\) with a zero of order \(j\),
by shifting each variable down by \(\epsilon\) and
integrating over the resulting simplex. Since \(v_y\)
is near \(1/2\), any nearby starting transition has
\(j>4\), and there are only finitely many \(j\).
If the extension has a jump at \(u=v_y\) from the
zero-prime atom, this is bounded away from zero
and does not affect the Taylor estimate below.

The cubic Taylor polynomial about \(u=0\) approximates
\(F_y(u)\) with \(O_\epsilon(u^4)\) error for all
\(u\ge0\): near zero use the fourth derivative,
and away from zero use boundedness of \(F_y\)
and the fixed polynomial.
The signed moments and absolute fourth moment of (5)
now give
\[
 \left\|\int F_y(u)\,dK_{\boldsymbol t}(u)-Q_\epsilon(v_y)\right\|_1
      \ll_\epsilon \sigma+\ell^2\sigma^4 \ll_\epsilon \ell^{-1}.
\]
This is an estimate for all coefficients jointly.
Integrating over \(y\in J\), respecting the actual
\(y/R_+\) cutoff and its interval endpoints, the result
for (2) is
\[
 \left\|\mathcal D(\boldsymbol t) -
  \left[\mathcal G_J(N)+\mathfrak S(N)
                 \int_J (Q_\epsilon(v_y)-1)\,dy\right]\right\|_1
      \ll_{\epsilon,J_0}\frac{x\mathfrak S(N)}{\ell}.          \tag{6}
\]
The bracket is independent of every label variable.
Keeping \(v_y\) rather than replacing it by \(1/2\) matters
for the displayed small error, though not for the
nonconstant coefficients.

Drop squareful \(y\), with the same negligible
coefficient norm cost used in Section 1.
A nonconstant monomial of the resulting (2) has exactly
the coefficient for its entire actual profile \(T\).
Taking the sum of absolute nonconstant coefficients in
(6) proves (1).
Finally, in every nonempty profile, the \(k=0\) sector
is absent and the \(k=1,2\) sector has
\(o_\epsilon(x\mathfrak S(N))\) combined absolute row
mass by Section 3 of the least-factor deletion (use
\(Y_0\le Y\)), including the bounded-rank gap transfer.
Subtracting these actual rows in the same coefficient
norm proves the assertion for \(k\ge3\).
This leaves the empty-profile genuine score, including
its pointwise comparison with calibration, unresolved.
