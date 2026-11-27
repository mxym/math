# Two interacting smoothing profiles on random binary quotient tori

**Scope.** Gaussian noise on an abstract quotient of a cubic torus.
We compute its total variation from uniform and its pointwise flatness
in two different critical windows, with limits in probability over the
random quotient. No hidden variables, keys, ciphertexts, computational
reduction, or implementation is in the model. These random lattices are
generally not cyclotomic ideal lattices.

[Dadush–Regev, §7](https://arxiv.org/pdf/1606.06913) discusses
Saloff-Coste's general comparison of \(L^1\) and \(L^\infty\) mixing on
flat tori. [Debris-Alazard–Ducas–Resch–Tillich](https://arxiv.org/abs/2205.10552)
develop general smoothing bounds for codes and lattices. The binary part
below uses the information density familiar from channel resolvability
(see [Watanabe–Hayashi](https://arxiv.org/abs/1404.5507) and
[Cuff](https://arxiv.org/abs/1605.06396)). What is calculated here is a
joint critical limit for a **vanishing-signal linear-code ensemble**:
even Fourier modes produce a surviving lognormal density at the same
time that odd modes produce a loss of typical density. Comparing total
variation only to the fully sign-averaged output, or summing two
total-variation bounds, would not yield the combined profile.

## 1. Model and statements

Let \(G\) be a uniform binary \(n\times r\) matrix with independent entries,
\(C=\operatorname{im}G\le\mathbb F_2^n\), and
\(\Lambda_C=\mathbb Z^n+\tfrac12 C\) (with any binary representatives).
Modulo \(\mathbb Z^n\) this lattice is the subgroup of half-shifts indexed by
\(C\). The uniform choice of a column source \(b\in\mathbb F_2^r\) yields
a uniform element \(Gb\) of \(C\) even if \(G\) is not injective.

Use independent centered continuous real Gaussian coordinates with widths
\(s_i\), so coordinate \(i\) has variance \(s_i^2/(2\pi)\). Put
\(a_i=e^{-\pi s_i^2}\). For \(0<a<1\) define the circle densities and
quotient ratio
\[
 f_a(y)=\sum_{j\in\mathbb Z} a^{j^2}e^{2\pi ijy},\qquad
 g_a(y)=\tfrac12(f_a(y)+f_a(y+1/2)),\qquad
 R_a(y)=\frac{f_a(y)-f_a(y+1/2)}{f_a(y)+f_a(y+1/2)} .
\]
The first is the Gaussian periodized on the unit circle by Poisson.
Define
\[
 d(x)=\tfrac12(1+x)\log(1+x)+\tfrac12(1-x)\log(1-x),\qquad
 I(a)=\int_0^1 d(R_a(y))\,dy .
\]
The logarithms in \(I(a)\) are natural. Write \(U_C\) for Haar on
\(\mathbb R^n/\Lambda_C\), and \(P_C\) for the Gaussian there.

**Total variation.** Assume \(\max_i a_i\to0\),
\(J=\sum_i a_i^2\to\infty\), \(\sum_i a_i^8\to\lambda\in[0,\infty)\),
and \(r\to\infty\). If
\[
     \frac{r\log2-\sum_i I(a_i)}{\sqrt{2J}}\longrightarrow
            u\in[-\infty,\infty],
     \qquad q=\Phi(u),
\]
then, in probability over \(G\),
\[
 \boxed{\quad d_{\rm TV}(P_C,U_C)
      \ \longrightarrow\
      1-\mathbb E\min\{q\,e^{-\lambda+\sqrt{2\lambda}Z},\,1\},
      \qquad Z\sim N(0,1).\quad}
 \tag{1}
\]
For \(\lambda=0\) this is \(1-q\). For \(q=1\) this is the usual
one-dimensional lognormal-likelihood TV profile
\(2\Phi(\sqrt{\lambda/2})-1\). If \(\lambda>0,\ q>0\), it equals
\(\Phi(h)-q\Phi(h-\sqrt{2\lambda})\) for
\(h=(\lambda-\log q)/\sqrt{2\lambda}\).
In particular an intermediate sign-averaging error does not simply add
to the even-mode TV. In the spherical case \(a_i=a\),
\(I(a)=a^2+a^4/2+O(a^6)\). If \(n a^8\) is bounded then the fourth
power term can affect the center by more than the window width,
whereas the \(O(n a^6)\) remainder is \(o(\sqrt{n a^2})\).

**Pointwise flatness.** Set
\[
  E_i=\sum_{j\ {\rm even}}a_i^{j^2},\quad
  O_i=\sum_{j\ {\rm odd}}a_i^{j^2},\quad x_i=O_i/E_i .
\]
Assume \(\max_i a_i\to0\), \(\sum_i a_i\to\infty\),
and \(\sum_i a_i^4\to\lambda_\infty\in[0,\infty)\).
If
\[
       c_n=r\log 2-\sum_i\log(1+x_i)\longrightarrow
                         c\in[-\infty,\infty],
\]
then the maximum of the absolute density deviation from Haar converges
in probability to
\[
      \boxed{\qquad e^{2\lambda_\infty}(1+e^{-c})-1.\qquad}
 \tag{2}
\]
Use \(e^{-c}=0\) at \(c=+\infty\), and interpret \(c=-\infty\)
as divergence to infinity. There is no normal window in (2).

For example, suppose the widths are spherical and
\(r\log2/n^{3/4}\to\kappa\in(0,\infty)\).
At the TV sign boundary, \(a\sim\sqrt\kappa\,n^{-1/8}\), so
\(\lambda=\kappa^4\). At the pointwise sign boundary,
\(a\sim(\kappa/2)n^{-1/4}\), so \(\lambda_\infty=\kappa^4/16\).
These are the scales at which both mechanisms survive. The corresponding
widths have asymptotic ratio \(\sqrt{2}\) (the squared-width ratio is
2); the error curves and the transition-window sizes are different.
No universal claim over other tori is made.

## 2. Lift to the unit cube and condition on the circle observation

Both TV and the maximum absolute density deviation on the quotient
can be computed on the unit cube with Haar \(U\), using the lifted
density
\[
   Q_G(y)=2^{-r}\sum_{b\in\mathbb F_2^r}
             \prod_{i=1}^n f_{a_i}\big(y_i+(Gb)_i/2\big).
 \tag{3}
\]
Indeed this is invariant by all the code half-shifts; integrating it
against a test that is invariant under those shifts is the same as
integrating the original wrapped Gaussian. Haar pushes to Haar.
The invariance also gives equality of the two norms just stated.

Write \(B(y)=\prod_i g_{a_i}(y_i)\) for the density obtained by
averaging over *all* half-shifts. Fix \(y\), let \(z\) be uniform in
\(\mathbb F_2^n\), and put
\[
 W_z(y)=\prod_i(1+(-1)^{z_i}R_{a_i}(y_i)),\qquad
 \mathbb E_z W_z(y)=1.
\]
Equation (3) says \(Q_G(y)/B(y)=2^{-r}\sum_b W_{Gb}(y)\).
The reweighted distribution of \(z\), with probabilities \(2^{-n}W_z(y)\),
is a product of binary signs with probabilities
\((1\pm R_{a_i}(y_i))/2\). Under that distribution, the information
\(\log W_z(y)\) is a sum of independent terms. The one-coordinate
mean is \(d(R_{a_i})\) and variance is
\[
 v(R_{a_i}),\qquad v(x)=\frac{1-x^2}{4}
                   \log^2\!\left(\frac{1+x}{1-x}\right).
\]
For \(a\) small,
\(R_a(y)=2a\cos(2\pi y)+O(a^5)\) uniformly in \(y\):
the next odd harmonic is order \(a^9\) and the even denominator
differs from 1 by \(O(a^4)\). Taylor expansion gives
\(d(x)=x^2/2+x^4/12+O(x^6)\) and \(v(x)=x^2+O(x^4)\).
Since the second and fourth circle moments of cosine are \(1/2,3/8\),
these prove \(I(a)=a^2+a^4/2+O(a^6)\) and
\(\int_0^1 v(R_a(y))\,dy=2a^2+O(a^4)\).

When \(y\) itself is sampled from cube Haar, the coordinates are
independent. The conditional mean \(\sum_i d(R_{a_i}(y_i))\)
differs from \(\sum_i I(a_i)\) by \(o_{\mathbb P}(\sqrt J)\):
the variance is \(O(\sum a_i^4)=o(J)\). The conditional variance
of the information is \(2J(1+o_{\mathbb P}(1))\), since its mean is
\(2J+O(\sum a_i^4)\) and its variance is \(O(\sum a_i^4)=o(J^2)\).
On events where it is at least \(J\), the conditional Berry–Esseen
bound is \(C\sum_i a_i^3/J^{3/2}=o(1)\); this uses bounded third
absolute central moment \(O(a_i^3)\) for each sign term.
It follows, with \(L\to\infty\) chosen so \(L=o(\sqrt J)\),
that the posterior mass of
\(\log W_z(y)\le r\log2-L\) converges in Haar probability to \(q\),
and the posterior mass of
\(r\log2-L<\log W_z(y)\le r\log2+L\) converges to zero.
This argument also covers \(u=\pm\infty\).

## 3. Typical code-averaged density and the TV profile

For every fixed \(y\), distinct nonzero sources \(b\) give
pairwise independent uniform vectors \(Gb\) as \(G\) varies.
Over \(\mathbb F_2\) any two distinct nonzero sources are linearly
independent, and each row of \(G\) produces a uniform pair of bits.
This is pairwise independence, not independence of the whole codebook.

Put \(M=2^r\). The low part of the sum \(M^{-1}\sum_{b\ne0} W_{Gb}\),
truncated at \(M e^{-L}\), has conditional expectation \((1-1/M)\)
times the low posterior mass of §2 and conditional variance at most
\[
    M^{-1}\mathbb E_z[W_z(y)^2\,1_{\{W_z(y)\le M e^{-L}\}}]
        \le e^{-L}.
\]
The middle part has expectation given \(y\) at most its posterior
mass, which tends to zero also in expectation over Haar because
it is bounded by 1. By a union bound and the first moment,
the chance that any nonzero-source term is above \(M e^L\) is
at most \(M\Pr_z(W_z(y)>M e^L)\le e^{-L}\), uniformly in \(y\).
The zero-source term is negligible in joint Haar and matrix
probability: \(R_a(y+1/2)=-R_a(y)\) implies
\(\mathbb E_U W_0(y)=1\), so its expected weight is \(1/M=o(1)\).
Combining these four parts gives
\[
                 Q_G(y)/B(y)\ \longrightarrow q
             \quad\text{in joint matrix and Haar probability}.
 \tag{4}
\]
There is no assertion of \(L^1\) convergence of this ratio to \(q<1\).

The independent factors of \(B\) have
\(g_a(y)=1+2a^4\cos(4\pi y)+O(a^{16})\).
Under Haar the mean of \(\log g_a\) is \(-a^8+O(a^{12})\), and its
variance is \(2a^8+O(a^{12})\), by expanding the logarithm around
1 with \(\int_0^1(g_a-1)=0\). The third central moments in absolute
value are \(O(a^{12})\). Since
\(\sum_i a_i^{12}\le (\max_i a_i)^4\sum_i a_i^8=o(1)\),
\(\log B\Rightarrow N(-\lambda,2\lambda)\) by the triangular array
CLT, or converges in probability to 0 when \(\lambda=0\).
In particular \(B\) is tight under Haar. By (4),
\(\min(Q_G,1)-\min(qB,1)\to0\) in joint probability; it is bounded,
so it also tends to zero in mean absolute value. Conditional averaging
over \(y\) then converges in probability over \(G\).
Finally for any density \(Q\) with respect to Haar,
\(d_{\rm TV}(Q,U)=1-\mathbb E_U\min(Q,1)\).
Apply this and integrate the limiting normal likelihood to obtain (1).
This use of the bounded overlap, rather than the first moment of a
limiting subprobability density, accounts for the mass on rare points
when \(q<1\).

## 4. Pointwise flatness

The Fourier coefficients of \(Q_G\) are the original nonnegative
Gaussian coefficients retained on
\(\Lambda_C^*=\{j\in\mathbb Z^n:j\bmod2\in C^\perp\}\).
Therefore the maximum absolute deviation is exactly \(Q_G(0)-1\).
Summing first within each parity pattern gives
\[
 Q_G(0)=\Big(\prod_i E_i\Big)(1+Y_G),\qquad
 Y_G=\sum_{\substack{z\in\mathbb F_2^n\\z\ne0}}
       1_{\{G^\mathsf T z=0\}}\prod_i x_i^{z_i}.
\]
For every nonzero \(z\), the indicator has expectation \(2^{-r}\);
the indicators for distinct nonzero \(z\)'s are pairwise independent,
by applying the same binary linear independence argument to the
columns of \(G\). Hence
\[
 \mathbb E Y_G=2^{-r}\left(\prod_i(1+x_i)-1\right),\qquad
 \operatorname{Var}Y_G\le 2^{-r}\prod_i(1+x_i^2).
\]
We have \(x_i=2a_i+O(a_i^5)\) and
\(\sum_i\log E_i=2\sum_i a_i^4+o(1)\).
Let \(S=\sum_i\log(1+x_i)\). Then \(S\sim 2\sum_i a_i\to\infty\),
and \(\sum_i\log(1+x_i^2)=O(\sum_i a_i^2)=o(S)\).
At finite \(c\), \(\mathbb E Y_G\to e^{-c}\) and
\(\operatorname{Var}Y_G\to0\). At \(c=+\infty\) Markov suffices;
at \(c=-\infty\) the mean diverges and the variance divided by the
square of the mean is at most
\((1+o(1))\exp(r\log2-2S+o(S))\to0\).
This proves (2). For spherical \(a\) at this boundary with \(na^4\)
bounded, \(n\log(1+x_i)=n\log(1+2a)+o(1)\); replacing the logarithm
only by \(2a\) would in general shift this window by a diverging amount.

**Replay.** Run `node verify-binary-quotient-smoothing-windows.js`.
It checks exact generated \( \mathbb F_2 \) pairwise counts and
small quotient identities, along with Fourier, posterior and limiting
profile normalizations. The asymptotic limits are analytic.
