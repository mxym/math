# The unavoidable error of appending Gaussian torus responses

An observation cannot generally be treated as a source of more
independent observations with exactly the same hidden location if the
actual observation must remain in the released data. This note calculates
an exact asymptotic total-variation obstruction for a product wrapped
Gaussian location experiment. The kernel used to define the optimum can
have unlimited computation. The result does not treat ordinary
Ring-LWE with fresh public coefficients, give a way to recover a hidden
location, or rule out transformations that replace the original
observations.

## 1. Model and theorem

Fix \(q\ge2\). Write \(H_d=(\mathbb Z/q)^d\) and
\[
 f_b(t)=\sum_{k\in\mathbb Z} b^{k^2}e^{2\pi i k t}
      \quad(0<b<1,\ t\in\mathbb T=\mathbb R/\mathbb Z).
\]
For \(s\in H_d\), let \(P_{s,b}\) have density
\(\prod_{i=1}^d f_b(x_i-s_i/q)\) on \(\mathbb T^d\).
The observed, labeled prefix consists of \(m=m_d\) rows
of \(P_{s,b}\). The intended continuation consists of \(r=r_d\ge1\)
new rows of \(P_{s,a}\), independent of the prefix at each fixed \(s\);
\(a=a_d\) can equal \(b=b_d\) or differ. A candidate kernel \(K\)
takes the prefix \(x\) and generates only the continuation. The prefix
in its labeled positions must be left unchanged, and the kernel
does not know \(s\). Define
\[
 {\cal R}_d=
 \inf_K\ \sup_{s\in H_d}\operatorname{TV}\bigl(
      P_{s,b}^{\otimes m}(dx)K_x(dy),\
      P_{s,b}^{\otimes m}(dx)P_{s,a}^{\otimes r}(dy)\bigr).
 \tag{1}
\]
No finite-code or time constraint is imposed on \(K\).

Let \(e_j=(\cos(2\pi j/q),\sin(2\pi j/q))\) and define
\(J_q(\alpha)\) for finite \(\alpha\ge0\) in a two-dimensional
Gaussian experiment. Let \(B\) be uniform on \(\mathbb Z/q\),
\(N\sim N(0,I_2)\) independent, and
\(T=\sqrt{2\alpha}\,e_B+N\). Put
\[
 J_q(\alpha)=\mathbb E\bigl\|\mathbb E[e_B\mid T]\bigr\|^2,\qquad
 J_q(\infty)=1.
 \tag{2}
\]
The posterior in (2) has weights proportional to
\(\exp(\sqrt{2\alpha}\,T\cdot e_j)\). In particular
\(J_q(0)=0\) and \(J_q(\alpha)<1\) for any finite \(\alpha\).

**Theorem.** Suppose \(d\to\infty,\ b_d\to0,\ a_d\to0\),
\(m_d b_d^2\to\alpha\in[0,\infty]\) and
\(d r_d a_d^2\to\gamma\in[0,\infty]\).
If \(\gamma<\infty\), then
\[
 {\cal R}_d\longrightarrow
     2\Phi\left(\sqrt{\gamma(1-J_q(\alpha))/2}\right)-1 .
 \tag{3}
\]
If \(\gamma=\infty\) and \(\alpha<\infty\), then
\({\cal R}_d\to1\). No claim is made at
\((\gamma,\alpha)=(\infty,\infty)\).
A posterior-predictive kernel attains (3) asymptotically as a
statistical comparison, but no implementation of such a kernel
is required by the obstruction.

## 2. Reduction to an overlap optimum

Use the uniform prior on \(H_d\). Let \(\pi_x\) be the posterior
of \(s\) from the prefix and \(\bar P_x=\int P_{s,a}^{\otimes r}\,d\pi_x(s)\)
its predictive law. Put \(\nu(dx,dy)=P_X(dx)\bar P_x(dy)\),
where \(P_X\) is the prior mixture of prefix laws. The random variable
\[
 L(s,x,y)=\frac{dP_{s,a}^{\otimes r}}{d\bar P_x}(y)
\]
is positive, and \(\mathbb E_{\pi_x}L(s,x,y)=1\) for every
\((x,y)\). For any kernel \(K\), let \(\kappa(x,y)\) be the
density of the absolutely continuous part of
\(P_X(dx)K_x(dy)\) with respect to \(\nu\). Then
\(\kappa\ge0\) and \(\int\kappa\,d\nu\le1\).
The Bayes TV risk under the uniform prior is exactly
\[
 1-\int \mathbb E_{\pi_x}\min(L(s,x,y),\kappa(x,y))\,d\nu(x,y).
 \tag{4}
\]
Indeed, adding the finite hidden index \(s\) to the observed pair
in both laws converts the joint TV into the average TV for fixed
\(s\). Under the reference joint law
\(\nu(dx,dy)\pi_x(ds)\), the target likelihood is \(L\), and
the absolutely continuous part of the kernel's joint likelihood
is \(\kappa\), independent of \(s\) given \(x,y\).
Any remaining singular component has zero overlap with the target,
which proves (4).

The worst-case risk is at least the uniform Bayes risk.
Conversely, the posterior-predictive kernel \(x\mapsto\bar P_x\)
is equivariant for the \(H_d\) translations of all rows, so
its risk is constant over \(s\) and equals its Bayes risk.
This will suffice for the matching bound.

## 3. What the prefix tells a single coordinate

For one coordinate write \(B\) for the uniform hidden label,
\(U\) for its prefix and \(\pi_U\) for its posterior.
The expansion
\[
 \log f_b(v)
   =2b\cos(2\pi v)-b^2-b^2\cos(4\pi v)+O(b^3)
 \tag{5}
\]
is uniform in \(v\) as \(b\downarrow0\), by the Fourier series
and Taylor expansion. Under a fixed \(B=j\), a prefix observation
has first harmonic mean \(b e_j\) in real two-vector coordinates
and second harmonic mean of magnitude \(b^4\).
For \(m b^2\) bounded, the sum of the second harmonic multiplied
by \(b^2\) tends to zero in probability: its mean magnitude is at
most \(m b^6=o(1)\) and its variance is at most \(m b^4=o(1)\).
The accumulated remainder is \(O(m b^3)=o(1)\).
Consequently, uniformly in the finitely many proposed labels,
the prefix scores after dropping the common term \(-m b^2\)
are
\[
 2b\, e_j\cdot \sum_{\ell=1}^m
         (\cos(2\pi U_\ell),\sin(2\pi U_\ell))+o_{\mathbb P}(1).
 \tag{6}
\]

If \(m b^2\to\alpha>0\) finite, \(m\to\infty\). The
bounded triangular-array CLT shows that
\(\sqrt{2/m}\sum_\ell(\cos(2\pi U_\ell),\sin(2\pi U_\ell))\),
conditional on \(B=j\), converges to \(N(\sqrt{2\alpha}\,e_j,I_2)\):
each summand has covariance \(I_2/2+O(b^2)\).
Use (6), continuity of normalized exponential weights, and boundedness
to conclude
\[
 \mathbb E\left\|\sum_j\pi_U(j)e_j\right\|^2
      \longrightarrow J_q(\alpha).
 \tag{7}
\]
If \(\alpha=0\), the first term in (6) tends to zero by its mean
and variance bounds even if \(m\) stays finite; hence the posterior
becomes uniform and (7) still holds. This includes the empty prefix.

If \(m b^2\to\infty\), the Hellinger affinity between the prefix
laws for any two different fixed labels tends to zero. To see
a sufficient bound, the one-coordinate first-harmonic means
differ by \(b\|e_i-e_j\|\), so its two laws have TV at least half
that difference; with \(H^2=1-\mathrm{Aff}\) one has
\(\operatorname{TV}\le\sqrt2 H\). Thus the one-row affinity is
at most \(1-c_q b^2\), and affinities multiply over the prefix.
The expectation under the Bayes mixture of
\(\sqrt{\pi_U(i)\pi_U(j)}\) is exactly the affinity of the
two prefix laws divided by \(q\). Meanwhile
\[
 1-\left\|\sum_j\pi_U(j)e_j\right\|^2
   =\sum_{i,j}\pi_U(i)\pi_U(j)(1-e_i\cdot e_j).
\]
Bounding the off-diagonal terms by the corresponding posterior
square roots establishes (7) with \(J_q(\infty)=1\).
For finite \(\alpha\), all posterior weights in (2) are
strictly positive, so their convex combination of distinct unit
vectors has norm strictly less than one almost surely.

## 4. The conditional likelihood of the continuation

Assume for now that \(\gamma<\infty\). Write \(h=r a^2=O(1/d)\).
The prior, prefix likelihood, and continuation likelihood all
factor along the \(d\) coordinates. Under \(\nu(dx,dy)\) the
coordinate pairs \((x_i,y_i)\) are iid, with \(x_i\) a prefix
column and \(y_i\) a continuation column. Given \(x,y\), the
coordinates of \(s\sim\pi_x\) are independent with weights
\(\pi_i=\pi_{x_i}\).

Let \(Q_i=\sum_{\ell=1}^r(\cos(2\pi y_{i,\ell}),\sin(2\pi y_{i,\ell}))\).
For a single coordinate and label \(j\), apply (5) with \(a\)
to the log continuation density. After dropping its common
constant \(-r a^2\), it is
\[
 z_{i,j}=\lambda_{i,j}+u_{i,j},\qquad
 \lambda_{i,j}=2a\,e_j\cdot Q_i,\qquad
 |u_{i,j}|\le a^2\left|\sum_{\ell=1}^r e^{4\pi i y_{i,\ell}}\right|
                  +O(r a^3).
 \tag{8}
\]
For estimates under \(\nu\) one can first sample a latent label
from \(\pi_i\), then use the independent conditional observations
having first mean \(a e_j\) and second mean of magnitude \(a^4\).
Uniformly in this label, Hoeffding's inequality for the centered
coordinates of \(Q_i\) yields
\(\max_{i,j}|\lambda_{i,j}|\to0\) in probability: the drift is
\(O(h)\) per coordinate and the subgaussian scale is
\(O(\sqrt h)=O(d^{-1/2})\). Also
\(\sum_i\max_j|\lambda_{i,j}|^2=O_{\mathbb P}(1)\), since
\(\mathbb E[a^2\|Q_i\|^2]\le C(h+h^2)\).
For the error in (8),
\[
 \mathbb E_\nu\sum_i\max_j|u_{i,j}|^2
    =O\bigl(d(h a^2+h^2 a^8+h^2 a^2)\bigr)=o(1).
\]
The second harmonic has centered second moment bounded by \(r\)
and squared mean at most \(r^2 a^8\); multiplying by \(a^4\)
and adding \(O(r^2a^6)\) from the remainder gives the estimate.

Let the coordinate likelihood ratio given \(x_i,y_i\) be
\[
 1+\delta_{i,j}=\frac{e^{z_{i,j}}}{\sum_k\pi_i(k)e^{z_{i,k}}}.
\]
Its conditional mean under \(\pi_i\) is 1. Uniform Taylor expansion
when \(\|z_i\|_\infty\) is small gives
\(\delta_{i,j}=z_{i,j}-\sum_k\pi_i(k)z_{i,k}
                 +O(\|z_i\|_\infty^2)\).
The bounds above imply
\[
 \max_{i,j}|\delta_{i,j}|=o_{\mathbb P}(1),\qquad
 V_d:=\sum_i\mathbb E_{\pi_i}\delta_{i,j}^2
     =\sum_i 4a^2 Q_i^{\mathsf T}
               \operatorname{Cov}_{\pi_i}(e_j)Q_i+o_{\mathbb P}(1).
 \tag{9}
\]
Indeed the total squared error when replacing \(\delta_{i,j}\)
by the centered \(\lambda_{i,j}\) is bounded by
\(C\sum_i(\max_j|u_{i,j}|^2+\|z_i\|_\infty^4)=o_{\mathbb P}(1)\);
the fourth-power sum is bounded by the maximum squared size
times the tight sum of squares. Cauchy–Schwarz then gives (9).

Conditional on \(x_i\), the matrix
\(\mathbb E[Q_i Q_i^{\mathsf T}\mid x_i]\)
equals \(\tfrac r2 I_2+O(r a^2+r^2 a^2)\) in operator norm,
by the mean and covariance within each latent label.
Also \(\mathbb E[a^4\|Q_i\|^4]\le C(h^2+h^4)\) uniformly:
the centered sum of bounded independent two-vectors has fourth moment
\(O(r^2)\), and the drift is \(O(ra)\).
Since \(\operatorname{Cov}_{\pi_i}(e_j)\succeq0\) has trace
\(1-\|\sum_j\pi_i(j)e_j\|^2\le1\), each principal term in (9)
has mean
\[
 2h\,\mathbb E_{x_i}\left(1-\left\|\sum_j\pi_i(j)e_j\right\|^2\right)
       +O(h a^2+h^2)
\]
and variance \(O(h^2+h^4)\). The terms are independent under
\(\nu\). From (7) and \(dh\to\gamma\), their sum converges in
probability to
\[
 v=2\gamma(1-J_q(\alpha)).
 \tag{10}
\]

Conditional on \(x,y\), \(L=\prod_i(1+\delta_{i,s_i})\).
Because \(\mathbb E_{\pi_i}\delta_{i,j}=0\), (9)–(10)
and Taylor expansion of \(\log(1+\delta)\) show that the conditional
mean and variance of \(\log L\) tend in probability to
\(-v/2\) and \(v\), respectively. The cumulative third-order
error is bounded by the maximum \(|\delta|\) times \(V_d\).
The same maximum bound gives the Lindeberg condition for the
independent conditional summands; when \(v=0\), Chebyshev suffices.
In particular the conditional law of \(L\) converges in probability
to the law of \(L_\infty=e^{\sqrt v\,Z-v/2}\) with \(Z\sim N(0,1)\),
in Wasserstein-1 distance. One way to justify this last step is to
take an arbitrary subsequence, couple the varying reference laws on their product space, and
pass to a further subsequence on which all probability convergences
used in (9)–(10) hold almost surely. Apply the conditional CLT there. The exact conditional
second moment satisfies
\[
 \mathbb E_{\pi_x}L^2
      =\prod_i(1+\mathbb E_{\pi_i}\delta_{i,j}^2)\le e^{V_d},
\]
which is bounded on that further subsequence at almost every
\((x,y)\), giving uniform integrability. The
Wasserstein-1 distance is always at most \(2\), since both
laws are supported on \([0,\infty)\) and have mean \(1\).
Its \(\nu\)-expectation therefore tends to zero.

## 5. Sharp overlap limit and divergence of the critical scale

For any nonnegative \(k\), the function \(l\mapsto\min(l,k)\)
is 1-Lipschitz. Thus replacing the conditional \(L\) in (4) by
\(L_\infty\) changes the integrated overlap by \(o(1)\)
uniformly over all choices of \(\kappa\).
The function \(k\mapsto\mathbb E\min(L_\infty,k)\)
is concave and nondecreasing. By Jensen and
\(\int\kappa\,d\nu\le1\), no kernel has asymptotic overlap
exceeding \(\mathbb E\min(L_\infty,1)\).
The posterior-predictive kernel uses \(\kappa\equiv1\) and
attains this limit. Its worst-case and uniform risks agree
as in Section 2. Since
\[
 1-\mathbb E\min(L_\infty,1)
   =\tfrac12\mathbb E|L_\infty-1|
   =2\Phi(\sqrt v/2)-1,
\]
we obtain (3). The last identity follows by integrating the
exponentially tilted normal above the crossing \(Z=\sqrt v/2\);
it also holds at \(v=0\).

If \(\gamma=\infty,\ \alpha<\infty\), fix any finite \(G>0\).
Set \(r'=\lceil 2G/(d a^2)\rceil\) and
\(d'=\lfloor G/(r'a^2)\rfloor\). For large \(d\), \(1\le r'\le r\),
\(d'\le d/2\), \(d'\to\infty\) and \(d'r'a^2\to G\):
indeed \(r'a^2\le2G/d+a^2\to0\), and \(d r a^2\to\infty\).
Project the experiment to \(d'\) coordinates and \(r'\)
continuation rows. For a Bayes lower bound, use the product-uniform
prior; the omitted prefix coordinates are independent of the
retained hidden coordinates and their observed prefix. Any
kernel after projection and averaging those omitted coordinates
is a valid kernel for the smaller experiment. Marginalization
cannot increase TV, including when averaging the hidden labels.
The original worst-case risk is therefore at least the limiting
uniform Bayes lower bound from (3) at \(\gamma=G\).
Since \(1-J_q(\alpha)>0\), taking \(G\to\infty\) gives limit 1.

## 6. Scope and comparison

[Axelrod–Garg–Sharan–Valiant, §§1 and 4](https://proceedings.mlr.press/v119/axelrod20a.html)
already identify the distinction between retaining and changing
the actual observations in Gaussian sample amplification.
[Axelrod–Garg–Han–Sharan–Valiant](https://arxiv.org/abs/2201.04315)
develop the general Le Cam comparison approach. Here we impose
a **labeled, unchanged prefix**, allow distinct prefix and
continuation widths, and give the exact minimax profile in
the stated product circle experiment. There is no claim
about unmarked original observations mixed among the others.
[Genise–Micciancio–Peikert–Walter, §5](https://web.eecs.umich.edu/~cpeikert/pubs/gaussians.pdf)
give an LWE sample-generation self-reduction with randomized
public rows and larger discrete Gaussian error. The theorem
above concerns a different experiment and does not contradict
that self-reduction.

For a dyadic cyclotomic codifferent torus, in orthogonal
coefficient coordinates this is the formal continuous spherical
model for **repeated observations at a fixed known unit
coefficient**, with the unit incorporated into the unknown grid
label. Standard [Ring-LWE, Definition 3.1](https://web.eecs.umich.edu/~cpeikert/pubs/ideal-lwe.pdf)
has independently uniform coefficients instead; a batch of
different coefficient actions does not have the posterior
product used here. Neither unrestricted Gaussian experiments,
discrete noise, deployed parameters, nor a complexity
classification follow. The companion checker confirms
finite arithmetic and overlap identities on synthetic data,
not the asymptotic probability analysis.
