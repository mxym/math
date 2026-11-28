# An information bottleneck for compressed Gaussian torus responses

This note bounds the information in single-response encodings that are
chosen nonadaptively across rows. In the broad-noise regime the exact
asymptotic retention curve depends on the number of stored bits per
coordinate, even if arbitrary joint quantization of coordinates within
each response is allowed. The result is an information bound for a specified
data interface. It contains no hidden-label solver, no efficiency claim
for the encoders in the sharpness argument, and no assessment of an
actual cryptographic scheme.

## 1. Statement

Let \(q\ge3\) be an integer, \(X\) uniform on
\((\mathbb Z/q)^d\), and \(Y=X/q+E\bmod\mathbb Z^d\), where the coordinates
of \(E\) have independent circle densities
\[
 f_b(t)=\sum_{k\in\mathbb Z}b^{k^2}e^{2\pi i k t},\qquad 0<b<1.
\]
Each coordinate is a wrapped centered real Gaussian. Small \(b\)
means broad unwrapped noise. The marginal law of \(Y\) is \(Q_b^{\otimes d}\);
\(Q_b\) is the circle law with density
\(g_b(y)=f_{b^{q^2}}(qy)\) relative to Haar.
All entropy quantities use natural logarithms.

For \(t\ge0\) put
\[
 Z(t)=\int_{\mathbb T} e^{t\cos(2\pi y)}\,dy,\qquad
 A(t)=\frac{Z'(t)}{Z(t)},\qquad
 R(t)=t A(t)-\log Z(t).
\]
Define \(\mathcal F\) by \(\mathcal F(R(t))=A(t)^2\) and
\(\mathcal F(\infty)=1\). This gives a continuous, strictly increasing
concave function on \([0,\infty)\) with
\(\mathcal F(0)=0,\ \mathcal F(r)\sim r\) at zero and
\(\mathcal F(r)\to1\) at infinity.

**Theorem.** There are absolute constants \(b_0>0,C>0\) such that for
all \(d,q\), all \(0<b\le b_0\), and all Markov chains
\(X\to Y\to V\) with this fixed law of \((X,Y)\) and with \(V\) on a
standard Borel space,
\[
 I(X;V)\le (1+Cb)d b^2\,\mathcal F\bigl(I(Y;V)/d\bigr).
 \tag{1}
\]
For an output with at most \(M\) labels this implies the uniform upper
bound obtained by replacing \(I(Y;V)\) by \(\log M\).

Moreover, as \(d\to\infty\), for arbitrary sequences \(q=q_d\ge3\),
\(b=b_d\to0\), and integers \(M=M_d\) with \(\log M_d\to\infty\),
\[
 \sup_{|\mathrm{range}(V)|\le M_d} I(X;V)
   =(1+o(1))d b_d^2\,\mathcal F\bigl((\log M_d)/d\bigr).
 \tag{2}
\]
The supremum includes randomized encoders; the lower bound in (2) is
already attained asymptotically by some deterministic encoders, without
a computational constraint. In particular, if \(1\ll\log M_d\ll d\),
the leading term is \(b_d^2\log M_d\), not \(d b_d^2\).
The statement does not give the optimal constant for fixed \(M\) as
\(d\to\infty\).

### A search-interface consequence

Take a uniform hidden variable \(S\) on a finite set \(\mathcal S\).
For each row \(i\le m\), conditional on all public data \(A=a\), let
\(X_i=T_{a,i}(S)\) be uniform on \((\mathbb Z/q)^d\).
The maps can be different across rows and the \(X_i\) need not be
independent. The public data are independent of \(S\). Each response adds
fresh noise of the stated shape to its \(X_i/q\), independently of all
other rows, of \(S\), and of the public data.
A row encoder is fixed given the public data and an independent public
seed, reads only that one response, and emits a label from a set of
size at most \(M\). The labels may then be combined by an arbitrary
estimator with all public data available. For \(|\mathcal S|\ge2\),
\[
 \mathbb P(\widehat S=S)\le
 \frac{m(1+Cb)d b^2\mathcal F((\log M)/d)+\log 2}{\log|\mathcal S|}.
 \tag{3}
\]
This includes rows that are surjective homomorphisms onto the full signal
module, such as conditioning on a unit public coefficient in scalar
dyadic Ring-LWE. It does not include arbitrary nonunit rows, adaptive
encoders using earlier response labels, joint batch compression across
rows, or iterative access to the uncompressed responses.

## 2. Scalar entropy contraction

Write \(u_q\) for uniform probability on \(\mathbb Z/q\) and \(W\) for
the reverse channel \(Y\to X\) in one coordinate:
\[
 \frac{W(a\mid y)}{u_q(a)}
    =\frac{f_b(y-a/q)}{g_b(y)}
    =1+2b\operatorname{Re}(e^{-2\pi i a/q}e^{2\pi i y})+\xi_a(y).
 \tag{4}
\]
Uniformly in \(a,y,q\ge3\), \(|\xi_a(y)|\le C_1 b^4\) and
\(\|g_b-1\|_\infty\le C_1 b^9\), by the absolute Fourier series.
The \(Q_b\) means of the first harmonic and of every \(\xi_a\) are
zero: \(g_b\) has frequencies divisible by \(q\), and \(Q_b W=u_q\).

For a probability \(\nu\) on \(\mathbb T\), set
\(r=|\int e^{2\pi i y}\,d\nu(y)|\) and \(D_0=D(\nu\|Q_b)\).
Let \(\delta=\|g_b-1\|_\infty\). For any real phase \(\theta\) and \(t\ge0\),
\[
 \int e^{t\cos(2\pi y-\theta)}\,dQ_b(y)
 \le 1+(1+\delta)(Z(t)-1)\le Z(t)^{1+\delta}.
\]
For the first inequality, subtract \(1+t\cos(2\pi y-\theta)\),
whose mean under either measure is 1; the remainder is nonnegative
pointwise. For the second, \(Z(t)\ge1\).
The relative entropy variational bound for the cosine tilted
in the direction of the first moment now gives
\[
 D_0\ \ge\ \sup_{t\ge0}\{tr-(1+\delta)\log Z(t)\},
 \qquad
 r^2\ \le\ (1+\delta)^2\mathcal F(D_0/(1+\delta))
       \le(1+\delta)^2\mathcal F(D_0).
 \tag{5}
\]
The middle implication follows because the Legendre transform at
\(A(t)\) is \(R(t)\); at \(r=1\) its value is infinite. For clarity,
\(A'(t)\) is the strictly positive variance of cosine under the
tilt, \(A(t)\uparrow1\), and \(R'(t)=t A'(t)>0\) for \(t>0\).
Also \(R(t)\to\infty\) because the tilted measures put mass tending
to one in arbitrarily short arcs, whose Haar masses tend to zero.
The increase and concavity of \(\mathcal F\) follow from
\(\mathcal F'(R(t))=2A(t)/t\) and strict decrease of \(A(t)/t\).
One direct proof of the latter uses
\(Z(t)=\sum_{n\ge0} a_n t^{2n}\), with \(a_n=1/(4^n(n!)^2)\).
Then \(Z'(t)/(tZ(t))\) is the weighted mean of \(1/[2(n+1)]\)
with weights proportional to \(a_n t^{2n}\), strictly decreasing
in \(t>0\) by the monotone likelihood ratio in \(n\).
The same series gives \(R(t)=t^2/4+O(t^4)\) and
\(A(t)^2=t^2/4+O(t^4)\) as \(t\to0\).
In particular \(\min(1,D_0)\le C_2\mathcal F(D_0)\) for all \(D_0\).

The output density relative to \(u_q\) is \(1+u(a)\) with
\(\|u\|_\infty=O(b)\) and mean of \(u\) zero. Its principal term in
(4) has \(L^2(u_q)\) norm \(\sqrt2\,b r\), since the second grid
harmonic has zero uniform mean for \(q\ge3\).
The remaining term has \(L^2(u_q)\) norm at most
\(C_3 b^4\min(1,\sqrt{D_0})\), by its zero \(Q_b\) mean and
Pinsker's inequality (or the sup bound when \(D_0=\infty\)).
Taylor expansion of the entropy,
\(D(\nu W\|u_q)=(1+O(b))\|u\|_2^2/2\), with absolute
uniform constants, together with (5), gives
\[
 D(\nu W\|u_q)\le (1+Cb)b^2\mathcal F(D_0).
 \tag{6}
\]
We will also use the uniform lower estimate
\[
 D(\nu W\|u_q)\ge (1-Cb)b^2 r^2
           - C b^7\min(1,D_0).
 \tag{7}
\]
Indeed the squared norm of a sum is at least
\((1-b)\) times the squared norm of its first term minus
\(b^{-1}\) times the squared norm of the second term.
At \(D_0=\infty\) the displayed inequalities use
\(\mathcal F(\infty)=1,\min(1,\infty)=1\).

## 3. Nonlinear tensorization and response-record bound

Under an arbitrary law \(\nu\) of \(Y^d\) passed through \(W^{\otimes d}\),
apply the relative-entropy chain rule on the output coordinates
and then (6) to the conditional input law \(Y_i\mid X_{<i}\).
The sum of expected conditional input divergences is bounded by
\(D(\nu\|Q_b^{\otimes d})\). In detail, \(Y_i\mid X_{<i}\) is a
mixture of \(Y_i\mid Y_{<i}\), because the reverse channel acts
coordinatewise; convexity of \(D(\cdot\|Q_b)\) and the relative
entropy chain rule give the assertion. Jensen's inequality for
\(\mathcal F\) across the coordinates and conditional values gives
\[
 D(\nu W^{\otimes d}\|u_q^{\otimes d})
     \le (1+Cb)d b^2\,\mathcal F(D(\nu\|Q_b^{\otimes d})/d).
 \tag{8}
\]
If the input divergence is infinite, bound each coordinate by the
right side of (6) at infinity. Apply (8) to \(Y\mid V\), where
\(X\mid Y,V\) still has the product reverse channel by the
Markov condition. Averaging conditional divergences and using Jensen
again proves (1), including the case of infinite \(I(Y;V)\).

For (3), condition on the public data and seed. Every single-row
marginal input \(X_i\) is uniform by hypothesis, and any private
independent encoder randomness can be included in the conditioning
seed without weakening an information upper bound. Given \(S\)
and those public values, the encoded responses are independent
because the error samples are independent. Therefore
\(I(S;V_1,\ldots,V_m\mid A,\mathrm{seed})\le\sum_i
 I(S;V_i\mid A,\mathrm{seed})\) by entropy subadditivity.
Every term equals \(I(X_i;V_i\mid A,\mathrm{seed})\): the row
law depends on \(S\) only through \(X_i\), which is a function of
\(S\) given the public values. Bound with (1) and \(\log M\).
Fano's inequality in the form
\(P_{\mathrm{succ}}\log|\mathcal S|\le I(S;\mathrm{transcript})+\log2\)
now gives (3).

## 4. Sharpness with a finite recording alphabet

This step certifies only the sharpness of the information upper
bound and places no runtime constraint. Draw \(M\) independent
Haar vectors in \(\mathbb T^d\) as candidate recorded centers.
For any fixed response \(y\), the \(M\) correlations with these
centers are iid and each has distribution
\(Z_d=d^{-1}\sum_{i=1}^d\cos(2\pi U_i)\) for independent Haar
\(U_i\). The law is independent of \(y\). Thus some deterministic
choice of centers yields a recording label \(V\) (largest
correlation, with a fixed tie rule) and centers \(c(V)\) with
\[
 d^{-1}\sum_i \mathbb E\operatorname{Re}\bigl(e^{2\pi i Y_i}
                  e^{-2\pi i c_i(V)}\bigr)\ \ge\ \gamma_{d,M},
 \qquad \gamma_{d,M}:=\mathbb E\max_{j\le M}Z_{d,j}.
 \tag{9}
\]
The inequality follows by averaging over the centers and over the
actual law of \(Y\). Write \(D_i(V)=D(P_{Y_i\mid V}\|Q_b)\) and
\(r_i(V)=|\mathbb E(e^{2\pi i Y_i}\mid V)|\).
For \(\gamma_{d,M}\ge0\), (9) and Cauchy–Schwarz give
\(\sum_i \mathbb E r_i(V)^2\ge d\gamma_{d,M}^2\).
Also the product input marginal implies
\(\sum_i \mathbb E D_i(V)=\sum_i I(Y_i;V)
 \le I(Y;V)\le\log M\).
Applying (7) to each conditional marginal and using the product
marginal of \(X\) gives
\[
 I(X;V)\ \ge\ \sum_i I(X_i;V)\
 \ge (1-Cb)d b^2\gamma_{d,M}^2
     - C b^7\min(d,\log M).
 \tag{10}
\]
The first inequality is the conditional entropy subadditivity
\(H(X\mid V)\le\sum_i H(X_i\mid V)\) for a product marginal \(X\).

We only need the lower estimate
\(\gamma_{d,M}\ge(1-o(1))\sqrt{\mathcal F((\log M)/d)}\)
when \(\log M\to\infty\). The following arguments prove it in
three ranges and hence on any sequence by taking subsequences.
Write \(m=\log M,\ \rho_d=m/d\).

* If \(\rho_d\to R\in(0,\infty)\), take any
  \(0<a<\sqrt{\mathcal F(R)}\). Under an exponential tilt with
  mean \(a'\) strictly between \(a\) and \(\sqrt{\mathcal F(R)}\),
  \(Z_d\) lies in \([a,a'+\eta]\) with probability tending to 1
  for any fixed \(\eta>0\). Reversing the tilt pays at most
  \(\exp(d[J(a')+t\eta])\), where \(t\) is the chosen tilt and
  \(J(a')=t a'-\log Z(t)<R\). Take \(\eta\) small enough to
  preserve the strict gap. Then \(M\mathbb P(Z_d\ge a)\to\infty\),
  so \(\mathbb P(\max_j Z_{d,j}\ge a)\to1\). The potentially
  negative contribution on failure is bounded by
  \(\mathbb E|Z_{d,1}|=O(d^{-1/2})\). Let \(a\) increase to
  \(\sqrt{\mathcal F(R)}\).
* If \(\rho_d\to0\) and \(m\to\infty\), fix
  \(0<\eta<1\) and tilt at mean
  \((1-\eta/2)\sqrt{\rho_d}\). The tilted mass of
  \([(1-\eta)\sqrt{\rho_d},\sqrt{\rho_d}]\) tends to one by
  Chebyshev, since the variance of the average is at most \(1/d\)
  and \(d\rho_d\to\infty\). The reverse weighting cost over this
  interval is at most \(\exp(m(1-\eta^2/4+o(1)))\) by
  \(t=2(1-\eta/2)\sqrt{\rho_d}+O(\rho_d^{3/2})\) and
  \(\log Z(t)=t^2/4+O(t^4)\).
  Hence the maximum reaches \((1-\eta)\sqrt{\rho_d}\) with
  probability tending to one. Its discarded negative contribution
  is \(O(d^{-1/2})=o(\sqrt{\rho_d})\) as above.
  Use \(\mathcal F(\rho_d)\sim\rho_d\) and let \(\eta\downarrow0\).
* If \(\rho_d\to\infty\), monotonicity in \(M\) and the first case
  give \(\liminf\gamma_{d,M}\ge\sqrt{\mathcal F(R)}\) for every
  fixed \(R>0\). Let \(R\to\infty\).

The error term in (10) is smaller than the leading term by
\(O(b^5)\), since \(\min(d,\log M)\le C_2 d\mathcal F(\rho_d)\).
Together with (1) this proves (2), with \(q\) allowed to vary
arbitrarily because neither (6)–(7) nor the center argument
has a \(q\)-dependent error.

## 5. Prior scope

The one-coordinate Legendre function \(J\) is a form of the
classical uniform-circle rate-distortion function with cosine loss;
see [Harremoës, Example 3 and Theorem 11](https://arxiv.org/abs/0901.0015).
Nonlinear information contraction and the fixed-reference
divergence/conditional-information framework are standard
[Polyanskiy–Wu, Theorem 4 and §2.2](https://arxiv.org/abs/1508.06025).
The specific conclusion here is the dimension- and modulus-uniform
first-order bottleneck for the *reverse* grid/wrapped-Gaussian
observation channel, including the vanishing recording rate in (2).
The expression is distinct from raw circle distortion and from
variance-only bounds with a linear factor in the number of labels.

The continuous spherical model in the [original Ring-LWE distribution
definition](https://web.eecs.umich.edu/~cpeikert/pubs/ideal-lwe.pdf)
specializes to the product law here in the orthogonal dyadic
codifferent coordinates; for (3) the public rows are explicitly
restricted to those with uniform full signal marginal. Compare
the [sample information converse](ring-lwe-search-ideal-converse.md)
for unrestricted access to the responses and the
[response interaction-degree obstruction](ring-lwe-response-degree-obstruction.md)
for a different restriction on the final readout. Neither matches
the arbitrary single-response recording interface in this note.
No implication for general Ring-LWE running time (classical or
otherwise), deployed parameters, or solver applicability is intended.
The companion finite arithmetic checker tests normalization and
coefficient identities; it does not replace the analytic proof.
