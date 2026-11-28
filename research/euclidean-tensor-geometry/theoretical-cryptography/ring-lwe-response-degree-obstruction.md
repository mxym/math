# An exact response-interaction obstruction for Ring-LWE-style hidden characters

This note bounds methods whose final readout has bounded interaction
degree in the noisy response blocks. The public coefficient matrix and
the response cosets outside the signal subgroup can be used arbitrarily.
The bound is for predicting a fixed nontrivial character of the hidden
element, not only for distinguishing an averaged distribution.
It is a theorem about the specified readout space, **not** a
polynomial-time lower bound for general Ring-LWE, an attack,
or any result about a deployment.

The use of Fourier moments for binary linear tests is standard:
see [Couteau–Rindal–Raghuraman, §3.2](https://opencryptology.org/2021/1150/versions/20240114T061328Z.pdf).
The low-degree likelihood framework is broader
[Hsieh et al., overview and limitations](https://arxiv.org/abs/2601.05850);
there are even explicit counterexamples to general low-degree
implications for polynomial time
[Holmgren–Wein, ITCS 2021](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITCS.2021.75).
Here the exact norm is for a finite **module** and a specified hidden
character. It incorporates the Fourier spectrum of the conditional
fiber of an arbitrary torus noise law. It is not the unrestricted
information converse in the [previous search note](ring-lwe-search-ideal-converse.md)
and it does not describe a transcript consisting only of certain
[folds](folded-error-information-limit.md).

## 1. Model and the declared readout space

Let \(R\) be a finite unital ring, \(M\) a finite left \(R\)-module,
and \(\iota:M\hookrightarrow G\) an injective additive map into
a compact metrizable abelian group. Let \(A\in R^{m\times n}\) have
independent uniform entries, \(S\) be independent and uniform on \(M^n\),
and let
\[
       B_i=\iota\!\left(\sum_j A_{ij}S_j\right)+E_i,\qquad
                           E_i\stackrel{\rm iid}{\sim}\mu .
\]
There is no feedback in the row selection. In the dual torus model
\(M=O_K^\vee/qO_K^\vee\), \(G=K_{\mathbb R}/O_K^\vee\),
and the signal map is \(s\mapsto s/q\bmod O_K^\vee\), as in
[LPR, Definition 3.1](https://web.eecs.umich.edu/~cpeikert/pubs/ideal-lwe.pdf).
Scalar Ring-LWE corresponds to \(n=1\) and can have a growing ring;
the growing-\(n\) statements below concern a different module limit.

Write \(Z_i=B_i+\iota(M)=E_i+\iota(M)\). Choose a measurable section
\(\sigma:G/\iota(M)\to G\) and identify the response within
this fiber by \(B_i=\sigma(Z_i)+\iota(Y_i)\). The corresponding
noise fiber probabilities are \(p_z\) on \(M\). They are well
defined almost everywhere by disintegration on finite fibers; a
Borel section can be obtained by choosing the least member
of each finite fiber under a fixed Borel total order on \(G\).
Let \(Q\) be the reference with the same public \(A,Z\), but,
conditional on these data, \(Y_1,\ldots,Y_m\) independent uniform
on \(M\). This retains all response-only bias visible in \(Z\),
which by construction is independent of the hidden element.

For an integer \(D\) with \(0\le D\le m\), a response-degree-\(D\)
readout \(F(A,Z,Y)\) is any function such that for almost every
\(A,Z\), its Fourier expansion in \(Y\in M^m\) consists of
characters supported on at most \(D\) response positions.
Equivalently it is a sum of functions each using at most \(D\)
response fibers, with the **entire** \(A,Z\) available in each
function. Neither the number of summands nor the computational
complexity of their coefficient functions is restricted.
If a method computes some low-degree statistics and then
applies nonlinear postprocessing, the *final* readout need not
lie in this space.

Write \(\widehat M\) additively for the group of characters, with
right \(R\)-action \((\xi\cdot a)(x)=\xi(ax)\).
Put
\[
       w_\xi=\mathbb E_Z\left|\sum_{x\in M}p_Z(x)\xi(x)\right|^2,
                  \qquad W=\sum_{\xi\ne0}w_\xi .
\]
These are independent of the section choice. By finite Parseval
\(W=\mathbb E_Z\chi^2(p_Z\|U_M)\le |M|-1\).

## 2. Exact norm identity for hidden-character correlation

Fix \(\chi=(\chi_1,\ldots,\chi_n)\in\widehat M^n\) nonzero
and write \(\chi(S)=\prod_j\chi_j(S_j)\). For any \(r\)-tuple of
nontrivial frequencies \(\xi_1,\ldots,\xi_r\), put
\(N(\xi_1,\ldots,\xi_r)=\sum_{i=1}^r \xi_i R\), a right submodule
of \(\widehat M\). Define
\[
 \mathcal E_D(\chi)=
   \sum_{r=1}^D\binom mr
     \sum_{\xi_1,\ldots,\xi_r\ne0}
       \frac{{\bf1}_{\{\chi_1,\ldots,\chi_n\in N(\xi_1,\ldots,\xi_r)\}}}
            {|N(\xi_1,\ldots,\xi_r)|^n}\,
       \prod_{i=1}^r w_{\xi_i}.                                      \tag{1}
\]
Then for every response-degree-\(D\) readout,
\[
   \big|\mathbb E[\overline{\chi(S)}F(A,Z,Y)]\big|
          \le \|F\|_{L^2(Q)}\sqrt{\mathcal E_D(\chi)} .                 \tag{2}
\]
In particular it applies to any bounded readout predicting the
character with a correlation criterion; the expectation on the
left is in the actual observation experiment. Formula (1) is
the exact squared norm of this linear functional on the
response-degree space. It is a restriction on information used,
not an assertion about how to construct or compute any readout.

To prove it, condition on \(A,Z\). The cosets \(Z\) contain no
hidden information and the noise fibers are independent.
For a fixed character tuple \(\xi\) on \(Y\), expectation of its
product times \(\overline{\chi(S)}\) is the product of the
conditional noise Fourier coefficients multiplied by
\[
                  \prod_{j=1}^n
                  {\bf1}_{\{\sum_{i=1}^m \xi_i\cdot A_{ij}=\chi_j\}} .
 \tag{3}
\]
This follows by separately averaging each \(S_j\): the integral
of a nontrivial character of a finite additive group is zero.
The conditional characters are orthonormal under the reference.
Hence Cauchy–Schwarz bounds the correlation by the square root
of the sum of the absolute squared conditional expectations
over tuples of support at most \(D\), times the conditional
\(L^2\) norm of the readout. Average again by Cauchy–Schwarz.

For each fixed tuple of nonzero frequency entries, the sum
in (3) for one column is uniform on \(N=\sum_i\xi_iR\):
the coefficient map from the additive group \(R^r\) is
a homomorphism with image exactly \(N\), so all fibers have
equal size. Distinct columns are independent. Thus the
expectation of (3) is \(|N|^{-n}\) if every \(\chi_j\in N\)
and is zero otherwise. The independent cosets average the
squared noise coefficients to \(\prod_i w_{\xi_i}\).
Finally count the choices of support. This proves (1)–(2),
and the norm equality follows from the orthogonal decomposition:
the coefficients of the linear functional are exactly the
conditional expectations just computed. In the trivial character
case the same formula, excluding degree zero, gives the norm for
the difference between the actual output expectation and the
reference expectation.

A conditional, high-probability reading is also available.
For each \(A,Z\) the squared conditional functional norm is the
sum before the last averaging step. It is nonnegative and has
mean \(\mathcal E_D(\chi)\). By Markov, except on a set of
\(A,Z\) of probability at most \(\mathcal E_D(\chi)/\eta^2\),
every conditional \(L^2\)-unit readout in the declared space has
correlation at most \(\eta\). There is no exchange of a conditional
worst case with an average.

## 3. Consequences and a limitation that holds even without noise

Put \(N_\chi=\sum_j\chi_j R\), not zero because the ring is unital
and \(\chi\ne0\). Equation (1) implies the upper bound
\[
          \mathcal E_D(\chi)\le |N_\chi|^{-n}
                    \sum_{r=1}^D\binom mr W^r.                        \tag{4}
\]
In the special case \(R=M=\mathbb F_Q\), every nonzero frequency
generates the full dual, so (4) is exact with \(|N_\chi|=Q\).
If \(m=O(n)\) and \(D=o(n)\), its right side is
\(Q^{-n+o(n)}\), uniformly even if \(Q\ge2\) grows, since
\(W\le Q-1\) and
\(\sum_{r\le D}\binom mr=\exp(o(n))\) in this range.
The latter statement also holds when \(D\) is not below \(m/2\):
if that occurs then \(m\le 2D=o(n)\), and bound by \(2^m\).
For fixed \(M,R\) one likewise obtains an exponentially small
bound for any nontrivial \(\chi\) because \(|N_\chi|\ge2\).
For the scalar \(n=1\) case with a growing module, (4) instead
is a bound involving the actual \(|N_\chi|\), \(W\), and \(D\);
the previous growing-\(n\) conclusion does not apply.

For a finite nilpotent chain toy model \(R=M=\mathbb F_2[u]/(u^k)\),
the pairing \(\xi_c(x)=(-1)^{[u^{k-1}](cx)}\) identifies the right
dual with \(R\). It is nondegenerate because the first nonzero
coefficient of \(c\) can be paired to total degree \(k-1\).
The submodules form the chain \(N_j=(u^{k-j})\), of size \(2^j\).
Set \(W_j=\sum_{\xi\in N_j\setminus\{0\}}w_\xi\). If
\(N_\chi=N_a\), the inner sum of (1) equals exactly
\[
                   \sum_{j=a}^{k}2^{-jn}(W_j^r-W_{j-1}^r).
\]
Indeed a tuple generates \(N_j\) if and only if all its entries
are in \(N_j\) but not all are in \(N_{j-1}\). This is a spectral
obstruction in the stated model, not a parameter claim.

A whole-element version does not require averaging over a random
\(A\). Suppose a guessing rule's probabilities of each guessed
value, as functions of \(Y\) for fixed \(A,Z\), have response degree
at most \(D\). Put \(N_0=|M|^n\). For fixed \(A,Z\), its success
probability is bounded by
\[
 \frac1{N_0}+
 \sqrt{\frac{1-1/N_0}{N_0}\!
      \sum_{\substack{I\subseteq\{1,\ldots,m\}\\1\le|I|\le D}}
            \prod_{i\in I}\chi^2(p_{Z_i}\|U_M)} .                    \tag{5}
\]
Indeed under reference with an independent uniform \(S\), the
success score on \((S,Y)\) has mean \(1/N_0\) and centered
squared norm at most \((1-1/N_0)/N_0\), because the probabilities
sum to one and each is in \([0,1]\). For each fixed \(S\) the
conditional response likelihood is a product of fiber densities
relative to uniform, translated by the signal; translations
preserve Fourier magnitudes. Its nonconstant projection of
degree at most \(D\) has squared norm equal to the sum in (5),
independent of both \(S\) and the row values. Cauchy–Schwarz in
the product reference gives (5). Averaging and Jensen replace
the sum under the square root by \(\sum_{r\le D}\binom mr W^r\).
This is a different criterion from an unrestricted rule that
only uses low-degree *intermediate* statistics.

It is important that (1)–(5) can give a small bound **even for
noiseless data**. In the field model with a fixed \(Q\),
\(m=\lceil(1+c)n\rceil\), \(c>0\), and no noise, a uniform public matrix
has full column rank with probability tending to one:
a union bound over nonzero vectors bounds failure by \(Q^{n-m}\).
Ordinary field linear algebra on the full system is a classical
polynomial-time operation, while every bounded readout of
response degree \(o(n)\) still has exponentially small
correlation by (4). Thus the result is not evidence of an
unconditional computational lower bound merely by interpreting
small interaction degree as efficient computation. No claim is
made about general noisy polynomial-time computation.

## 4. Fourier weights for the wrapped lattice response

In the torus \(G=\mathbb R^d/L\), let \(p\) be a positive
noise density with respect to probability Haar. Define
\[
   p_M(x)=|M|^{-1}\sum_{u\in M}p(x+\iota(u)),\qquad
   P_\xi p(x)=|M|^{-1}\sum_{u\in M}p(x+\iota(u))\,\overline{\xi(u)}.
\]
The quotient density is \(p_M\), as a function constant on each
fiber. In a chosen fiber the conditional Fourier coefficient
in absolute value is \(|P_\xi p|/p_M\), so
\[
               w_\xi=\int_G |P_\xi p|^2/p_M\,d\mathrm{Haar}.          \tag{6}
\]
Here the conjugate in \(P_\xi\) only changes Fourier convention,
not the absolute value, because \(p\) is real. Parseval gives
\(\int|P_\xi p|^2=\sum_{\gamma|_{\iota(M)}=\xi}|\widehat p(\gamma)|^2\),
where the sum is over the dual lattice \(L^*\). For a centered
spherical width-\(s\) wrapped Gaussian, this becomes
\(\sum_{\gamma|_M=\xi}e^{-2\pi s^2\|\gamma\|^2}\).
If \(p_M\in[1-\epsilon,1+\epsilon]\) with \(\epsilon<1\), divide
that sum by \(1+\epsilon\) or \(1-\epsilon\) to obtain lower
and upper bounds on \(w_\xi\). Anisotropic covariance simply
changes the quadratic form. The weights use the **whole fiber**,
not just an unconditional marginal coefficient on a particular
character representative. The formula assumes independent draws
from the specified fixed error law (or conditions on a shared fixed
parameter); it does not classify mixtures of such experiments.

The companion checker uses only tiny fixed abstract fields and
nilpotent rings, with exact generated probabilities to compare
finite character identities. No guessing procedure, cryptographic
parameters, or concrete samples are used.
