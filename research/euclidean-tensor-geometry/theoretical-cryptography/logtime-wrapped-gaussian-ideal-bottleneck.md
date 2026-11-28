# Log-time concavity and the unique Gaussian torus information bottleneck

A wrapped Gaussian on a circle has strictly concave entropy
as a function of the logarithm of its heat time. This identifies
the unique limiting ideal direction in a fixed-modulus search
experiment. The result also handles unequal independent widths in
the coefficient coordinates by averaging cyclic coordinate orders.
It is an information-theoretic comparison and does not supply an
algorithm for any hidden-label or cryptographic problem.

## 1. A positive representation for the Fisher deficit

Use angular coordinates \(\theta\in\mathbb R/(2\pi\mathbb Z)\)
and normalized Haar measure. For heat time \(t>0\) let
\[
 p_t(\theta)=\sum_{n\in\mathbb Z} e^{-tn^2}e^{in\theta},\qquad
 h(t)=-\int p_t\log p_t,\qquad
 A(t)=\int p_t(\partial_\theta\log p_t)^2 .
\]
The raw Gaussian before wrapping has variance \(2t\).
The heat equation and periodic integration by parts give
\(h'(t)=A(t)\). We show an exact representation with a
nonnegative auxiliary variable \(V\) independent of \(t\):
\[
       1-2t A(t)=
         \mathbb E\!\left[\Theta_4(t+t^2V)\right],\qquad
 \Theta_4(s)=\sum_{n\in\mathbb Z}(-1)^n e^{-sn^2},\qquad
 V=\sum_{j\ge1}\frac{G_j}{\pi^2j^2},
 \tag{1}
\]
where the \(G_j\) are independent mean-one exponentials.

Indeed, the Jacobi product for \(p_t\) gives
\[
 \log p_t(\theta)
   =c(t)+2\sum_{n\ge1}
       \frac{(-1)^{n+1}e^{-tn}}{n(1-e^{-2tn})}\cos(n\theta).
\]
This is the known Lambert-series route to the angular Fisher
coefficient; see [Jang et al., Lemma A.2 and the alternating
sum in Lemma A.5](https://arxiv.org/pdf/2610.37985v1).
Taking minus the \(p_t\) expectation of the second derivative,
with \(\mathbb E_{p_t}\cos(n\theta)=e^{-tn^2}\), gives
\[
 A(t)=\sum_{n\ge1}(-1)^{n+1}
                   \frac{n e^{-tn^2}}{\sinh(tn)}.
 \tag{2}
\]
All differentiations and integrals here are justified by
absolute, locally uniform convergence for \(t>0\), and by
positivity of \(p_t\). The Euler product for the
[hyperbolic sine](https://dlmf.nist.gov/4.36.E1) gives, for
real \(x\),
\[
 \mathbb E e^{-t^2x^2 V}
     =\prod_{j\ge1}(1+t^2x^2/(\pi^2j^2))^{-1}
     =t x/\sinh(t x).
\]
This includes value 1 at \(x=0\). The series defining \(V\)
is finite almost surely with finite mean, since the sum of
its expected nonnegative terms is finite.
Substituting this equality in the two-sided alternating
sum of (2) gives (1); the absolute value is summable under
the majorant \(e^{-tn^2}\). The hyperbolic-sine mixture
representation is itself classical; the point here is
its substitution into the normalized Fisher deficit.

For \(s>0\) the [Jacobi product for \(\theta_4\)](https://dlmf.nist.gov/20.5.E4)
is
\[
 \Theta_4(s)
   =\prod_{j\ge1}(1-e^{-2js})(1-e^{-(2j-1)s})^2 .
\]
It is positive and strictly increasing in \(s\), with
\(\Theta'_4(s)>0\): the logarithmic derivative is a normally
convergent sum of positive terms for \(s>0\).
It tends to zero at \(s\downarrow0\), bounded above by
\(1-e^{-2s}\), and to 1 as \(s\to\infty\).
For each \(V\ge0\) the map \(t\mapsto t+t^2V\) has positive derivative,
and differentiating its \(\Theta_4\) expectation is justified
on compact positive \(t\)-intervals by an integrable bound
\(C(1+V)\), using the absolutely convergent differentiated
theta series for \(s\ge t\). Thus \((t A(t))'<0\) for every
\(t>0\). The limits of \(t A(t)\) at 0 and infinity are,
respectively, \(1/2\) and 0 by bounded convergence.
In particular
\[
            H(u):=h(e^u)\quad\text{satisfies}\quad
            H'(u)=e^u A(e^u)>0,\quad H''(u)<0 .
 \tag{3}
\]

## 2. Strict ordering of scalar group ratios

Write \(b=e^{-t}\) and
\(f_b(x)=p_t(2\pi x)\) on \(\mathbb R/\mathbb Z\).
For integer \(\ell>1\), let \(C_\ell(b)\) be the mutual
information between a uniform \(\ell\)-point circle-grid
signal and that signal plus independent \(f_b\)-noise.
Averaging the noise over the grid retains only Fourier
modes in \(\ell\mathbb Z\). The output density is
\(f_{b^{\ell^2}}(\ell x)\), whose entropy is \(h(\ell^2t)\),
because \(x\mapsto\ell x\) preserves Haar measure.
Consequently
\[
   \frac{C_\ell(b)}{\log\ell}
       =2\,\frac{H(\log t+2\log\ell)-H(\log t)}{2\log\ell}.
 \tag{4}
\]
The right-hand secant slope of the strictly concave
\(H\) at fixed \(\log t\) decreases strictly as \(\ell\)
increases, even when extended to a real variable \(\ell>1\).
In particular the minimum normalized information among
divisors \(\ell>1\) of **any** \(q\) is at \(\ell=q\),
uniquely. This proves strictness for every \(b\in(0,1)\),
not only a large-noise or small-noise expansion.

## 3. Cyclic averaging removes dependence on an anisotropic basis order

Let \(q\ge2\), let \(J\ne0\) be an additive subgroup of
\((\mathbb Z/q)^d\) invariant under a group of signed coordinate
permutations which acts transitively on the axes, and let
\(X\) be uniform in \(J\). The observations \(Y_i=X_i/q+E_i\)
are modulo 1 with independent \(E_i\sim f_{b_i}\),
\(b_i\in(0,1)\) arbitrary. Then
\[
 \frac{I(X;Y)}{\log|J|}
    \ \ge\ \frac{1}{d\log q}\sum_{i=1}^d C_q(b_i),
 \qquad
 \text{equality iff } J=(\mathbb Z/q)^d .
 \tag{5}
\]
In particular this holds for all nonzero ideals of the
negacyclic ring \((\mathbb Z/q)[x]/(x^d+1)\), by its signed
cyclic multiplication action. This strict information
statement by itself does not require fixed or odd modulus.

For any fixed order \(i_1,\ldots,i_d\) define \(\ell_j\) as
the cardinality of the subgroup underlying the conditional uniform
law of \(X_{i_j}\) given \(X_{i_1},\ldots,X_{i_{j-1}}\).
The conditional law is a uniform translate with the same
\(\ell_j\) at every allowed prefix, since the projection
between successive subgroup projections has equal fibers.
In particular \(\sum_j\log\ell_j=\log|J|\).
The product channel gives
\[
 I(X;Y) \ge
 \sum_j I(X_{i_j};Y_{i_j}\mid X_{i_1},\ldots,X_{i_{j-1}})
  = \sum_j C_{\ell_j}(b_{i_j})
  \ge \frac{1}{\log q}\sum_j\log\ell_j\, C_q(b_{i_j}).
 \tag{6}
\]
The first inequality is by the entropy chain rule.
Its nonnegative deficit is the sum of conditional mutual
informations of \(Y_{i_j}\) and the earlier \(X\)-coordinates
given earlier \(Y\)-coordinates, because \(Y_{i_j}\) is
conditionally independent of earlier \(Y\) given earlier \(X\).
The last inequality uses (4), with \(C_1=0\).
Equality in the first inequality requires \(J\) to be a product:
if a conditional mutual information vanishes, the law of
\(Y_{i_j}\) given earlier \(X\) must be the same for every
allowed earlier \(X\). Positivity of all noise densities
ensures each earlier label has positive posterior probability
at every earlier observation, and all Fourier coefficients of
\(f_{b_{i_j}}\) are nonzero, so observation convolution is
injective on the coordinate input laws. Thus that input
coordinate is independent of the earlier ones. If equality
holds in every term the inputs form a product.

Start from any fixed order and apply every element of the
signed permutation group to it. By invariance of \(J\),
\(\ell_j\) at position \(j\) stays the same in this reordered
version; signs only relabel the prefix and coordinate group.
Transitivity sends each position label uniformly through the axes.
Averaging (6) over the group gives (5). If \(J\) is not a product,
every order incurs a strict deficit in the first inequality.
If it is a nonzero product, transitivity makes all subgroup
orders equal to one \(\ell>1\). Then (4) is strict unless
\(\ell=q\), which is exactly the full grid. This establishes
the equality statement.

## 4. Consequence for the full statistical search window at fixed odd modulus

Apply the [fixed-odd-modulus search theorem](ring-lwe-fixed-odd-modulus-threshold.md)
in the spherical case. Formula (4) eliminates the apparently
multiple divisor candidates in its statement: \(q\) is the
only possible active ideal at every interior \(b_*\).
Thus the first-order rate is \(C_q(b_*)/\log q\)
even when \(q\) is composite. The corresponding second-order
profile is the single scalar normal CDF, with the \(q\)-grid
scalar likelihood variance.

More generally let \(q\ge3\) be odd and fixed and let \(d\to\infty\)
through powers of two. Use precisely that note's observation
model (iid uniform public rows, uniform hidden element, product
continuous wrapped Gaussian error in the coefficient coordinates),
except the coefficients of the error have independent nomes
\(b_{d,1},\ldots,b_{d,d}\) that can vary arbitrarily within a
fixed compact subinterval of \((0,1)\). The product error law
is the same in each row. Write
\[
 \begin{split}
 M_d&=\sum_{i=1}^d C_q(b_{d,i}),\\
 V_d&=\sum_{i=1}^d
  \operatorname{Var}_{f_{b_{d,i}}}
  \left(\log\frac{f_{b_{d,i}}(u)}
                 {f_{b_{d,i}^{q^2}}(qu)}\right).
 \end{split}
\]
If \((m M_d-dn\log q)/\sqrt{mV_d}\to z\in[-\infty,\infty]\),
the unlimited-computation best success for the realized public
matrix tends to \(\Phi(z)\) in \(L^1\) over the matrix.

To prove this extension, use the fixed-base ideal decomposition
of the cited note, valid independently of the errors. Each
ideal is the product of \(d/d_0\) copies of its base ideal
\(J_0\), after a coordinate permutation, for one fixed
\(d_0\). Product noise remains product, with different
coordinate nomes allowed in each base block.
For every proper nonzero \(J_0\), inequality (5) gives the
strict bound per block, in the notation of that note,
\[
      D_{J_0}(\boldsymbol b)>
           \frac{\log|J_0|}{d_0\log q}
                \sum_{i\ \text{in block}} C_q(b_{d,i}).
\]
Its positive gap is uniform over the compact set of block widths
and the finitely many base ideal types, by continuity.
The ideal information sums have bounded block increments and
variance \(O(md)\). In the central window any proper ideal's
mean exceeds its own \(n\log|J|\) threshold by \(\Omega(md)\):
the difference in the full normalized center is at most
\(O(\sqrt{md})\), and each block gap is bounded below.
Thus all proper ideals are inactive in the finite-sample sandwich
of the cited note. The full-ideal sum has independent scalar
increments with mean \(mM_d\) and variance \(mV_d\).
The individual variances have positive lower bounds on the
compact set (a constant scalar log likelihood would force
a nontrivial translation invariance), and all increments are
bounded. The triangular-array CLT and a cutoff
\(\gamma=(md)^{1/4}\) in the sandwich give the result for finite \(z\).
If \(z=+\infty\), the full mean also lies above its threshold
and the proper gaps remain uniform; concentration and the lower
half of the same sandwich give limit 1.
If \(z=-\infty\), the full-direction upper bound gives limit 0.
The deterministic upper and ensemble-average lower bounds squeeze
\(L^1\) for a finite limit in the same way as in the cited note.

The statistical corollary depends on the fixed odd modulus and
the stated product coordinate law. A diagonal law in these
coefficient coordinates is **not** an arbitrary elliptical law
in archimedean embedding coordinates. We make no inference for
nonproduct errors or width sequences approaching the endpoints
under this corollary, and no assertion about a classical
polynomial-time procedure. The analytic identities and cyclic
averaging do not depend on those corollary restrictions.
