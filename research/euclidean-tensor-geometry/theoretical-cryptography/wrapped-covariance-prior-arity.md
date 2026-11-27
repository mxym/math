# Exact equality of Gaussian covariance mixtures after lattice wrapping

**Scope.** This note gives equality and nonequality criteria for
probability laws of *standalone centered noise*. The mixing parameter is
drawn once, and the errors in one batch then have independent Gaussian
draws conditionally on it. This shared-parameter distinction is present
in [Lyubashevsky–Peikert–Regev, Definitions 3.3 and 3.5](https://web.eecs.umich.edu/~cpeikert/pubs/ideal-lwe.pdf)
and for canonical block widths in
[Peikert–Regev–Stephens-Davidowitz, Definition 6.1](https://web.eecs.umich.edu/~cpeikert/pubs/rlwe-anyring.pdf).
We compare *exact batch distributions*, not what can be learned from a
finite observed data set. There is no estimator, numerical inverse,
learning sample, actual key, or security conclusion about a scheme.

## 1. Statements

Fix a full-rank lattice \(\Lambda\) in \(\mathbb R^n\). A prior \(\mu\)
on positive semidefinite symmetric matrices \(C\) feeds a Gaussian
batch: conditional on \(C\), draw \(m\) independent centered real
Gaussians of covariance \(C/(2\pi^2)\) and reduce each modulo \(\Lambda\).
This normalization makes the Fourier exponent at \(v\in\Lambda^*\)
equal to \(-v^{\mathsf T}C v\).

1. **Arbitrary covariance.** For \(n\ge2\), equal laws of the wrapped
   batches necessarily imply equal covariance priors if \(m\ge n\),
   for every full-rank lattice. This is optimal: if \(m<n\), different
   priors with smooth compactly supported strongly log-concave densities
   inside the positive-definite cone can give the same law even
   *before* wrapping. For \(n=1\) the optimal number is instead two.
2. **One width.** In the restricted family \(C=wI\) with arbitrary
   \(w\ge0\), one wrapped draw suffices if \(n\ge2\).
   In rank one a single wrapped draw fails even for different smooth
   compactly supported strongly log-concave priors on any prescribed
   positive interval, and the ambiguous priors can match any prescribed
   finite initial number of moments. Two draws sharing \(w\) suffice.
3. **Place-by-place widths.** Fix a known orthogonal decomposition
   \(\mathbb R^n=\bigoplus_{j=1}^d E_j\), each \(E_j\ne0\), and use
   \(C|_{E_j}=w_j I\), with arbitrary joint prior on \((w_1,\ldots,w_d)\).
   Two wrapped draws sharing the width vector suffice for any lattice.
   One suffices if an endomorphism \(T\) preserving \(\Lambda^*\) and
   all the blocks satisfies
   \[
       T|_{E_j}+(T|_{E_j})^{\mathsf T}=2c I,\qquad
       (T|_{E_j})^{\mathsf T}T|_{E_j}=D I,\qquad D>c^2
       \tag{1}
   \]
   with the same \(c,D\) in all blocks. An example is the ideal lattice
   of a CM field containing an imaginary quadratic subfield, with
   \(T\) multiplication by a nonreal algebraic integer in that
   subfield. Conversely, a one-dimensional block whose projection
   of the dual is discrete gives a one-draw counterexample.

The one-dimensional counterexample does not contradict the fact that
a finite atomic scalar prior is identified by one wrapped draw, even
on the circle. The lower bounds concern general priors, and the
upper bounds assert exact uniqueness, not quantitative stability.

## 2. Fourier probes and a one-dimensional density principle

For the signed difference \(\nu\) of two priors on the positive
semidefinite cone let
\[
    F(A)=\int e^{-\operatorname{tr}(AC)}\,d\nu(C)\qquad (A\succeq0).
\]
The wrapped batches have the same law if and only if
\[
    F\!\left(\sum_{i=1}^m v_i v_i^{\mathsf T}\right)=0
                      \quad\text{for all }v_i\in\Lambda^* .
    \tag{2}
\]
Indeed this is the equality of their Fourier coefficients on the
product torus, obtained by conditioning and multiplying the Gaussian
characteristics. Haar character polynomials are dense in continuous
functions on the torus, so this criterion is also sufficient.
One may use some frequencies equal to zero. The map \(F\) is
continuous on the entire positive semidefinite cone by dominated
convergence.

We will repeatedly use this consequence of the
[Müntz–Szász theorem in the Borwein–Erdélyi form](https://people.tamu.edu/~terdelyi/papers-online/Fullmuntz.pdf):
if a finite signed measure \(\omega\) on \([0,\infty)\) has a Laplace
transform that vanishes at 0 and at a locally finite unbounded
set \(\mathcal S\subset(0,\infty)\) with \(\sum_{s\in\mathcal S}1/s=\infty\),
then \(\omega=0\). Push forward under \(x=e^{-w}\) to \([0,1]\);
the vanishing quantities are the integrals of \(1\) and \(x^s\),
whose span is dense in \(C[0,1]\).
In one direction this needs neither bounded support nor a density.
Conversely, if the reciprocal sum converges, the span is not dense
on any compact nondegenerate interval \([a,b]\subset(0,\infty)\),
by the [positive-interval Müntz theorem, Borwein–Erdélyi](https://people.tamu.edu/~terdelyi/papers-online/compact.pdf).
We use this converse only for the sequence of positive integer squares
and its constant multiples.

For a nonspherical positive-semidefinite direction \(A\),
\(F(tA)\) is a scalar Laplace transform along \(t\ge0\), of the
pushforward onto the nonnegative quantity \(\operatorname{tr}(AC)\).
The same is true of \(F(B+tA)\) for any \(B\succeq0\) after multiplying
the signed measure by the bounded weight \(e^{-\operatorname{tr}(BC)}\).

## 3. Reciprocal divergence for lattice norm values in rank at least two

**Lemma.** For a positive-definite real binary quadratic form \(Q\),
the distinct positive values \(Q(k,\ell)\) for integer \(k,\ell\)
have divergent sum of reciprocals. In particular this holds for
the distinct positive squared norms of every lattice of rank at
least two, under any positive-definite metric.

Here is an elementary proof covering both rational and irrational
metrics. If the three coefficients of \(Q\) span a space of
dimension at least two over \(\mathbb Q\), express \(Q\) in a
basis of independent real coefficients with rational quadratic
forms \(Q_j\). Equal \(Q\)-values on integer pairs imply equal
\(Q_j\)-values for every \(j\). At least one \(Q_j\) is not
proportional to \(Q\): otherwise all nonzero rational forms \(Q_j\)
would be rational multiples of one rational form and the coefficient
span of \(Q\) would have dimension one. In coordinates whitening
\(Q\) and diagonalizing this \(Q_j\), a fixed pair of values fixes
both coordinate squares, since the two eigenvalues are distinct.
Thus there are at most four representations of each positive value.
The ellipse \(Q\le X\) contains \(cX\) integer pairs for all large \(X\)
(for instance from an inscribed square), so the distinct count
is at least \(c'X\).

If the coefficients are proportional to rational numbers, scale
to a rational form and restrict to a rank-two sublattice on which
it is diagonal: if the basis vectors are \(u,v\), clear denominators
in \(v-\langle u,v\rangle_Q u/\langle u,u\rangle_Q\).
After another constant scaling the restricted form is
\(Ak^2+B\ell^2\) with positive integers \(A,B\). In the range
of values \(\le X\), all four coordinates of any equality of two
representations have size \(O_{A,B}(\sqrt X)\).
Write a nontrivial equality as
\[
      A(k-k')(k+k')=B(\ell'-\ell)(\ell'+\ell).
\]
When both sides are zero there are \(O(X)\) equalities.
Otherwise take absolute values, at a constant cost from possible
signs, and reduce the ratio \(A|k-k'|/(B|\ell'-\ell|)=r/s\)
to coprime integers. For \(h=\max(r,s)\), the common integer
factor before reduction has \(O(\sqrt X/h)\) possibilities.
The complementary factors \(|k+k'|,|\ell'+\ell|\) are an
integer multiple of \(s,r\), again \(O(\sqrt X/h)\) possibilities.
There are \(O(h)\) pairs \((r,s)\) of maximum \(h\).
The total number of equalities is therefore
\(O(X)+O(X\sum_{h\le C\sqrt X}1/h)=O(X\log X)\).
There are at least \(cX\) representations in all, so Cauchy–Schwarz
gives at least \(c'X/\log X\) distinct values. Partial summation
then gives divergence of their reciprocals by the integral of
\(1/(X\log X)\). Constant rescaling does not affect divergence.
For higher rank restrict to any two independent lattice vectors.

## 4. Sharp arity for arbitrary covariance

Suppose first that \(n\) is even and \(m=n\). Fix a basis matrix
\(B\) of \(\Lambda^*\). For an integer \(n\times n\) matrix \(V\),
\(A=BVV^{\mathsf T}B^{\mathsf T}\) is an available probe.
Right-multiply \(V\) by a block-diagonal matrix with \(n/2\) identical
integer blocks
\(\left(\begin{smallmatrix}k&-\ell\\ \ell&k\end{smallmatrix}\right)\).
It yields probe \((k^2+\ell^2)A\) with the **same** number of
frequencies. The lemma for \(k^2+\ell^2\) and the density principle
imply \(F(tA)=0\) for every \(t\ge0\). For rational \(V\) clear
denominators and then use the real scale \(t\), so the same conclusion
holds. Such rational Gram factorizations are dense in the
positive semidefinite cone, because real matrices have dense
rational approximations and every positive semidefinite matrix
has a square root. Hence \(F\) vanishes on the entire cone.

When \(n\ge3\) is odd and \(m=n\), reserve the last frequency
\(v\in\Lambda^*\). Run the preceding integer two-column rotations
on the \(n-1\) other columns, with an \(n\times(n-1)\) matrix \(V\).
For each fixed \(v\), apply the density principle to
\(F(vv^{\mathsf T}+tBVV^{\mathsf T}B^{\mathsf T})\), which vanishes
also at \(t=0\) by (2). Then clear denominators and pass to all real
rank-\(\le n-1\) factorizations:
\[
        F(vv^{\mathsf T}+A)=0
           \quad (A\succeq 0,\ \operatorname{rank}A\le n-1).
        \tag{3}
\]
Now fix any \(Q\succ0\). For each nonzero \(v\in\Lambda^*\), let
\(t_v=v^{\mathsf T}Q^{-1}v\). The matrix
\(t_v Q-vv^{\mathsf T}\) is positive semidefinite of rank \(n-1\):
conjugating by \(Q^{-1/2}\) gives \(t_v I-ww^{\mathsf T}\)
with \(\|w\|^2=t_v\). Thus \(F(t_v Q)=0\) by (3).
The lemma for metric \(Q^{-1}\) says the *distinct* values
\(t_v\) have divergent reciprocal sum. A second application of
the density principle gives \(F(tQ)=0\) for all \(t\ge0\).
Extend by continuity from positive definite \(Q\) to the entire cone.
This avoids having to realize a nonsquare common scaling by an odd
number of dimensions.

In either case, zero \(F\) on the cone implies \(\nu=0\).
For example, encode \(C\) via \(\operatorname{tr}(A_j C)\) on a
basis of positive semidefinite \(A_j\) for the symmetric matrices:
one can use the rank-one matrices of \(e_i\) and \(e_i+e_j\)
for \(i<j\). This gives an injective linear coordinate map with
nonnegative image coordinates. The joint Laplace transform there
is known at all nonnegative parameters because
\(\sum_j t_j A_j\succeq0\). Already the nonnegative integer
parameters identify the signed measure after exponential
coordinate mapping to a cube, by polynomial density.

For sharpness when \(m<n\), use real coordinates \(C_{ii},C_{ij}\)
(\(i<j\)) on symmetric matrices. Let the matrix of commuting constant
coefficient derivatives have entries \(\partial/\partial C_{ii}\)
on the diagonal and \(\tfrac12\partial/\partial C_{ij}\) in both
positions \(ij,ji\). For a smooth nonnegative nonzero bump \(g\)
compactly supported in a small ball inside the positive-definite cone,
apply the determinant of the top \((m+1)\)-by-\((m+1)\) principal
block of this matrix of operators to \(g\), obtaining \(h\).
Integration by parts gives
\[
   \int e^{-\operatorname{tr}(AC)} h(C)\,dC
      = \det(A_{1:m+1,\,1:m+1})\int e^{-\operatorname{tr}(AC)}g(C)\,dC.
\]
The half factors account for the double occurrence of off-diagonal
entries in the trace. Hence \(\int h=0\), and \(h\ne0\)
by taking \(A=I\). It annihilates every probe of rank at most \(m\),
even with arbitrary real rather than lattice frequencies. Add and
subtract a sufficiently small multiple of \(h\) to a common smooth
probability density on a slightly larger ball inside the cone.
The base density can be proportional to
\(\exp[-1/(R^2-\|C-C_0\|^2)]\) on the ball of radius \(R\), extended
by zero. It is strictly positive there and its log has Hessian
bounded above by a negative multiple of the identity. Since \(h\)
is supported strictly inside that ball, small \(C^2\) perturbations
preserve both positivity and strict log-concavity.
The resulting different priors give the same unwrapped batch by
the ordinary characteristic-function uniqueness theorem and thus
also the same wrapped law.

## 5. Scalar and block widths

For the scalar family \(C=wI\), (2) depends just on sums of
squared lattice norms. In rank at least two the lemma proves
one-draw uniqueness by the scalar density principle.
In rank one the available set for a single draw is a constant
multiple of integer squares; for a pair of draws it contains
a constant multiple of sums of two squares. The divergence lemma
therefore proves uniqueness of a shared scalar width for two draws.

To prove failure for one draw on a circle, take a smaller closed
positive interval inside the interval of allowed widths. After
\(x=e^{-w}\), the non-density statement in §2 and Hahn–Banach
give a nonzero signed finite measure on that interval annihilating
the constant function and all probed exponentials. Convolve it
in the width coordinate with a small nonzero nonnegative smooth
mollifier, with support remaining inside the allowed interval.
This multiplies its Laplace transform by the mollifier's transform
and preserves the zeros. It remains nonzero: a finite signed
compactly supported measure has a nonzero Laplace transform
somewhere on the real axis unless it is zero, and the mollifier's
transform is positive there. If desired, differentiate the resulting
compactly supported smooth function \(k+1\) times to make its
moments of degrees \(0,\ldots,k\) vanish by integration by parts;
the probed Laplace values stay zero. The derivative is nonzero
because a nonzero compactly supported smooth function cannot be
a polynomial. Add and subtract a small multiple of this function
to a smooth strictly strongly log-concave base density on the
positive interval, with the perturbation supported strictly inside,
as in §4. This gives the claimed smooth ambiguous priors.
Refreshing the parameter independently between observations would
keep their single-draw laws identical at every batch size;
two *shared*-width observations are different. For finite atomic
scalar priors the difference is a finite weighted sum of
\(e^{-tw}\) for distinct \(w\); vanishing as a function of an
unbounded sequence of frequency squares forces the coefficient
of the smallest \(w\) to vanish, then all others successively.

For the block setting, the Laplace direction of a frequency \(v\)
is
\[
    q(v)=(\|\operatorname{proj}_{E_j}v\|^2)_{j=1}^d .
\]
Two frequencies \(kv,\ell v\) give direction
\((k^2+\ell^2)q(v)\). After the density principle this yields
the whole ray through \(q(v)\) in the nonnegative orthant.
The union of the rays is dense in the orthant: for any
\(a=(a_j)\ge0\) choose a real vector \(z\) with block norms
\(\sqrt{a_j}\), and approximate \(kz\), as integer \(k\to\infty\),
within a fixed fundamental-parallelepiped distance by dual lattice
vectors \(v_k\). Then \(q(v_k)/k^2\to a\). Continuity and
multivariate Laplace uniqueness give equality of the joint prior
without any independence hypothesis. If (1) holds, the single
frequency \(kv+\ell T v\) instead gives
\((k^2+2c k\ell+D\ell^2)q(v)\), the same argument by the lemma.
For the CM example, conjugate embeddings of the imaginary quadratic
integer have the same real part \(c\) and squared modulus \(D>c^2\),
and multiplication preserves the dual ideal.
Finally if some real one-dimensional block projects the dual
to a discrete line lattice, all its one-draw directions are
a multiple of squares. Take the ambiguous scalar priors independently
of identical widths in the other blocks. Equality of each probed
product Laplace value gives equality of the one-draw mixtures.

The use of Laplace values of wrapped Gaussian scale mixtures is
classical; see [Jammalamadaka and coauthors, §4](https://jammalam.faculty.pstat.ucsb.edu/html/Some%20Publications/2017_Wrapped%20CDs%20via%20Mixtures_Sankhya.pdf).
[Vandermeulen–Scott](https://arxiv.org/abs/1502.06644) treat identifiability
of *finite* mixtures of arbitrary component distributions from grouped
samples. The exact rank-dependent arity here is for arbitrary priors
with a restricted Gaussian component family, and uses the arithmetic
Fourier probes of the wrapping lattice.

**Replay.** Run `node verify-wrapped-covariance-prior-arity.js` for
exact synthetic Gram-rotation, odd-rank tangency, binary-form multiplicity,
and block-probe checks. The existence of the ambiguous smooth priors
and the infinite-dimensional uniqueness are proved above, not inferred
from the replay.
