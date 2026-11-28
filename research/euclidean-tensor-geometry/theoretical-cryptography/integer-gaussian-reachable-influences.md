# Exact reachable-center influences in integer Gaussian fields

**Scope.** A forward probability distribution on a fully specified integer
lattice with known rational precision matrix and center. The results concern
its coordinate-resampling contraction and forward normalizer; they do not
fit unknown inputs, address lattice search/decoding, or apply to any scheme.

For \(a>0\) and \(c\in\mathbb R\), let \(D_{a,c}\) have law proportional
to \(e^{-a(x-c)^2}\) on \(\mathbb Z\), and write \(M_a(c)=\mathbb E_{D_{a,c}}X\).
Circular distances below are on \(\mathbb R/\mathbb Z\), with circumference one.
For the field
\[
 \pi_{Q,\mu}(x)=Z^{-1}e^{-(x-\mu)^\top Q(x-\mu)},\qquad
 x\in\mathbb Z^n,\quad Q=Q^\top\succ0,
\]
put \(a_i=Q_{ii}\), \(r_{ij}=-Q_{ij}/Q_{ii}\) for \(j\ne i\),
and \(\alpha_i=\mu_i-\sum_{j\ne i}r_{ij}\mu_j\).
The conditional at coordinate \(i\) is \(D_{a_i,\alpha_i+\sum r_{ij}x_j}\).

**Theorem.** For rational \(Q,\mu\), let \(D_i\) be the least common multiple
of the reduced denominators of \(r_{ij}\) for \(j\ne i\), using \(1\) for the
empty list. For \(i\ne j\), write \(|r_{ij}|=\ell+u\) with \(\ell\) a nonnegative
integer and \(0\le u<1\). Pick \(c_*\in\alpha_i+D_i^{-1}\mathbb Z\) such that
\(c_*+u/2\) is closest to \(1/2\) in circular distance. The best constant in
\[
 W_1\bigl(\pi_i(\cdot\mid x_{-i}),\pi_i(\cdot\mid y_{-i})\bigr)
       \le C_{ij}|x_j-y_j|
\]
over integer contexts differing only at \(j\) is
\[
                          C_{ij}=\ell+M_{a_i}(c_*+u)-M_{a_i}(c_*).       \tag{1}
\]
It can be evaluated to \(b\) absolute precision bits in deterministic time
polynomial in the rational input length and \(b\), without a scan of size
\(D_i\) or of \(|r_{ij}|\).

Set \(C_{ii}=0\). A supplied positive rational vector \(v\) with
\(Cv\le(1-\gamma)v\), for \(0<\gamma\le1\), certifies a factor \(1-\gamma\)
per full coordinate sweep. In particular there is a randomized forward
approximation of \(\pi_{Q,\mu}\) with total variation error \(\epsilon\)
in time polynomial in the input bit length (including \(v,\gamma\)),
\(1/\gamma\), and \(\log(1/\epsilon)\). A rational witness can also be
found in polynomial bit time given a promised inverse spectral gap
\(\rho(C)\le1-\gamma\), with a factor \(1-\gamma/2\) per sweep.
With \(\mu=0\), a lower spectral bound
\(\lambda I\preceq Q\) gives a randomized relative approximation of \(Z\),
with constant confidence, in time polynomial also in \(1/\epsilon\) and
\(1/\lambda\). These are sufficient conditions for the stated forward tasks,
not necessary mixing conditions.

**Separation.** For every simple 3-regular graph, even with arbitrary signs
on edges, take \(Q_{ii}=3\), \(Q_{ij}=\pm 3/4\) on edges, zero otherwise,
and \(\mu=0\). The exact matrix \(C\) has spectral radius \(<99/100\), while
the matrix of best pairwise coefficients over *unrestricted real phases*
has spectral radius \(>1\). Positive diagonal reweighting cannot rescue
the latter test. This gap is not merely an improvement over a derivative
upper bound. The graph can have unbounded treewidth.

## 1. The moving-window lemma for one coordinate

For \(c<d\) the likelihood ratio of \(D_{a,d}\) to \(D_{a,c}\) is a positive
constant times \(e^{2a(d-c)x}\). Thus the former stochastically dominates
the latter. The monotone quantile coupling and the linear test \(x\mapsto x\)
give \(W_1(D_{a,d},D_{a,c})=M_a(d)-M_a(c)\). Reflection gives
\(M_a(1-c)=1-M_a(c)\), and \(M_a(c+1)=M_a(c)+1\).

In fact \(M_a'(c)\) is a continuous, strictly circularly decreasing density
away from the point \(1/2\). To see this, put \(h=\pi^2/a\) and \(q=e^{-h}\).
Poisson summation and the Jacobi product give the normalizer
\(Z_a(c)=\sqrt{\pi/a}\,\vartheta_3(\pi c,q)\) and
\(M_a(c)=c+(\log Z_a)'(c)/(2a)\). The \(c\)-dependent portion of \(\log Z_a\)
is \(\sum_{j\ge1}\log(1+2q^{2j-1}\cos(2\pi c)+q^{4j-2})\).
Expand each logarithm and differentiate twice, using absolute convergence
for fixed \(a\). The result is
\[
 M_a'(c)=1+2\sum_{k\ge1}\frac{hk}{\sinh(hk)}
                     \cos(2\pi k(c-\tfrac12)).                        \tag{2}
\]

Here is a real-variable way to see strict radial decrease in (2). Euler's
product for \(\sinh\) writes the Fourier coefficient as
\[
 \frac{hk}{\sinh(hk)}
        =\prod_{j\ge1}(1+(hk/(\pi j))^2)^{-1}.
\]
Each factor is the Fourier coefficient of a periodized two-sided exponential
density, proportional on \([-1/2,1/2]\) to
\(\cosh(\beta(1/2-|x|))\), with \(\beta=2\pi^2j/h>0\).
These are even and strictly decreasing on \(0<x<1/2\).
Convolution preserves the even decreasing property: convolution with the
indicator of a centered arc of radius \(t\in(0,1/2)\) has derivative
\(f(x+t)-f(x-t)\le0\) for \(0<x<1/2\), since the circular distance of
\(x+t\) is larger than that of \(x-t\). Use the layer-cake formula for the
other density. For strictness, separate the first exponential kernel.
The remaining product gives an even nonincreasing, nonconstant density:
partial convolutions converge uniformly by the summable Fourier
coefficients of the second factor, and the first nontrivial coefficient
of the remaining product is positive. Its layer cake includes
nonempty, proper arcs for a positive measure of levels. Convolution with
the first, strictly decreasing factor is then strictly decreasing.

It follows that for \(0<u<1\), the function
\[
                       c\longmapsto M_a(c+u)-M_a(c)
\]
is strictly decreasing as the midpoint \(c+u/2\) moves in circular distance
away from \(1/2\). Indeed it is the integral of (2) on an arc of length \(u\),
and the same endpoint derivative argument applies. For \(u=0\) it vanishes.
For a longer displacement \(\ell+u\), the extra integer translates
contribute exactly \(\ell\), independent of \(c\).

## 2. What integer contexts can reach

The subgroup generated in the circle by all \(r_{ij}\) is
\(D_i^{-1}\mathbb Z/\mathbb Z\). Multiplying by \(D_i\), the resulting integer
numerators together with \(D_i\) have gcd one: at each prime dividing
\(D_i\), at least one denominator attains the full prime power, and its
numerator is coprime to that prime. All those phases are attained by some
integer context. A one-unit move of \(x_j\) with the appropriate sign
produces the positive displacement \(|r_{ij}|\) from any chosen context.
A move by many units telescopes along these one-unit steps, and cannot
raise their maximum ratio. Thus (2) and the moving-window lemma establish
the exact coefficient (1). Rounding the rational
\(D_i(1/2-\alpha_i-u/2)\) to the nearest integer selects \(c_*\);
a tie gives the same value. The denominators, rounding, and integer
part \(\ell\) all have polynomial binary length.

For numeric evaluation, first reduce \(c\) by a known integer translate.
For \(a\ge1\), recenter the primal sums at the nearest integer \(m\).
The relative weight for \(m+k\) is at most
\(e^{-|k|(|k|-1)}\), and the denominator is at least one.
Truncate \(O(b+1)\) terms on either side with certified exponentially
small error even for the first moment. For \(a<1\), use
\(c+(\log Z_a)'/(2a)\) with the Poisson Fourier series instead. Its
normalized denominator is bounded below by a positive absolute constant,
and the tail contains \(e^{-\pi^2 k^2/a}\); even accounting for the prefactor
\(1/a\), \(O(b+\operatorname{bits}(a)+1)\) terms suffice. Bounded-argument
trigonometric and exponential functions, and terms already below
requested tolerance, can be evaluated by Taylor intervals and range
reduction in polynomial bit time. In particular strict contraction
inequalities with a promised slack can be certified with upper numerical
intervals. Here is the precise witness argument. Given
\(\rho(C)\le 1-\gamma\), put \(\tau=1-\gamma/2\) and use, just in this proof,
\(w=(I-C/\tau)^{-1}\mathbf1\). Its entries are at least one by the
nonnegative Neumann series, and \(Cw=\tau(w-\mathbf1)\).
The entry bound \(C_{ij}\le |r_{ij}|+1\), the determinant bound
\(|\det(I-C/\tau)|\ge(\gamma/2)^n\), and the adjugate formula give a
known upper bound \(V\) on \(\|w\|_\infty\) of polynomial binary length.
Find a rational upper approximation \(\bar C\) entrywise within
\(\tau/(2nV)\). Then \(\bar Cw\le\tau w-(\tau/2)\mathbf1\), proving
\(\rho(\bar C)<\tau\) by a weighted row norm. Rational linear algebra
now yields the actual witness \(\bar v=(I-\bar C/\tau)^{-1}\mathbf1\),
which is positive and obeys \(C\bar v\le\tau\bar v\). This does not
require deciding equality at zero slack.

## 3. Forward computation under the certificate

Couple two copies with the same scan and monotone quantile coupling at
each update. Let \(e_i=\mathbb E|X_i-Y_i|\). Updating \(i\) leaves other
entries unchanged and sets its new entry to at most \(\sum_j C_{ij}e_j\)
by telescoping over positions and the optimal one-site coupling.
The maximum of \(e_i/v_i\) never increases; after a full sweep every
coordinate has been updated with the bound \(1-\gamma\) times its
pre-sweep maximum. Start one copy from the coordinatewise rounded center,
the other from stationarity (all exact update kernels preserve \(\pi\)).
For \(s\) sweeps the total variation error is at most
\[
        (1-\gamma)^s\left(\sum v_i\right)\max_i e_i^{(0)}/v_i.           \tag{3}
\]
The prefactor has logarithm at most polynomial in the bit input.
For example rational determinant bounds give a positive computable
\(\lambda_0\le\lambda_{\min}(Q)\) of polynomial binary length.
If \(E_0\) is the energy of the rounded center then \(Z\ge e^{-E_0}\);
for radius \(R\) the exterior probability is at most
\[
 e^{E_0-\lambda_0 R^2/2}
       (1+\sqrt{2\pi/\lambda_0})^n.
\]
Here the shifted one-dimensional sums are maximized at an integer by
Poisson summation and bounded by a zero term plus an integral. Choosing
\(R\) of polynomial binary length to absorb \(E_0\) and the normalizer,
and integrating the Gaussian bound beyond \(R\), proves the prefactor
claim even when precision numbers have large numerical range.

For completeness one conditional update can be approximated in time
polynomial in the bit length of \(a,c\) and \(\log(1/\nu)\), for error
\(\nu\), uniformly when the width is numerically large. Use the
integer \(L=\lceil\max(1,a^{-1/2})\rceil\) and nearest mode \(m\).
Propose a block \(k=0,1,\ldots\) with probability \(2^{-k-1}\), and
an integer uniformly in \(kL\le |x-m|<(k+1)L\). Relative to the mode's
unnormalized weight, every weight in block \(k\ge1\) is bounded by
\(e^{-k(k-1)}\), because \(aL^2\ge1\) and
\(|x-m|(|x-m|-1)\ge k(k-1)L^2\).
The weight in block \(0\) is at most \(1\). Thus \(8L\) times this
proposal density dominates the unnormalized weights.
If \(a\le1\), at least \(L\) integers with \(|x-m|\le L/2\) have
relative weight at least \(e^{-4}\), since \(aL^2\le4\); otherwise
the mode suffices and \(L=1\). Acceptance has absolute constant
lower bound. Capping proposal trials, geometric block indices,
and uniform-integer subtrials at suitable \(O(\log(1/\nu)+1)\),
and rounding each acceptance probability with enough bits, gives
error at most \(\nu\) by coupling. Under these caps the output length
increases by at most a polynomial input-dependent number of bits at
each update, since the next center is a fixed rational linear expression
in the previous states. Coupling the approximate and exact updates
over the polynomial number in (3) yields the claimed bit complexity.

For the centered normalizer, condition successive coordinates to equal
zero. Every conditional model is governed by a principal submatrix
of \(Q\), with the other coordinates fixed to zero. Its influence
coefficients cannot increase (the sets of contexts only shrink),
and the same certificate vector restricted to the remaining indices
suffices. For each coordinate being conditioned, its marginal odds
at \(k\) relative to zero are at most \(e^{-\lambda k^2}\). Complete
the square in the other coordinates: the Schur complement is at least
\(\lambda\), and the shifted residual Gaussian sum is maximized at
zero by Poisson summation with nonnegative Fourier coefficients.
Hence the coordinate zero probability is at least
\((1+\sqrt{\pi/\lambda})^{-1}\).
Estimate those \(n\) conditional zero probabilities to relative
accuracy \(O(\epsilon/n)\) by independent samples, using total
variation precision below a constant fraction of the required additive
precision. Standard bounded-variable concentration and a union bound
give constant confidence in all estimates simultaneously. Their product
estimates \(\pi_{Q,0}(0)=1/Z\); inversion gives the stated relative error.
This final normalizer statement needs a useful numerical lower bound
on \(\lambda\), whereas the forward law in (3) only uses its bit length.

## 4. Stiffness and the arithmetic gap

In the signed 3-regular example, \(Q\succeq(3/4)I\) by the row-sum bound.
Here \(D_i=4\) and \(\alpha_i=0\). For every edge the nearest midpoint
to \(1/2\) gives the interval \([1/4,1/2]\) or \([1/2,3/4]\).
Thus \(C_{ij}=1/2-M_3(1/4)\).
Unrestricted phases give the interval \([3/8,5/8]\), with coefficient
\(1-2M_3(3/8)\). These symmetric nonnegative matrices have spectral
radii three times their respective entries.

The strict inequalities \(M_3(1/4)>17/100\) and \(M_3(3/8)<1/3\) can be
checked with short rigorous bounds. At \(c=1/4\), use
\(w_k=e^{-3(k^2-k/2)}\). In
\(\sum_k(100k-17)w_k\) keep \(k=0,1\) and bound the negative side:
\[
 \sum_k(100k-17)w_k \ \ge\
             83e^{-3/2}-17-117e^{-9/2}
                 -\sum_{m\ge2}(100m+17)e^{-3(m^2+m/2)}>0.
\]
One may use \(e^{-3/2}>223/1000\), \(e^{-9/2}<112/10000\), and
the last tail \(<1/1000\) (start at \(217e^{-15}\) and compare
successive terms with a geometric ratio \(<1/50\)).
At \(c=3/8\), the sum
\(\sum_k(3k-1)e^{-3(k^2-3k/4)}\) is at most
\[
                   -1+2e^{-3/4}+\sum_{k\ge2}(3k-1)e^{-3(k^2-3k/4)}<0,
\]
using \(e^{-3/4}<473/1000\), \(e^{-15/2}<1/1600\), and the same
ratio bound for the tail starting at \(5e^{-15/2}\).
The exact finite inequalities are also reproduced in the verifier.
The unrestricted matrix has constant row sum \(>1\);
\(Av\le(1-\gamma)v\) for a positive \(v\) would contradict summing its
entries against the constant left eigenvector. The exact coefficient
matrix admits \(v=\mathbf 1,\gamma=1/100\).
The degree restriction does not bound width: replacing each vertex of
a square torus grid by a four-cycle with one old incident edge at each
port yields degree three and retains that grid as a minor.

The arithmetic effect has a sharp fixed-shape low-temperature limit.
If \(Q\) is scaled by \(t\to\infty\), the attainable grids and \(\ell,u\)
are unchanged, while \(M_{ta_i}(c)\) tends to the nearest integer,
or to \(c\) at a half integer. For \(u>0\), write \(u=k/D_i\).
If the half integer lies in the interior of an attainable arc of
length \(u\), (1) tends to \(\ell+1\). Otherwise it lies at an
endpoint of a best arc, giving \(\ell+1/2\).
The latter happens exactly if \(k=1\) and
\(1/2\in\alpha_i+D_i^{-1}\mathbb Z\): a nonaligned half integer
is strictly in some consecutive grid cell, and two or more grid
cells can straddle an aligned half integer. Integer displacements
keep their exact coefficient \(\ell\). This is a limit of the
coefficient criterion, not a necessary condition for actual mixing.

## Relation to prior work

Dobrushin contraction and coordinate Gibbs sampling are not new here.
[Dorlas and Savoie](https://arxiv.org/abs/2305.19371) develop
the one-site Wasserstein-distance criterion in general metric spaces.
[Wang, Ling, and Hanrot](https://arxiv.org/abs/1405.1623) introduce
lattice Gaussian Gibbs sampling; [Wang, 2019](https://seu-zheng-wang.github.io/Files/z-tcom-2019.pdf)
analyzes geometric convergence via forward-operator spectra.
Our additional ingredient is the exact attainable rational phase,
a finite bit certificate for its coefficient, and an explicit family
where the best continuous phase test cannot certify the same gap.
The analytic identity (2) uses classical
[Jacobi products](https://dlmf.nist.gov/20.5) and is also equivalent
to the familiar Fourier series for a squared elliptic function
([DLMF 22.11.13](https://dlmf.nist.gov/22.11.E13)
with \(1-k^2\mathrm{sn}^2=\mathrm{dn}^2\)).
Neither the theta identity itself nor the Markov chain framework is
claimed as novel.
