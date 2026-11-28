# Strong-component Poisson elimination for sparse integer Gaussian fields

**Scope.** A fully specified centered forward Gaussian law on integer
coordinates. The entire precision form is part of the input. Nothing
is inferred from observations or unknown coefficients, and no
cryptographic instance or implementation is analyzed.

Let \(G\) be a loop-free signed graph with rational nonnegative unary and
edge weights. Write its energy as
\[
 {\cal E}(x)=\sum_i a_i x_i^2+
                   \sum_{e=ij}w_e(x_i-\sigma_e x_j)^2,\quad
                   \sigma_e\in\{1,-1\}.
\]
Terms of weight zero can be removed. Assume \({\cal E}\) is positive
definite and a tree decomposition of width at most \(w\) is supplied.

**Theorem.** For fixed \(w\), there is a deterministic algorithm whose
bit cost is polynomial in the complete input length and the requested
precision \(P\), with output a relative \(2^{-P}\) approximation to
\[
                            Z=\sum_{x\in\mathbb Z^n}e^{-{\cal E}(x)} .
\]
There is no numerical lower or upper bound on positive weights, no
condition-number bound, and no bound on the number of weak modes or
on their coupling rank. The treewidth is the original graph's width,
not the treewidth of a dense Schur complement.

For example, on a cyclic coordinate set with a fixed interaction
bandwidth \(b\), the graph has bounded width. One may use positive or
negative edge signs, including those obtained from the signed dyadic
shift \(T e_i=e_{i+1}\) with \(T e_{n-1}=-e_0\), in energies with
terms \(w_h\|x-T^h x\|^2\), \(h\le b\). The weights may also vary with
the site. This is a statement about these supplied quadratic forms;
it says nothing about generic noisy linear problems.

Even a tree can produce the dense, full-rank correction in this theorem.
Take a path of roots, attach one strong unit-weight leaf edge to each root,
and place weak weight \(b_0\in(0,1/K)\) on every root-path edge and every leaf
pin. Choose the path vertices as free-component roots. In the coordinates
below the \(z\)-precision is \(b_0(I+L_{\rm path})\), where \(L_{\rm path}\)
is the ordinary graph Laplacian, and the cross block is \(b_0 I\).
Thus the correction is \(b_0(I+L_{\rm path})^{-1}\), full rank with
all entries strictly positive. Indeed write \(I+L_{\rm path}=D-A_{\rm path}\)
with \(D_{ii}=1+\deg(i)\), and use the nonnegative Neumann series for
\((I-D^{-1}A_{\rm path})^{-1}\); path connectivity gives a positive term
for every entry. Deleting the roots by simply forming a finite discrete
Schur graph would make it complete.

## 1. Split broad coordinates using strong graph components

Let \(m\ge1\) be the number of nonzero forms (unary or edge) and let
\(n\ge1\). Put \(K=64(m+1)(n+P+10)\). Call a form strong if its weight
is at least \(1/K\), weak otherwise. The strong graph is the graph of
strong edge forms, retaining isolated vertices. A strong component is
free if it has no strong unary pin and all its cycles have sign product
\(+1\). Then there are signs \(\tau_i\) on that component such that
\(\tau_i=\sigma_e\tau_j\) on every strong internal edge. Choose a
root in each free component with \(\tau_{\rm root}=1\).
Set
\[
                   x_i=y_i+\tau_i z_C
\]
on a free component \(C\), with \(y_{\rm root}=0\), and set \(x_i=y_i\)
on other components. The free-component roots supply the \(r\)
coordinates \(z_C\). All other vertices supply the \(n-r\) coordinates
of \(y\). This is an integral bijection with integral inverse
\(z_C=x_{\rm root}\), \(y_i=x_i-\tau_i x_{\rm root}\).
The \(z\)-part of every strong form vanishes.
Components, signs, and roots can be found by a spanning-tree traversal.

In the resulting coordinates write
\[
 {\cal E}=y^\top B y+2 z^\top L y+z^\top A z .
\]
If \(r>0\), \(A\succ0\). Its contributions come only from weak forms.
The \(z\)-coefficient vector of a weak form has Euclidean norm at most
two: it has at most two signed unit contributions, possibly to the
same coordinate. Consequently
\[
                        A\preceq (4m/K)I.                       \tag{1}
\]
Let \(B_s\) be the contribution to \(B\) from the strong forms.
On the \(y\)-space,
\[
                        B_s\succeq (4Kn^2)^{-1} I.              \tag{2}
\]
To check this, follow signed paths in a strong component. In a free
component the root \(y\)-coordinate is zero, so the absolute value at
any other vertex is at most the sum of absolute edge forms along a
path to that root. In a pinned component use a strong unary value as
the starting point. In an unpinned but unbalanced component, a negative
cycle of length at most \(n\) gives \(2|y_i|\le\sum_{\rm cycle}|\ell_e(y)|\)
at one of its vertices by telescoping (use a fundamental cycle with
negative sign product). Then use a path from that vertex.
Cauchy–Schwarz and \((u+v)^2\le2u^2+2v^2\) give
\(|y_i|^2\le4n\sum_{\rm component}\ell^2\) in all three cases, where the
sum is over the unweighted strong forms. Sum these inequalities and
use the minimum strong weight.

Completing the square in the continuous variables \(z\) gives
\[
  S=B-L^\top A^{-1}L,\qquad u(y)=y^\top L^\top A^{-1}L y .
\]
Use the conventions \(u=0\), \(S=B\), and determinant prefactor one
when \(r=0\). The weak energy is nonnegative for every real \(y,z\).
Minimization over \(z\), with the strong part independent of \(z\),
proves \(S\succeq B_s\) and
\[
                            0\le u(y)\le y^\top(B-B_s)y.         \tag{3}
\]

## 2. Uniform Poisson approximation and a finite box

For each fixed \(y\), Poisson summation on the shifted \(z\)-lattice
gives
\[
 \sum_{z\in\mathbb Z^r}e^{-{\cal E}(y,z)}
    =C\,e^{-y^\top S y}(1+\epsilon_y),\qquad
 C=\pi^{r/2}/\sqrt{\det A},
\]
where \(|\epsilon_y|\le\sum_{v\in\mathbb Z^r\setminus\{0\}}
e^{-\pi^2 v^\top A^{-1}v}\). By (1) this is at most
\[
   \left(1+\frac{2e^{-\pi^2K/(4m)}}{1-e^{-\pi^2K/(4m)}}\right)^r-1
                        \ <\ 2^{-P-10}.
\]
The bound is uniform over all shifts, with no loss proportional to
the range of \(z\). Thus \(Z/C\) is approximated relatively by the
theta sum on \(S\).

Write \(\kappa=(4Kn^2)^{-1}\). Restrict the \(y\)-space to
\(\|y\|_\infty\le R\) for an integer \(R\) polynomial in \(n,m,P\).
To see that one can choose it, use (2)–(3) and
\[
 \sum_{\|y\|_\infty>R}e^{-y^\top S y}
      \le e^{-\kappa R^2/2}(1+\sqrt{2\pi/\kappa})^n .
\]
Since the quotient theta contains its zero term, making this bound
at most \(2^{-P-10}\) also bounds the relative loss.
The remaining problem is a finite-box sum of
\(e^{-y^\top B y} e^{u(y)}\). Although \(B\) has the original sparse
description with roots fixed to zero, \(u(y)\) can be dense and have
growing rank. Direct use of the dense Schur matrix is not required.

## 3. One formal variable for an arbitrary number of coupled weak modes

On the box, (3) implies the numerical bound
\(u(y)\le U=4mR^2\):
each weak form on \(y\) has size at most \(2R\) and weight \(<1\).
Choose an integer \(J\ge 8(U+P+10)\).
The polynomial \(T_J(s)=\sum_{h=0}^J s^h/h!\) differs from \(e^s\)
by relative at most \(2^{-P-10}\) for all \(0\le s\le U\)
(e.g. use \(h!\ge(h/e)^h\) for the tail). We need
\[
            \sum_{\|y\|_\infty\le R}e^{-y^\top B y}T_J(u(y)).    \tag{4}
\]
Rather than represent all pairwise interactions of \(u\),
put one formal scalar \(\xi\) on every bilinear cross term.
Using a centered continuous Gaussian with precision \(A\),
\[
 \frac1C \int_{\mathbb R^r} e^{-z^\top A z}e^{-2\xi z^\top L y}\,dz
                      = e^{\xi^2 u(y)} .                        \tag{5}
\]
Use equality of Taylor coefficients through total \(\xi\)-degree \(2J\).
The coefficient on the left at degree \(j\) is an integral of a
polynomial of degree \(j\) in the continuous variables, against the
common Gaussian. Evaluating the truncated result at \(\xi=1\)
gives exactly \(T_J(u(y))\).

Here is how to compute those coefficients without a state for all \(z\).
For each original bag, augment it by \(z_C\) whenever it contains a
vertex in a free strong component \(C\), retaining only non-root
discrete \(y\)-coordinates there. Each new variable appears in a connected
set of bags: its appearances are the union of the original bag
subtrees for vertices of a connected component, and subtrees for
endpoints of an edge intersect. The augmented width is at most
\(2(w+1)-1\). Each original factor after the substitution has all of
its remaining variables in an augmented bag. For the contribution
\(a\bigl(\ell(y)+\ell(z)\bigr)^2\) attach the three factors
\[
 e^{-a\ell(y)^2},\quad e^{-a\ell(z)^2},\quad
      \sum_{j=0}^{2J}\frac{(-2a\xi\,\ell(y)\ell(z))^j}{j!},
\]
where \(a\) is its weight and each of the two linear forms is local.

Use bounded-width variable elimination derived from the augmented
decomposition (take a leaf-bag-only variable, and remove bags
contained in neighbors to continue). In a bucket, factors are of
the form a common Gaussian in the live continuous variables times a
polynomial in \(\xi\) and those variables, with the coefficients
tabulated for the live discrete values. The Gaussian factor is
independent of all discrete values and of \(\xi\).
Products and sums are done modulo \(\xi^{2J+1}\), which commutes
with all coefficientwise integrations. When a discrete variable
is eliminated, sum its polynomial tables while retaining their common
Gaussian. When a continuous variable \(z_i\) is eliminated, the pure
Gaussian part involving it is
\[
 e^{-a z_i^2-2z_i b^\top z_{\rm rest}}
\]
times a Gaussian in \(z_{\rm rest}\), where the leading coefficient
\(a>0\) follows from the Schur complements of \(A\).
Complete the square, producing a new common quadratic part
and scalar \(\sqrt{\pi/a}\). In the polynomial, replace \(z_i\) by a
centered Gaussian of variance \(1/(2a)\) minus \(b^\top z_{\rm rest}/a\).
Calculate each moment by the binomial formula and the rational
even moments \((2h-1)!!/(2a)^h\), with odd centered moments zero.
The product of the scalar normalization factors is exactly \(C\);
it can be tracked separately. This integration reduces or preserves
the total continuous degree of each coefficient.
The two cases preserve the induction on factor types and add no
variables outside the elimination bag.

At degree \(j\) the continuous polynomial always has degree at most \(j\).
Thus each bag needs only polynomially many coefficients for fixed
augmented width and degree \(2J\), and polynomially many discrete box
assignments. Both sums and polynomial multiplications are ordinary
finite table operations. This proves a polynomial count of algebraic
operations, without either a rank restriction or a discretization
of the broad variables.

## 4. Exact algebra and bit accounting

To execute (4), round the tabulated discrete exponential factors
to nonnegative dyadics in \([0,1]\), with absolute error at most
\(\delta\) per factor. Leave all rational cross factors and all
rational Gaussian moment identities exact.
For each fixed \(y\) the final result after integration and truncation
divided by \(C\) is exactly the product of the rounded discrete
factors times \(T_J(u(y))\). The error of that product is at most
\(m\delta\); the latter polynomial is between \(1\) and \(e^U\).
There are at most \((2R+1)^n\) box points. Hence it suffices to take
\[
                    \delta\le \frac{2^{-P-10}}{
                                       m(2R+1)^n e^U}.
\]
Its number of precision bits is polynomial in \(n,m,P\).
The exponents of very stiff discrete factors need not be expanded:
if too negative they can be rounded to zero, while bounded ones
are evaluated with elementary interval arithmetic.

The Gaussian precision updates are rational Schur complements of
\(A\), of polynomial bit length by minors; equivalently compute them
from the exact elimination pivots. Precompute the rational
conditional-moment substitution maps for degrees at most \(2J\);
their coefficients have polynomial bit length by the displayed
moment and shift formulas. All the local truncated polynomials and
the rounded weights have polynomial bit-length coefficients.
For a detailed bound on the message coefficients, take a common
denominator for these finite local data and all the conditional-moment
maps. Its bit length is polynomial, since there are polynomially many
such entries. In an expanded contribution to any message, each original
factor and each eliminated-variable map is used at most once: a bucket
consumes its current factors and creates one new factor, so their
sets of ancestors are disjoint. The number of multiplicative
coefficient entries in one such contribution is at most \(m+n\),
and the number of possible choices per operation is polynomial
(a convolution index, a conditional-moment term, or a discrete
assignment). Thus all numerators and denominators of the message
coefficients have polynomial bit length, even when signed intermediate
terms cancel. This is an exact rational computation after the single
local rounding step. The scalar \(C\) has polynomial-size logarithm
by rational determinant bounds and is approximated relatively with
polynomially many bits.

Finally the quotient theta and the finite polynomial expression with
unrounded weights both contain the zero contribution. The absolute
box and rounding errors are therefore also relative errors at the
requested scale, and the Poisson, truncation, scaling, and rounding
bounds combine to less than \(2^{-P}\). All cut selection,
component contractions, and bag augmentations are explicit.
For a circular graph of bandwidth \(b\), keep the first \(b\)
vertices in every bag and slide a window of \(b+1\) over the rest;
the width is at most \(2b\), since only arcs touching the fixed
initial vertices can cross the cut. This establishes the application.

## Comparison with prior work

[Barvinok, *Computing the Theta Series*](https://www.theoryofcomputing.org/articles/v022a009/v022a009.pdf)
gives randomized integration under spectral hypotheses.
Common Gaussian elimination is standard in graphical models
([Malioutov–Johnson–Willsky](https://jmlr.csail.mit.edu/papers/volume7/malioutov06a/malioutov06a.pdf));
truncated generating functions are standard for finite message-passing
moments ([Ilić et al.](https://doi.org/10.3934/amc.2012.6.363)).
The earlier [stiff signed graph cutoff](https://github.com/mxym/math/blob/c29f1f2f92fcbf9c528b354a1a7bb2a3013d2de3/research/euclidean-tensor-geometry/theoretical-cryptography/stiff-signed-graph-gaussian-cutoff.md)
truncates directly with a useful numerical stiffness lower bound.
The additional ingredient here is an integral broad-mode split
whose bag augmentation preserves width, followed by a common Gaussian
integration of one globally truncated formal variable. This handles
arbitrarily weak positive weights without requiring a sparse or
low-rank dense Schur complement. It is a normalizer computation on
the stated forward class only; no inference or hardness claim is made.
