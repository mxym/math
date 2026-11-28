# Soft-constraint interpolation for bounded-width unimodular Gaussian sums

**Scope.** A centered forward integer Gaussian sum with all row forms
and weights supplied. There are no observations, unknown coefficients,
cryptographic targets, or inference tasks in the input.

Let \(M_0\in\mathbb Z^{m\times n}\) be a supplied totally unimodular
matrix, with rows \(\ell_j\). Let \(a_j\ge0\) be rational, and suppose
the form \(Q(x)=\sum_j a_j\ell_j(x)^2\) is positive definite.
In the primal graph, put an edge between two variables sharing any
nonzero row. A tree decomposition of this graph of fixed width \(w\)
is supplied.

**Theorem.** The centered sum
\[
                         Z=\sum_{x\in\mathbb Z^n}e^{-Q(x)}
\]
admits a deterministic relative \(2^{-P}\) approximation in time
polynomial in the binary input length and \(P\), with polynomial
exponent depending on \(w\). No numerical upper or lower bound on
the positive \(a_j\) is required. Row supports may have more than two
coordinates. The proof does not require the integer kernel to have
a basis respecting the tree decomposition. For instance, use rows that
sum consecutive windows of at most three coordinates on a path, together
with any unary rows making the energy positive definite. The transpose
has the consecutive-ones property in each column, so the matrix is totally
unimodular; the primal graph has width at most two. The weights of the
window rows may range over arbitrarily separated binary scales.

The useful mechanism is to sum over a bounded box of integer strong-row
residuals. Continuous Gaussian penalties keep each residual local
in the tree decomposition. An analytic extrapolation removes the
soft-constraint bias without taking a penalty of size \(2^P\).

## 1. Integral fibers and a uniformly broad kernel

Delete zero rows or weights. For \(n\ge1\), \(m\ge1\), put
\[
                      K=64(m+1)(n+1)^3(n+P+10).
\]
Call a row strong when \(a_j\ge1/K\), and let \(M\) be the matrix of
the \(s\) strong rows, \(W=\operatorname{im}_{\mathbb R}M\subseteq\mathbb R^s\)
and \(r=\operatorname{rank}M\). Write \(Q_w\) for the precision matrix
formed by the weak rows alone. Thus
\[
            Q(x)= \sum_{j\text{ strong}} a_j(Mx)_j^2+x^\top Q_w x .
\]
All entries of \(M_0\) are \(0,\pm1\). Therefore
\(\|Q_w\|_{\rm op}\le mn/K\).

Select independent row indices \(I\) and column indices \(J\) giving
an invertible \(r\times r\) minor \(B=M_{I,J}\).
By total unimodularity, \(\det B=\pm1\); entries of \(B^{-1}\) are
\(0,\pm1\). For any integer \(y\in W\), the vector \(x_J=B^{-1}y_I\)
with other coordinates zero is an integer solution of \(Mx=y\).
It solves all rows because every other row is a linear combination of
the selected rows. Consequently
\[
                           M\mathbb Z^n=W\cap\mathbb Z^s.        \tag{1}
\]
The integral kernel has a basis \(U\) obtained by setting one free
coordinate to one and the rest of the free coordinates to zero,
then solving its pivot coordinates with \(B\). Each entry of \(U\)
is \(0,\pm1\) by Cramer's rule: replaced-column determinants are
minors of \(M\). This is a basis over the integers because the free
coordinates are literal coordinates. In particular \(\|U\|_{\rm op}\le n\).

Let \(A_0=U^\top Q_w U\). It is positive definite on the kernel
coordinates, since the full form is positive definite and all strong
rows vanish there; also
\[
                            A_0\preceq(mn^3/K)I .
\]
Let \(C_0=\pi^{(n-r)/2}/\sqrt{\det A_0}\) and
\[
                       f(y)=\min_{Mx=y}x^\top Q_w x,\qquad y\in W .
\]
Use \(C_0=1\) in zero kernel dimension. On each integer fiber
substitute \(x=x_0+Uz\) with \(z\in\mathbb Z^{n-r}\) and complete the
square. Poisson summation bounds the relative difference between the
remaining shifted theta and \(C_0\) uniformly by
\[
       \sum_{v\in\mathbb Z^{n-r}\setminus\{0\}}
                       e^{-\pi^2 v^\top A_0^{-1}v}
                             <2^{-P-20}.
\]
Indeed compare it with the product of one-dimensional theta sums at
precision at least \(\pi^2 K/(mn^3)\), and bound each nonzero tail by
a geometric series. This inequality also holds in zero kernel
dimension, with zero remainder. Thus
\[
    Z/C_0=(1+\epsilon)\!
           \sum_{y\in W\cap\mathbb Z^s}e^{-\sum_j a_j y_j^2-f(y)},
                              \qquad |\epsilon|<2^{-P-20}.       \tag{2}
\]
An integral kernel basis is used for this estimate, not as an input
to graphical variable elimination.

The nonnegative quadratic form \(f\) on \(W\) is
\(f(y)=\langle y,Gy\rangle\) for a self-adjoint \(G\succeq0\) on the real
Euclidean space \(W\). Complete the square on the kernel to see it
is quadratic. The above feasible solution has norm at most \(n\|y\|\)
also for real \(y\in W\), so
\(f(y)\le(mn^3/K)\|y\|^2\); in particular \(\|G\|_{\rm op}\le1\).
Computing an orthonormal basis or diagonalizing \(G\) is not required.

## 2. Residual truncation and separation of infeasible integers

The sum in (2) contains the zero term. As all strong weights are
at least \(1/K\) and \(f\ge0\), the contribution outside a box
\(\|y\|_\infty\le R\) is at most
\[
             e^{-R^2/(2K)}(1+\sqrt{2\pi K})^s .
\]
Choose an integer \(R\) polynomial in \(K,s,P\) making this at most
\(2^{-P-20}\).

There is a uniform numerical gap from an infeasible integer residual
to \(W\). Each dependent row of \(M\) can be written in terms of the
rows in \(I\) with coefficients in \(\{0,1,-1\}\), using its restriction
to columns \(J\) and replaced-row determinants of \(B\).
Consequently \(W\) is given by equations \(y_j=\sum_{i\in I}b_{ji}y_i\)
for \(j\notin I\) with such coefficients. Any integer \(y\notin W\)
violates at least one by an integer of absolute value at least one.
The norm of that equation's normal is at most \(\sqrt{r+1}\), hence
\[
                   \operatorname{dist}(y,W)\ge1/\sqrt{r+1}.    \tag{3}
\]
The cases of an empty strong matrix or no dependent rows are
included: where there are no infeasible residuals the bound is
vacant. Empty-dimensional sums and determinants use their usual
value one.

## 3. Soft constrained node computation by mixed graphical elimination

For positive rational \(T\), define
\[
\begin{split}
 f_T(y)&=\min_{x\in\mathbb R^n}
                    \{x^\top Q_w x+T\|Mx-y\|^2\},\\
 H_T&=\sum_{\substack{y\in\mathbb Z^s\\\|y\|_\infty\le R}}
                     e^{-\sum_j a_j y_j^2-f_T(y)} .
\end{split}
\]
Let \(A_T=Q_w+T M^\top M\succ0\), and \(C_T=\pi^{n/2}/\sqrt{\det A_T}\).
Completing the square rewrites \(H_T\) as the finite sum over \(y\) of the
integrals over \(x\) of
\[
            \exp\{-x^\top Q_w x-\sum_j a_j y_j^2
                         -T\sum_j (\ell_j(x)-y_j)^2\}/C_T .      \tag{4}
\]
Here \(\ell_j\) in the residual factors refers to each strong row.
The variables \(x\) are continuous and \(y_j\) are finite-state.

The local factor of a strong row splits into a discrete factor
\(e^{-(a_j+T)y_j^2}\), a common Gaussian factor
\(e^{-T\ell_j(x)^2}\), and a cross factor \(e^{2T y_j\ell_j(x)}\).
Weak factors are common Gaussian factors.
The row support of an original form is a clique and hence is
contained in a tree-decomposition bag. Attach a leaf bag consisting
of that support and \(y_j\) for each strong row. The new width is at
most \(w+1\), even if many rows originally use one bag.

By one formal scalar \(t\) on all cross factors, the Gaussian moment
factor integrated for each \(y\) equals \(e^{t^2 u_T(y)}\), where
\[
 u_T(y)=T^2 y^\top M A_T^{-1}M^\top y,\qquad
 0\le u_T(y)\le T\|y\|^2\le T s R^2 .
\]
The upper bound follows from \(f_T(y)=T\|y\|^2-u_T(y)\ge0\).
If \(T\) is at most polynomial numerically, the upper bound is
polynomial numerically in \(n,m,R,T\).

Use the mixed polynomial-elimination argument in
[Strong-component Poisson elimination, §§3–4](https://github.com/mxym/math/blob/1e5e70eafeb602db9527f926f72fa602a572fe77/research/euclidean-tensor-geometry/theoretical-cryptography/multiscale-sparse-gaussian-elimination.md):
multiply the local Taylor factors modulo one globally bounded
degree of \(t\). Every message is a common Gaussian on its remaining
continuous coordinates times a polynomial in \(t\) and those coordinates,
tabulated over its remaining finite states.
A continuous elimination uses rational shifted Gaussian moments,
with the pivot scalar \(\sqrt{\pi/a}\) factored out; the product of
these scalars is exactly \(C_T\), so the polynomial result already
computes (4) divided by \(C_T\). A discrete elimination sums the
finite tables with their common Gaussian unchanged.
The number of monomials per bag is polynomial at fixed width because
the degree in live continuous variables never exceeds the formal degree.
All subtraction and cancellation occurs in rational arithmetic after
rounding the local discrete weights.

In particular \(H_T\) can be computed to an arbitrary \(2^{-L}\)
absolute tolerance in polynomial binary time in the input,
\(R,T,L\), with \(R,T\) regarded as numerical bounds in this step.
For precision bookkeeping choose the formal degree to make
\(T_J(u)\) approximate \(e^u\) relatively within
\(2^{-L-2}/(2R+1)^s\) on \([0,T sR^2]\); a degree polynomial in
\(T sR^2+L+s\log(2R+1)\) is enough by the factorial tail bound.
Every full term in \(H_T\) is at most one, giving the required
absolute tail error. Round each discrete factor within
\(2^{-L-2}/[m(2R+1)^s e^{T sR^2}]\); the remaining error bound is
again obtained term by term since all products are nonnegative
after the integrated Taylor evaluation. As in the cited argument,
conditional Gaussian moments use Schur coefficients with polynomial
bit length, and coefficient denominators and numerator magnitudes
stay of polynomial bit length. No powers of an exponentially
large numerical \(T\) are needed below.

## 4. Extrapolation removes the penalty bias at bit precision

On a feasible \(y\in W\), minimization over \(v=Mx\) gives exactly
\[
 f_T(y)=\min_{v\in W}(f(v)+T\|v-y\|^2)
        =\langle y,G(I+G/T)^{-1}y\rangle .                       \tag{5}
\]
Diagonalizing the real nonnegative form \(G\) verifies the last equality.
For infeasible integer \(y\), (3) gives \(f_T(y)\ge T/(r+1)\).
Thus the node computation \(H_T\) differs from the feasible-only
sum using (5) by at most
\[
                           (2R+1)^s e^{-T/(r+1)} .               \tag{6}
\]

Define the analytic function on the complex disk \(|h|\le1/2\)
\[
 F(h)=\sum_{\substack{y\in W\cap\mathbb Z^s\\\|y\|_\infty\le R}}
       \exp\{-\sum_j a_jy_j^2-\langle y,G(I+hG)^{-1}y\rangle\}.
\]
The quadratic expression here is its analytic continuation for real
\(y,G\). By \(\|G\|\le1\), the operator norm of \(G(I+hG)^{-1}\)
is at most two there. Hence
\[
 |F(h)|\le (2R+1)^s e^{2sR^2}\le 2^q,\quad
 q=s\lceil\log_2(2R+1)\rceil+4sR^2 .
\]
It is analytic on a neighborhood of the closed disk, and
\(F(0)\) is exactly the feasible-box contribution needed in (2).

Set \(D=q+P+20\) and let
\[
  \eta=\bigl[64(r+1)(q+P+4D+20)\bigr]^{-1},\qquad
  h_j=\eta(1+j/D),\quad 0\le j\le D .
\]
Interpolate using \(H_{1/h_j}\) at these distinct nodes,
with value sought at zero.
For the exact values \(F(h_j)\) the interpolation error at zero
is at most
\[
         2^q\left(\frac{2\eta}{1/2-2\eta}\right)^{D+1}
                                      <2^{-P-20}.
\]
This is the Cauchy contour remainder, since the product of the
distances from zero to the nodes is at most \((2\eta)^{D+1}\)
and on \(|h|=1/2\) every distance to a node is at least
\(1/2-2\eta\). The sum of absolute values of the evaluation weights
is at most \((4e)^D<2^{4D}\): each term is bounded by
\((2D)^D/[j!(D-j)!]\) from the equal-spacing formula and the
sum is \((4D)^D/D!\).

At each node \(T=1/h_j\) is polynomial numerically, and is at least
\(32(r+1)(q+P+4D+20)\). Thus (6) is below
\(2^{-(P+4D+20)}\), even after accounting for all infeasible
box points. Compute \(H_T\) to that same absolute accuracy.
The weighted sum of the two types of node error is
at most \(2^{-P-19}\). All interpolation weights are rationals of
polynomial bit length, directly from the Lagrange formula.
This gives \(F(0)\) within a small constant multiple of \(2^{-P-20}\),
with no inverse-accuracy numerical penalty. The exact sum in
(2) is at least one; the box tail, uniform fiber error, and
extrapolation errors remain well inside relative \(2^{-P}\).
The scalar \(C_0\) needs only a relative approximation of that
precision, computable using its rational Gram determinant and
ordinary elementary arithmetic in polynomial bit time.
This completes the proof.

## Comparison with prior work

[Barvinok, *Computing the Theta Series*, §5](https://www.theoryofcomputing.org/articles/v022a009/v022a009.pdf)
also uses soft quadratic penalties in comparing Gaussian sums on a
subspace, with spectral hypotheses for its computational guarantees.
We use a different soft step, a mixed real integral indexed by finite
integer residuals. The bit-precision extrapolation, integral image
saturation and infeasible-residual gap, plus bounded-width local
node evaluation, are the structural additions.
The [strong signed graph theorem](https://github.com/mxym/math/blob/1e5e70eafeb602db9527f926f72fa602a572fe77/research/euclidean-tensor-geometry/theoretical-cryptography/multiscale-sparse-gaussian-elimination.md)
already handles frustrated signed edges not promised unimodular;
we reuse its mixed Taylor machinery, not its signed-component
parameterization. This note adds genuine multi-coordinate
totally unimodular forms, not arbitrary matrices with general minors.
No inference or worst-case lattice search conclusion is asserted.
