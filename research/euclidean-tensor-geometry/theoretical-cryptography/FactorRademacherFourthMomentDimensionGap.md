# Exact fourth moments for rectangular Rademacher series and the three-unitary dimension gap

For same-size rectangular matrices \(A_1,\ldots,A_m\) over \(\mathbb R\)
or \(\mathbb C\), let \(X=\sum_i\varepsilon_i A_i\), with independent
uniform signs, and use the unnormalized trace and Schatten norms.
Put
\[
 \begin{aligned}
 S&=\sum_i A_i^\ast A_i,& T&=\sum_i A_iA_i^\ast,\\
 M&=\max\{\|S\|_F^2,\|T\|_F^2\},&
 L&=\min\{\|S\|_F^2,\|T\|_F^2\},\\
 D&=\sum_i\|A_i^\ast A_i\|_F^2,&
 J&=\mathbb E\|X\|_{S_4}^4 .
 \end{aligned}
\]
The following are finite fourth-moment claims. They do not assert
optimality for other Schatten exponents or for operator-norm
concentration. For comparison, [Buchholz's Theorem 5](https://www.impan.pl/shop/publication/transaction/download/product/85635)
gives the uniform fourth-power upper constant 3 as the number of
summands varies. We retain the finite number and both covariance
energies, then consider a dimension-sensitive sharp lower bound.

**Theorem 1 (exact rectangular envelope).** Every such tuple satisfies
\[
 D\le L\le M\le mD,\qquad M\le J\le M+2L-2D.
\tag{1}
\]
Conversely, for each fixed \(m\ge1\), every quadruple of nonnegative
reals satisfying (1) occurs in finite rectangular matrix dimensions,
over either field. If necessary replace all \(A_i\) by their adjoints
so that \(M=\|S\|_F^2\). In this orientation the two endpoint gaps are
exact sums of squares:
\[
 \begin{split}
 J-M&=\sum_{i<j}\|A_i^\ast A_j+A_j^\ast A_i\|_F^2,\\
 M+2L-2D-J&=\sum_{i<j}\|A_i^\ast A_j-A_j^\ast A_i\|_F^2.
 \end{split}
\tag{2}
\]
In particular, the sharp upper constant for fixed m is
\(J\le (3-2/m)M\).

**Theorem 2 (exact three-unitary minima).** For three unitary
matrices over \(\mathbb C\), or three orthogonal matrices over
\(\mathbb R\), of any fixed size \(d\ge1\), the minimum of J is
\(9d+\delta(d)\), where
\[
\begin{array}{c|c|c}
\text{field}&\text{dimension}&\delta(d)\\ \hline
\mathbb C&d\text{ even}&0\\
\mathbb C&d\text{ odd}&3\\ \hline
\mathbb R&d\equiv0\pmod4&0\\
\mathbb R&d\equiv2\pmod4&6\\
\mathbb R&d\text{ odd}&12
\end{array}
\tag{3}
\]
For complex odd d every minimizer, after a common left unitary
factor, individual sign changes, and a common orthonormal basis
choice, has one scalar line with phases
\(1,e^{i\pi/3},e^{2i\pi/3}\) (up to swapping the latter two)
and a remaining exact Clifford part. For real \(d\equiv2\bmod4\)
the corresponding statement holds with a common real
two-plane of rotations \(0,\pi/3,2\pi/3\), up to choice of
orientation and the same equivalences. No uniqueness is asserted
for real odd dimensions.

## 1. Rectangular proof and all attainable data

The pair characters \(\varepsilon_i\varepsilon_j\), \(i<j\), are
orthonormal and mean zero. Expanding \(X^\ast X\) in them and taking
squared Frobenius norms gives the first equation in (2).
For \(W=A_i^\ast A_j\),
\[
 \|W+W^\ast\|_F^2+\|W-W^\ast\|_F^2=4\|W\|_F^2.
\]
Also
\(\sum_{i,j}\|A_i^\ast A_j\|_F^2=\|T\|_F^2\), with diagonal
contribution D. This gives the second equation. Both sides obey
\(D\le\|S\|_F^2,\|T\|_F^2\le mD\): the lower bound uses the
nonnegative trace product of positive semidefinite summands,
the upper Cauchy–Schwarz in the Frobenius Hilbert space.
Here \(\|A_i^\ast A_i\|_F^2=\|A_i A_i^\ast\|_F^2\).

For attainability assume \(D=1\) by scaling (the zero case is
trivial). The feasible \((M,L)\) triangle has vertices
\((1,1),(m,1),(m,m)\), and in the following examples the orientation
\(\|S\|_F^2=M\) is uniform.

* At \((1,1)\) take just one nonzero coefficient, a real scalar 1.
* At \((m,1)\) take the \(m\) orthogonal unit coordinate columns
  scaled by \(m^{-1/4}\), with a common one-dimensional domain.
  Here the endpoints coincide.
* At \((m,m)\) all equal scalar coefficients \(m^{-1/4}\) attain
  the upper endpoint. For the lower endpoint use unitary
  \(U_1=I\), and \(m-1\) mutually anticommuting skew-Hermitian
  unitaries \(U_2,\ldots,U_m\). Then
  \(U_i^\ast U_j+U_j^\ast U_i=0\) for all \(i\ne j\).
  Such families exist in a finite complex dimension via Pauli
  matrices: for \(r=\lfloor(m-1)/2\rfloor\), on \(r\) tensor factors
  use \(Z^{\otimes(j-1)}\otimes X\otimes I^{\otimes(r-j)}\) and
  the same with \(Y\), \(j=1,\ldots,r\), and if needed
  \(Z^{\otimes r}\), and multiply by \(i\). Realification gives
  finite real orthogonal families with the same relations.
  In dimension d rescale by \((md)^{-1/4}\) to give \(D=1\).

For direct sums the four squared energies
\((\|S\|_F^2,\|T\|_F^2,D,J)\) add, and scaling the coefficients by
\(w^{1/4}\) multiplies all four by w. Thus direct sums realize convex
combinations of the displayed vertices, independently at either
endpoint, preserving the orientation \(M=\|S\|_F^2\).
Mix the two endpoint realizations at the same \((M,L,D)\) to
get the entire interval, then scale to general D.

For completeness the equality condition at \(J=(3-2/m)M>0\)
is rigid. Both covariances must have energy M, all
\(A_i^\ast A_i=P^2\) and \(A_iA_i^\ast=Q^2\) must agree on their
respective sides, and all relative overlaps on the chosen side
must be self-adjoint by (2). On the common support write
\(A_i=U_iP\) and set \(W_i=U_1^\ast U_i\). The equality of the
output covariances makes \(W_i\) commute with P; self-adjointness
of \(A_1^\ast A_i\) makes \(W_i\) self-adjoint, and
self-adjointness of \(A_i^\ast A_j\) makes the \(W_i\) pairwise
commute. Conversely these properties give equality. Thus on
the nonzero singular support the equality tuple consists of
the same singular values and arbitrary sign choices in a common
singular basis, up to a simultaneous left and right isometry.
All zero directions can be omitted.

## 2. A three-angle estimate

For a unitary \(W\) write \(H(W)=(W+W^\ast)/2\).
A common left unitary multiplication reduces the three matrices
to \(I,U,V\). Equation (2) gives
\[
 J-9d=4\bigl(\|H(U)\|_F^2+\|H(V)\|_F^2
                       +\|H(U^\ast V)\|_F^2\bigr).
\tag{4}
\]
The same formula holds for real orthogonal matrices.

Work in the real Hilbert space given by the real part of the
inner product, and put \(\theta=\arcsin\|H(U)\|_{\rm op}\),
\(\psi=\arcsin\|H(V)\|_{\rm op}\). Suppose there is a unit vector
x and a unit vector e such that
\[
 \langle e,Ux\rangle_{\mathbb R}\ge\cos\theta,\qquad
 \langle e,Vx\rangle_{\mathbb R}\ge\cos\psi .
\]
The real angle between \(Ux,Vx\) is at most \(\theta+\psi\)
(by decomposition along e, or by the spherical triangle
inequality). Consequently,
\[
 \|H(U^\ast V)\|_{\rm op}\ge
       \max\{0,\cos(\theta+\psi)\}.
\tag{5}
\]
For \(0\le\theta,\psi\le\pi/2\), the numerical minimum
\[
 \sin^2\theta+\sin^2\psi+\max\{0,\cos(\theta+\psi)\}^2
                  \ \ge\ 3/4
\tag{6}
\]
is attained only at \(\theta=\psi=\pi/6\). Indeed for sum at least
\(\pi/2\) the first two terms are at least 1 by
\(\sin^2\theta+\sin^2\psi=1-\cos(\theta+\psi)\cos(\theta-\psi)\).
Otherwise set \(c=\cos(\theta+\psi)>0\); the expression is
at least \(1-c+c^2=3/4+(c-1/2)^2\), with equality requiring
\(\theta=\psi\) as well.

## 3. Complex dimension parity

Assume d is odd. If either \(\|H(U)\|_{\rm op}\) or
\(\|H(V)\|_{\rm op}\) is one, (4) is at least 4.
Otherwise the Hermitian imaginary part of each unitary is
invertible, since it commutes with the real part and the sum of
their squares is I. Independently flip signs of U and V so their
imaginary parts each have a positive eigenspace of dimension
at least \((d+1)/2\); (4) is unchanged. These eigenspaces
intersect. A common unit vector x satisfies
\[
 \langle ix,Ux\rangle_{\mathbb R}\ge
 \sqrt{1-\|H(U)\|_{\rm op}^2},\qquad
 \langle ix,Vx\rangle_{\mathbb R}\ge
 \sqrt{1-\|H(V)\|_{\rm op}^2},
\]
by the spectral lower bounds on those eigenspaces. Apply
(5)–(6) with \(e=ix\) and use
\(\|H(W)\|_F^2\ge\|H(W)\|_{\rm op}^2\).
Thus (4) is at least 3.

Sharpness in dimension one uses the displayed scalar phases.
The two-dimensional matrices \(iX,iZ\), with \(X,Z\) the usual
Pauli matrices, have three vanishing Hermitian parts in (4).
Taking direct sums of these pairs gives the even-dimensional
zero and extends the odd-dimensional equality example to
all odd sizes.

At equality in odd dimension, each of the three Hermitian
parts has rank one, since it has a nonzero operator norm and
its squared Frobenius and operator norms agree. The angles in
(6) are both \(\pi/6\), and equality in (5) forces \(Ux,Vx\)
to make exactly those angles with \(ix\). The imaginary part
of U on x is therefore its minimal positive eigenvalue
\(\sqrt3/2\): equality in the spectral lower bound says x
lies in that eigenspace. On it \(H(U)^2\) is \(1/4\), so x
spans the nonzero eigenspace of \(H(U)\); the same is true for
V. Consequently x is a common scalar eigenvector. Equality
of the angle between \(Ux,Vx\) forces opposite signs of
their real parts, hence the two stated phases after the
chosen signs. On the orthogonal complement all three
Hermitian parts vanish; in particular the two relative
unitaries are skew-Hermitian and anticommute. This proves
the equality description.

## 4. Real dimension modulo four

In odd real dimension, each of \(U,V,U^{\mathsf T}V\) has a
real eigenvalue \(+1\) or \(-1\), since eigenvalues off the
real line come in conjugate pairs. Thus each of the three
Frobenius squares in (4) is at least one and (4) is at least
12. This is attained by the scalar pair in dimension one.
For size three choose unit axes u,v with
\(u\cdot v=\sqrt2-1\), and let \(U,V\) be rotations by
\(\pi/2\) about u,v. Rodrigues' formula
\(R_u=uu^{\mathsf T}+[u]_\times\) gives
\(\operatorname{tr}(R_u^{\mathsf T}R_v)=(u\cdot v)^2+2(u\cdot v)=1\).
Since this relative rotation is in \(\mathrm{SO}(3)\),
it too has angle \(\pi/2\). Thus each Hermitian-part square in
(4) is one. In dimension four, real left multiplication by
the quaternion units i and j gives skew orthogonal,
anticommuting \(U,V\), so (4) is zero. Direct sums settle all
odd real sizes and all sizes divisible by four.

Now assume \(d\equiv2\bmod4\). If any of the three orthogonal
matrices in (4) has real eigenvalues, there are at least two,
counted with multiplicity, by parity. It alone contributes
at least 8 to (4). Otherwise all three symmetric parts
satisfy \(\|H(W)\|_F^2\ge2\|H(W)\|_{\rm op}^2\) since each
rotation plane contributes a repeated cosine. For U and V
write their skew parts as \(J B_U,K B_V\), respectively,
where \(J,K\) are real skew orthogonal complex structures
(\(J^2=K^2=-I\)), and
\(B_U=(I-H(U)^2)^{1/2}\), \(B_V=(I-H(V)^2)^{1/2}\)
are positive definite. This comes from the real rotation
blocks, or from polar decomposition of the skew parts.
Each symmetric part commutes with its skew structure.

We claim there is a nonzero real vector x with \(Jx=Kx\)
or \(Jx=-Kx\). The symmetric operator
\((JK+KJ)/2\) commutes with J and K and has spectrum in
\([-1,1]\). On an eigenspace of value \(|\lambda|<1\), the
operator \((K+\lambda J)/\sqrt{1-\lambda^2}\) is another
skew orthogonal complex structure anticommuting with J.
Such a space has dimension a multiple of four: for any unit
vector, its images by \(1,J,K',JK'\) form an orthonormal
invariant quadruple, and one iterates on the orthogonal
complement. Hence there must be an endpoint eigenspace,
where \(K=-\lambda J\), since \(K+\lambda J\) is skew and
squares to zero there. This proves the claim.

Choose x of unit length there and, if needed, flip the sign
of V to make \(Jx=Kx\). Relative to \(e=Jx\) one has
\[
 \langle Jx,Ux\rangle=\langle x,B_Ux\rangle
         \ge\sqrt{1-\|H(U)\|_{\rm op}^2},
\]
since \(J^{\mathsf T}H(U)\) is skew. The analogous V
bound holds. Now (5)–(6), with the factor two for the
Frobenius squares, give the lower bound 6 in (4).
On a real two-plane, take rotations \(\pi/3,2\pi/3\);
all three squared symmetric parts equal \(1/2\).
Add quaternionic four-blocks for every larger size
\(d\equiv2\bmod4\).

For equality in this residue class the three symmetric
parts each have rank two with one nonzero rotation-plane
cosine of absolute value \(1/2\). Equality in the two spectral
lower bounds puts x in the nonzero plane for U and for V.
Because each plane is invariant under its own skew
structure, \(x,Jx=Kx\) span the same plane for both. Their
rotation angles, with the chosen orientation and signs, are
\(\pi/3,2\pi/3\), by opposite real parts in the equality
of (5). On the complement the three symmetric parts vanish
and one is left with exact anticommutation, as claimed.

## 5. A prescribed-spectrum corollary and the equality barrier for more summands

If three rectangular coefficients have exactly the same
input covariance \(P^2\) and the same output covariance \(Q^2\),
fix these two equal nonzero spectra and restrict to their
supports. The relative unitaries \(W_i\) commute with P.
Decomposing into eigenspaces of each positive singular value
\(\sigma\), with multiplicity \(d_\sigma\), formula (4)
and the sharp examples show that the exact minimum is
\[
 \sum_{\sigma>0}\sigma^4\bigl(9d_\sigma+\delta(d_\sigma)\bigr)
\]
over the real or complex field as appropriate. This is a
finite-size restriction, unlike the unconstrained attainability
assertion of Theorem 1.

A related complex obstruction works for any m at the fully
balanced corner \(M=L=mD\). By equality in the covariance
Cauchy–Schwarz bounds, both covariances agree term by term.
On each common positive singular-value eigenspace,
equation (2) allows \(J=M\) exactly when there are
\(m-1\) mutually anticommuting skew-Hermitian unitaries.
Thus its dimension must be divisible by
\(2^{\lfloor(m-1)/2\rfloor}\), and this is sufficient by the
Pauli construction above. To see necessity directly, write the
\(m-1\) generators as \(R_1,\ldots,R_{m-1}\). Pair
\(R_{2j-1},R_{2j}\) and form the commuting Hermitian involutions
\(iR_{2j-1}R_{2j}\). Each \(R_{2j-1}\) swaps the two signs of the
j-th involution and
preserves all other signs, so all joint eigenspaces have the
same dimension. This is the classical Clifford dimension
mechanism; (3) gives more at the first forbidden sizes,
by determining the exact positive fourth-moment gap.

The optional exact checker
~~~sh
python3 verify_factor_rademacher_fourth_moment.py
~~~
checks both fourth-moment expansions on rectangular Gaussian
integer matrices and the sharp three-unitary examples in a
rational algebra with radical relations. The universal bounds
do not depend on finite or numerical optimization.
