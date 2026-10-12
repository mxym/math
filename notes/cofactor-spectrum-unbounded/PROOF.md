# Unbounded normalized cofactor spectra for rank two Gram matrices

Date: 2026-10-08. Complete proof for independent review. Literature novelty is
subject to the separate bounded source audit. This is not a resolution of
Lieb's permanental-dominance conjecture.

For an N by N Hermitian positive-semidefinite matrix A, define

    C(A)_ij = A_ij per A(i|j),

where A(i|j) deletes row i and column j. The notation C(A) avoids confusing
this matrix with the product polynomial used below. It is positive semidefinite,
and every row sum is per A. In particular per A is an eigenvalue.

## Theorem

For every R>0 there are a positive integer N and a complex Hermitian correlation
matrix A of rank exactly two such that

    lambda_max(C(A)) > R per A.

The same unboundedness holds for lambda_max(Re C(A)), where Re denotes entrywise
real part, equivalently the maximum Rayleigh quotient over real unit vectors.
There also exist complex Hermitian positive-definite correlation matrices with
both ratios arbitrarily large. The positive-definite assertion does not retain
rank two.

The proof gives no explicit rate in N. It uses two successive finite choices:
first a sufficiently large equidistributed base, then a sufficiently large
integer repetition count for that fixed base.

## 1  Bargmann convention and Gram identities

Let v_i=(a_i,b_i) be unit row vectors in C^2. Put ell_i(x,y)=a_i x+b_i y,
A_ij=a_i conjugate(a_j)+b_i conjugate(b_j), and P=product_i ell_i.
For homogeneous binary forms of degree d, use the inner product linear in its
first argument,

    <sum p_k x^(d-k)y^k, sum q_k x^(d-k)y^k>_B
       = sum_(k=0)^d (d-k)! k! p_k conjugate(q_k).

Leibniz expansion, or complex Gaussian moments, gives

    <product_i ell_i, product_j ell'_j>_B
       = per[<ell_i,ell'_j>_B].                         (1)

Thus per A=||P||_B^2>0 and

    C(A)_ij = <v_i tensor (P/ell_i),
                  v_j tensor (P/ell_j)>.

This proves positive semidefiniteness with the stated conjugation. Laplace
expansion gives C(A) 1=(per A)1.

Let mu be the probability Haar measure on CP^1, represented by unit (x,y).
For forms p,q of degree d,

    <p,q>_B = (d+1)! integral p conjugate(q) dmu.        (2)

Indeed, the phase integral kills different monomials and
integral |x|^(2a)|y|^(2b) dmu=a!b!/(a+b+1)!.

## 2  Exact compression under repetition

Fix n nonzero unit rows, and repeat every row exactly L times. Write N=nL,
A_L for their Gram matrix, and P_L=P^L. Index each row by (i,a), with
1<=i<=n and 1<=a<=L. Formula (1) gives

    C(A_L)_((i,a),(j,b))
       = A_ij <P^L/ell_i,P^L/ell_j>_B.                 (3)

In particular every L by L cluster is constant. Let U_L map the i-th standard
basis vector of C^n to the vector equal to 1/sqrt(L) on cluster i and zero
elsewhere. U_L is an isometry; C(A_L) vanishes on its orthogonal complement.
Consequently the nonzero spectrum of C(A_L)/per A_L, with multiplicities,
is exactly the nonzero spectrum of

    K_L = U_L* C(A_L) U_L / per A_L.

Let mu_L have density |P|^(2L)/integral |P|^(2L) with respect to mu. Using (2),
noting that P^L/ell_i has degree N-1, gives the exact identity

    (K_L)_ij = L/(nL+1) A_ij
                  integral [1/(ell_i conjugate(ell_j))] dmu_L.   (4)

Products in (4) are projectively well-defined. At a zero of a denominator the
integrand against its density means the continuous polynomial expression
P^L/ell_i times conjugate(P^L/ell_j), divided by the normalizing integral.

## 3  Spectral limit at a unique projective maximum

Suppose |P| has a unique projective global maximum at u. By a unitary change
of variables take u=(1,0). Since P(u) is the nonzero global maximum, every
ell_i(u)=a_i is nonzero. Define z_i=b_i/a_i.

For each fixed i,j, concentration in (4) yields

    integral [1/(ell_i conjugate(ell_j))] dmu_L
           -> 1/(a_i conjugate(a_j)).                 (5)

Here is a proof controlling the apparent poles. Near u the integrand is
continuous. Outside any chosen neighborhood of u, |P|<=a<M=|P(u)|. Choose
a smaller neighborhood with positive measure on which |P|>=b>a. The absolute
unnormalized tail is bounded by

    a^(2L-2) sup |(P/ell_i)(P/ell_j)|,

because |P|^(2L)/|ell_i ell_j|
=|P|^(2L-2)|(P/ell_i)(P/ell_j)|. The denominator is at least a positive
constant times b^(2L). Thus the normalized tail vanishes exponentially.
Continuity near u proves (5).

It follows entrywise, hence in operator norm in the fixed dimension n, that

    K_L -> K_infty = (J_n+z z*)/n.                    (6)

The first-order critical-point condition gives sum_i z_i=0. Explicitly, in
the local coordinate (1,t)/sqrt(1+|t|^2),

    log |P|^2 = constant + sum_i log |1+z_i t|^2
                              - n log(1+|t|^2).

The real and imaginary first derivatives at t=0 vanish, giving this sum.
Therefore the eigenvalues of K_infty are 1, ||z||^2/n, and zeros (with the
usual merger of zero eigenvalues if z=0). In particular

    lim_(L->infinity) lambda_max(C(A_L))/per A_L
        = max(1, n^(-1) sum_i |z_i|^2).               (7)

For the real Rayleigh quotient, compression by the real isometry U_L commutes
with entrywise real part. Writing z=x+i y gives

    Re K_infty = (J_n+x x^T+y y^T)/n,
    x,y perpendicular to 1.

The positive-semidefinite operator (x x^T+y y^T)/n has rank at most two and
trace ||z||^2/n. Hence

    lim_(L->infinity) lambda_max(Re C(A_L))/per A_L
        = lambda_max(Re K_infty)
        >= max(1, ||z||^2/(2n)).                     (8)

The factor one-half is a lower bound, not an asserted exact eigenvalue.

## 4  Equidistributed rows and a moving maximum

Choose finite collections of m unit rows whose empirical projective measures
nu_m converge weakly to Haar measure on CP^1. For example one may take a
sequence of rectangular midpoint grids in p=|a|^2 in (0,1) and the relative
phase, with both grid sizes tending to infinity; here m ranges along the
corresponding sequence of grid cardinalities. Only such a sequence is needed.
Let u_m be any projective global maximum of the corresponding product.
Rotate variables unitarily so that u_m=(1,0), and write the transformed rows
as (a_i,b_i). No a_i is zero.

The transformed empirical measures still converge weakly to Haar measure,
even though the rotations vary with m. To prove this, take an arbitrary
subsequence of these rotations. Compactness of U(2) gives a convergent
subsubsequence. For any continuous test function on compact CP^1, the
corresponding rotated test functions converge uniformly. Weak convergence
of nu_m and invariance of Haar then give the same Haar integral. Since every
subsequence has this property, the full transformed sequence converges.

For T>0, define

    f_T([a:b])=min(|b/a|^2,T),

with value T at a=0. This is continuous on CP^1. Under Haar measure,
p=|a|^2 is uniform on [0,1], and direct integration gives

    integral f_T dmu
       = integral_0^1 min((1-p)/p,T) dp
       = log(1+T).                                  (9)

Thus

    liminf_(m->infinity) (1/m) sum_i |b_i/a_i|^2
       >= log(1+T)

for every T>0. Since T is arbitrary, the averages tend to infinity. This
uses only bounded continuous test functions and does not assume convergence
of an unbounded moment.

## 5  Enforcing a unique maximum and choosing finite witnesses

The original product need not have a unique maximum. Append one additional
unit linear form ell_u(z)=<z,u_m>, using the convention that this expression
is linear in z. Its modulus on the unit sphere is at most one, with equality
exactly at the projective point u_m. If the original maximum value is M,
then the augmented product has modulus at most M, equals M at u_m, and
attains equality nowhere else. Its global maximum is therefore unique.

In the coordinates u_m=(1,0), the appended row is (1,0). It contributes z=0.
The augmented base has n=m+1 rows, and its squared-ratio average is

    (1/(m+1)) sum_(i=1)^m |b_i/a_i|^2 -> infinity.     (10)

For a prescribed R, choose one sufficiently large finite base so that the
quantity in (10) exceeds 2R+2. Its rows span C^2, since an equidistributed
sequence eventually is not contained in a single projective point. Freeze
this base. Equations (7) and (8) then show that for every sufficiently large
integer L both desired spectral ratios exceed R. All rows remain unit, so
A_L is a correlation matrix, and its rank is exactly two. This proves the
rank-two assertions of the theorem.

Finally, for any one strict witness A, the entries of C(A) and per A are
polynomials in the matrix entries; the largest eigenvalues of Hermitian
matrices and of their entrywise real parts are continuous. Since per A>0,
the strict inequalities persist for A+epsilon I when epsilon>0 is sufficiently
small. Divide by 1+epsilon to restore unit diagonal. The ratios are unchanged
by a positive scalar rescaling, because C(cA)=c^N C(A) and per(cA)=c^N per A.
The resulting matrix is positive definite. This proves the final assertion.

## 6  Interpretation and scope

The original eigenvalue assertion with R=1 was already disproved by Drury in
2018. The theorem here concerns the absence of every dimension-independent
constant, already among complex rank-two correlation matrices. Neither the
unbounded spectrum of the much larger Schur-power matrix nor the unbounded
Hadamard-product bunching ratio is being substituted for this cofactor claim.
Lieb's normalized character/subgroup inequality is a different assertion;
this theorem alone is not a counterexample to it.

For completeness, the local consequence can be stated with real directions,
which removes any row-versus-column Gram convention ambiguity. Let w be a
real unit vector and put

    B(epsilon)_ij=(1+epsilon^2 w_i w_j)
                  /sqrt((1+epsilon^2 w_i^2)(1+epsilon^2 w_j^2)).

This is a correlation matrix of rank at most two, with strictly positive
entries for sufficiently small epsilon. Its expansion is

    B(epsilon)_ij=1+epsilon^2(w_i w_j-(w_i^2+w_j^2)/2)+O(epsilon^4).

Multilinearity of the permanent, followed by the row and column sum identities
for C(A), gives

    per(A circ B(epsilon))/per A
      =1+epsilon^2[w^T Re C(A) w/per A-1]+O(epsilon^4).          (11)

Indeed the coefficient before division by per A is
sum_ij C(A)_ij w_i w_j - (1/2)sum_ij C(A)_ij(w_i^2+w_j^2)
=w^T C(A)w-per A; its first term equals w^T Re C(A)w because w is real.
This is the real-direction specialization of Pioge and coauthors,
arXiv:2508.00111, Lemma 1. For complex w their convention is the column Gram
with numerator 1+epsilon^2 conjugate(w_i)w_j; one should not silently replace
it by the opposite row-Gram convention.

Choosing a real top eigenvector of Re C(A), the theorem shows that the
relative second-order coefficient in (11) is unbounded. This is a local
coefficient statement; it supplies no uniform finite-epsilon gain. The
radius on which the expansion is useful may depend on the witness.
