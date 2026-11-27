# Near-square Gaussian module transfer: the kernel volume cost

**Scope.** The infinite-domain Gaussian leftover hash lemma compares a Gaussian linear image with a discrete Gaussian of the corresponding continuous covariance. See [Agrawal–Gentry–Halevi–Sahai](https://eprint.iacr.org/2012/714) and the number-field extension of [Albrecht–Felderhoff–Lai–Lapiha–Woo (AFLLW)](https://perso.jfelderhoff.fr/work/papers/AFLLW25.pdf), especially its separate column-generation and kernel-smoothing requirements. We quantify the volume obstruction to transfer for near-square matrices, even on the event that the columns already generate the entire target module. For one surplus column, the same volume determines a deterministic sufficient smoothing width up to a factor sqrt(n). This is a statistical comparison of abstract Gaussian distributions, not an algorithm for sampling kernels or attacking or testing a scheme.

## 1. Setup and a deterministic volume identity

Use R=Z[zeta_(2n)] for n a power of two, in the usual canonical Euclidean metric (complex conjugate pairs counted twice). Its lattice is isometric to sqrt(n) Z^n by the power basis, hence det R=n^(n/2). Let X in R^(r by m), m=r+u, u>=1, have full row rank over the field. Denote by A its real linear map between the associated canonical Euclidean spaces and put

    J= sqrt(det_RR(AA^T))
       = product_(complex places v) det(X_v X_v^*).        (1)

The second notation means real determinant on the ambient real target space; X_v is the complex matrix in embedding v, with * its conjugate transpose. Because singular values in each complex place are repeated twice over the reals, the real square root is the product shown. Let Lambda=ker(A) intersect R^m. If X is surjective onto R^r as an R-module, then

    det Lambda = n^(nu/2) J.                              (2)

Indeed, orthogonal projection of the source lattice onto ker(A)^perp has covolume det(R^r)/J: A restricts to an invertible linear map there, with Jacobian J, and takes that projection onto R^r. Multiplying this projection covolume by the covolume of the fiber lattice gives det(R^m). This multiplication follows, for example, by lifting a lattice basis of the image and adjoining a lattice basis of the kernel, then taking the block-triangular determinant in the orthogonal splitting. This proves (2).

For any epsilon>0, by Poisson summation and the primal origin term,

    eta_epsilon(Lambda)
       >= sqrt(n) J^(1/(nu)) (1+epsilon)^(-1/(nu)).         (3)

In particular, it may be much larger than eta_epsilon(R^m) although the image has no arithmetic index obstruction.

### One surplus column: a deterministic upper bound

If u=1 and X is surjective, let w be the vector of signed r by r minors obtained by deleting one column at a time. It generates the kernel over the field. It also generates Lambda over R, because those minors generate the unit ideal: a proper ideal would lie in a maximal ideal where X was not full rank. If z=a w is integral in every coordinate, an R-linear combination of the coordinates of w is 1, so a is integral too.

The isometry of the kernel lattice with a diagonally weighted copy of R has weights W_v=||w_v|| in the complex places. Cauchy–Binet gives W_v^2=det(X_v X_v^*) and the weighted geometric mean of W_v is J^(1/n). In this metric, spherical width t on Lambda is the elliptical width vector (t/W_v)_v on R. The ideal product-of-widths smoothing bound [Peikert–Regev–Stephens-Davidowitz, Lemma 6.9](https://web.eecs.umich.edu/~cpeikert/pubs/rlwe-anyring.pdf) (with |Delta_K|^(1/n)=n) therefore gives

    eta_(exp(-n))(Lambda) <= n J^(1/n).                    (4)

This uses the product only; no near equality of the W_v is required. Equations (3)–(4) put the one-surplus kernel smoothing width between the covolume scale and sqrt(n) times that scale.

## 2. Actual statistical necessity and sufficiency

For t>0 let P_X be the law of XZ for Z drawn from D_(R^m,t). Let Q_X be the discrete Gaussian on the whole lattice R^r with real width operator t(AA^T)^(1/2), i.e. mass proportional to

    exp(-pi y^T (AA^T)^(-1)y/t^2).

If X is surjective, each fiber over y is a translate of Lambda, and the least Euclidean length real preimage is perpendicular to the kernel. Splitting this preimage orthogonally gives exact mass

    P_X(y) proportional to
       exp(-pi y^T(AA^T)^(-1)y/t^2) rho_t(Lambda+c_y)

for some offset c_y in the kernel. Thus t>=eta_epsilon(Lambda) ensures TV(P_X,Q_X)<=epsilon/(1-epsilon) when epsilon<1: by Poisson summation all the fiber factors are between (1-epsilon) and (1+epsilon) times the same main term. In particular (4) supplies a deterministic near-square sufficient bound, even if the canonical singular values vary over the places.

The next assertion is an actual TV obstruction, not just a failure of a sufficient criterion. Fix any polynomial bound on m and take n tending to infinity. Suppose t>=2n and the least singular value of A is at least one. Define

    Gap = log J - nu [log(t/sqrt(n)) + 1/2].

There are absolute constants in the following estimates. For each fixed b>0 take large enough C_b. If

    Gap >= C_b sqrt(nm log n),                             (5)

then TV(P_X,Q_X)>=1-O(n^(-b)). This direction does not require surjectivity; in particular it applies even if surjectivity is already known. At smaller t>=sqrt(n), one weaker sufficient condition for TV to tend to one is

    log J - nu log(t/sqrt(n)) - (pi+log 2)nm -> +infinity,
                                                                    (6)

and this weaker condition does not require a lower bound on the smallest singular value beyond full row rank.

**Proof of (5).** For a Gaussian of width operator B on a full lattice M of dimension d, write V=pi ||B^(-1)x||^2 for its energy. Poisson gives the normalization

    rho_B(M) = det(B)/det(M) * Theta_M(B),
    Theta_M(B)=sum_(w in M*) exp(-pi ||B w||^2).

Here B is positive symmetric. Formulas for the source and target use B=tI and t(AA^T)^(1/2), respectively. Since t>=2n, min singular(A)>=1, and the Gaussian dual tails for each n-dimensional component at width n are at most exp(-n) by the same PRS smoothing bound or elementary dyadic coordinates, both of these normalizers have Theta=1+O(m exp(-n)). This remains true under division of B by sqrt(1-z) for all |z|<=1/2, by domination by the spherical dual theta at width n. The energy moment generating function is exactly

    E exp(z V)=(1-z)^(-d/2) Theta_M(B/sqrt(1-z))/Theta_M(B).

Thus log E exp(z(V-d/2))<=C d z^2+O(m exp(-n)). Taking |z| of order sqrt(log n/d) proves deviations of order sqrt(d log n) with probability at least 1-O(n^(-b)), for suitable constants. Since information content is log rho_B(M)+V, this yields high probability information centers

    h_in  = nm [log(t/sqrt(n))+1/2],
    h_out = nr [log(t/sqrt(n))+1/2]+log J.

Their difference h_out-h_in is exactly Gap. Let S be the high-probability source set with information at most h_in+delta. Its cardinality is at most exp(h_in+delta). Thus P_X places almost all mass in A S. On the high-probability target set with information at least h_out-delta, each point has probability at most exp(-h_out+delta). Consequently Q_X(A S)<=O(n^(-b))+exp(-Gap+2delta). Use delta of order sqrt(nm log n) and absorb b log n into (5) to finish. No enumeration of S is needed.

**Proof of (6).** The source is within a ball of radius t sqrt(nm) with probability at least 1-exp(-nm), using the Gaussian width-doubling tail bound. The ball has at most exp(pi nm) rho_t(R^m) points. Since t/sqrt(n)>=1, the one-dimensional Poisson identity and geometric Gaussian-tail bound give rho_t(R)<= (2t/sqrt(n))^n. Every target atom has probability at most (sqrt(n)/t)^(nr)/J, by its dual origin term. Multiplying gives (6) as a bound for the Q_X mass of the image of the source ball.

## 3. Size of the realized barrier for broad random dyadic matrices

Take r,u>=1 with m=r+u at most polynomial in n and independent entries X_ij~D_(R,s). A convenient explicitly broad range for the next estimates is s>=n^3 m^3. With probability tending to one the map has least real singular value at least one, and

    (log J)/(nr)
       = log(s/sqrt(2 pi))
            + (1/(2r)) sum_(j=u+1 to u+r) psi(j) + o(1),    (7)

where psi(j)=E log Gamma(j,1) is the usual digamma value. This still holds with high conditional probability if one conditions on surjectivity: the ramified-rank theorem in the companion note [Gaussian module generation](cyclotomic-gaussian-module-generation.md) gives a uniform positive lower bound on that event in the dyadic range. That note is not needed to prove (2)–(7) unconditionally.

For u=1, as r grows, sum psi(j)/r=log r-1+o(1). Thus the one-surplus scale sqrt(n) J^(1/n) has logarithm

    (1/2)log n + r [log(s sqrt(r)/(sqrt(2 pi e))) + o(1)].

Consequently, even the actual Gaussian transfer is impossible at a fixed fractional deficit in this logarithmic scale, while a factor sqrt(n) above the realized volume scale suffices. More precisely, the lower bound (5) starts at log(t/sqrt(n)) <= (log J)/(nu)-1/2-O(sqrt(nm log n)/(nu)). These are statements about the Gaussian model and realized map, not optimal width estimates for open variants at smaller s or all values of u.

**Proof of (7).** Because the dyadic power basis is an orthogonal basis scaled by sqrt(n), a discrete Gaussian ring entry has independent integer coefficients of width s/sqrt(n). In one dimension, the TV between nearest rounding of the continuous Gaussian of width a and the normalized discrete Gaussian of width a is O(a^(-2)) for a>=1: use the centered cell average expansion with integral second derivative, summed over unit cells, and Poisson for the normalization. Explicitly, for continuous Gaussian density f_a, Taylor with integral remainder on each unit cell gives sum_k |int_(k-1/2)^(k+1/2) f_a - f_a(k)| <= C int |f_a''|=O(a^(-2)); the discrete sum of f_a differs from one by O(exp(-pi a^2)). Thus all n r m coefficients can be coupled to nearest rounding together except with probability O(n^2 r m/s^2).

In the continuous model the canonical real coordinates are independent spherical Gaussians. At each complex embedding place v the matrix is (s/sqrt(2 pi)) G_v, where the G_v are independent standard complex Gaussian matrices with E|G_(v,i,j)|^2=1. Rounding all coefficients shifts a complex matrix by operator norm at most n sqrt(rm)/2: each scalar embedding perturbation is bounded by n/2, and Frobenius bounds operator norm. Even the leading square G_v has least singular value at least 1/(n r^(3/2)) with probability tending to one simultaneously over all places. To see this, each row's distance to the span of the others, conditional on those rows, has the law of the modulus of a standard complex Gaussian. It is less than 1/(nr) with probability at most (nr)^(-2). Union over at most nr row/place pairs, and use the inverse-matrix identity ||G_v^(-1)||_F^2=sum of inverse squared row distances. Appending extra columns cannot lower the least row singular value. With s>=n^3 m^3 the singular value perturbation relative to even that minimum is O(n^2 m r^(3/2)/s)=o(1), so rounding changes log J by o(nr) and all least singular values exceed one.

For each continuous place, Gram–Schmidt on the rows gives det(G_v G_v^*) as the product of independent Gamma(j,1) variables for j=u+1,...,u+r. This follows from independent isotropic complex Gaussian row projections onto residual complex dimensions m,m-1,...,m-r+1. Differentiating E Gamma(j,1)^a=Gamma(j+a)/Gamma(j) twice gives variance of its logarithm psi'(j)<=pi^2/6. By independence across places and factors, Chebyshev gives concentration of the average logarithm over all nr/2 factors. Including the deterministic s/sqrt(2 pi) scaling yields (7). The log-asymptotic for u=1 follows from psi(j)=log j+O(1/j), or directly from the integer harmonic-number formula and Stirling.

## Reproduction

    node verify-near-square-gaussian-kernel-volume.js

The verifier uses exact cofactor/Gram identities for generated integer matrices, exact rank-one primitive examples, and numerical gamma log-moment and Poisson comparisons. It does not contain a protocol implementation or a lattice decoding or sampling algorithm.
