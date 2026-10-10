# Unrestricted purity confinement from rearrangeable Schmidt tests

Research working proof, 10 October 2026. No manuscript or Release is prepared. This is an analytic proof for arbitrary actual APPT states, not a restriction to a candidate spectral family. It is not Lean-formalized or externally reviewed.

## 1. The physical necessary condition

Let 3<=m<=n, D=mn, and let lambda_1>=...>=lambda_D be the eigenvalues of an APPT density matrix. Put

    R=m(m-1)/2, S=m(m+1)/2, j=D-S+1, b=lambda_j,
    delta_i=lambda_i-lambda_{D+1-i},  1<=i<=R.

These differences are nonnegative and decreasing. For ANY assignment of the R differences to the edges of the complete graph on m vertices, let A_delta be the symmetric zero-diagonal weighted adjacency matrix. Then

    lambda_max(A_delta)<=2b.                                      (1)

Proof: for any nonnegative unit vector x, use psi=sum_i x_i |ii>. The partial transpose of its projector has eigenvalues x_i^2 on diagonal vectors, +x_i x_l on symmetric pairs, -x_i x_l on antisymmetric pairs, and zeros on the remaining D-m^2 dimensions. On the edge carrying delta_i assign lambda_i to the negative eigenvector and lambda_{D+1-i} to the positive eigenvector. Assign the next m smallest eigenvalues to diagonal vectors. The slots are distinct since m^2<=D; a global unitary realizes this assignment. Each diagonal eigenvalue beta_l is at most b. APPT gives

    0<=sum_l beta_l x_l^2-sum_edges delta_edge x_i x_l
      <=b-(1/2)x^T A_delta x.

The maximum Rayleigh quotient of a symmetric nonnegative matrix has a nonnegative maximizing vector (take componentwise absolute values). This proves (1) without assuming a spectral-characterization theorem or a product-ordering compatibility condition. In particular,

    sum_{i=1}^R delta_i<=mb.                                      (2)

## 2. Two different rearrangements of the same spectrum

Put h=floor(m/2), l=ceil(m/2), q=hl=floor(m^2/4). Then l<=m-1 and q<=R. Put the largest l differences on a star and fill the other edges with the remaining nonnegative differences. The star's spectral radius and monotonicity of Rayleigh quotients give

    sum_{i=1}^l delta_i^2<=4b^2.                                 (3)

Next fill an h-by-l matrix C row by row with delta_1,...,delta_q. Use it for the cross edges of a complete bipartite graph and put all other differences on the within-part edges. Equation (1) implies ||C||_op<=2b. For the unit all-ones vector e in R^l,

    ||Ce||^2=(1/l)sum_rows(sum_entries_in_row delta)^2.

Every entry of row t is at least every entry of row t+1, so its squared row sum divided by l is at least the sum of squares in row t+1. Summing t=1,...,h-1 yields

    sum_{i=l+1}^q delta_i^2<=4b^2,
    sum_{i=1}^q delta_i^2<=8b^2.                                 (4)

Neither test assumes that there are only two or three eigenvalues.

## 3. Finite unrestricted purity bound

Let V=sum lambda_i^2-1/D, t=delta_q and z=(lambda_q+lambda_{D-q+1})/2. For i<=q, the numbers u=lambda_i-z and v=z-lambda_{D+1-i} are at least t/2 and sum to delta_i. Expanding (u-t/2)(v-t/2)>=0 gives

    u^2+v^2<=delta_i^2-t delta_i+t^2/2.

The other D-2q eigenvalues are within t/2 of z. The mean 1/D minimizes the sum of squared distances to a scalar. Therefore

    V<=sum_{i<=q}delta_i^2-t sum_{i<=q}delta_i+D t^2/4
     <=8b^2+(D/4-q)t^2.                                         (5)

Since D/4>=q and qt<=mb by (2), define

    C(m,n)=8+(D/4-q)m^2/q^2.

Then every APPT density matrix obeys

    V<=C(m,n)b^2<=C(m,n)/(D-S+1)^2.                              (6)

The last step is j*b<=1. If C(m,n)<j, a stronger explicit bound is

    D^2 V<=C(m,n)/(1-sqrt(C(m,n)/j))^2.                           (7)

Indeed b<=1/D+sqrt(V/j): if b>1/D, the first j eigenvalues each contribute at least (b-1/D)^2 to V; otherwise the inequality is immediate. Insert V<=Cb^2 and rearrange.

## 4. Proportional growth and an improved constant

Suppose m tends to infinity and n/m tends to a finite gamma>=1. Equation (6) first implies V=O_gamma(D^-2), uniformly over APPT spectra. Also

    Db<=1+D sqrt(V/j)=1+O_gamma(D^-1/2).

Hence (6) gives

    limsup D^2 V<=4+4gamma.                                      (8)

A second variance estimate improves this when gamma is larger. Set t=delta_q, w=delta_R, Bq=sum_{i<=q}delta_i and Bmid=sum_{q<i<=R}delta_i. Choose the center (lambda_R+lambda_{D-R+1})/2. The first q pairs have squared distance at most delta_i^2-w delta_i+w^2/2. For q<i<=R, additionally use

    delta_i^2<=(t+w)delta_i-tw,

valid because w<=delta_i<=t. The D-2R remaining eigenvalues are within w/2 of the center. These estimates give

    V<=8b^2+t Bmid-w Bq-(R-q)tw+D w^2/4
     <=8b^2+tmb-qt^2-Rtw+D w^2/4,                               (9)

where Bmid<=mb-Bq and Bq>=qt. Also

    0<=w<=t, qt+(R-q)w<=mb.                                     (10)

One has b>0: otherwise (1) forces delta_1=0, and the ordering then forces every eigenvalue to be zero, contrary to trace one. Put x=mt/b and y=mw/b. They are bounded, and every limit pair satisfies 0<=y<=x and x+y<=4. The nonconstant part of (9), after division by b^2, tends to

    f_gamma(x,y)=x-x^2/4-xy/2+gamma*y^2/4.

For fixed x this is convex in y, so its maximum is at y=0 or y=min(x,4-x). At y=0 the maximum is 1. At y=x, 0<=x<=2, it equals x+(gamma-3)x^2/4, whose maximum is at most max(1,gamma-1). At y=4-x, 2<=x<=4, it equals -y+(gamma+1)y^2/4 with 0<=y<=2; its maximum is max(0,gamma-1). Thus max f_gamma=max(1,gamma-1).

Combining this with (8), the unrestricted maximal purity satisfies

    limsup D^2[Pmax(m,n)-1/D]<=U(gamma)
    U(gamma)=min{4+4gamma, 8+max(1,gamma-1)}
            =4+4gamma,  1<=gamma<=5/4;
             9,         5/4<=gamma<=2;
             7+gamma,   gamma>=2.                               (11)

The passage to maximizing states is legitimate: the finite bounds are uniform, and the APPT state set is compact. In particular,

    limsup m^4[Pmax(m,m)-1/m^2]<=8.                              (12)

Together with the previously proved positive D^-2 lower constructions, this establishes the exact order of the unrestricted excess purity in proportional growth. It does not establish the sharp leading constant. No restriction on the number of spectral levels or the rank of an extremizer was used.

## Verification boundary

The proof uses the displayed physical Schmidt tests and elementary real matrix analysis. Finite regression checks of the rearrangement and variance identities are ancillary, not substitutes for the argument over all dimensions. Literature searches do not constitute a first-priority certification. Existing immutable publications are unchanged.
