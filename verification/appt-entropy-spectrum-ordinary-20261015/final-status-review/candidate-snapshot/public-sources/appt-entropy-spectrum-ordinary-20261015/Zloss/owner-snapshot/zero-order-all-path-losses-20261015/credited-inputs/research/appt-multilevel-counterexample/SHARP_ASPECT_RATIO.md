# Sharp unrestricted APPT purity for aspect ratios up to three

> Subsequent sharp result: [SHARP_ASYMPTOTIC.md](SHARP_ASYMPTOTIC.md) closes the remaining leading-constant gaps for every aspect ratio, and gives an equivalent uniform over all dimension pairs as total dimension grows. The proofs below remain valid; descriptions of then-open asymptotic gaps record intermediate progress. Exact finite maxima and absolute separability remain unresolved.


Research working proof, 10 October 2026. This strengthens the balanced result in MULTISCALE.md. It is an analytic proof, not a Lean certificate or externally reviewed result. No new manuscript or Release is prepared.

## 1. The theorem

For every sequence of integer dimensions m<=n with m tending to infinity and n/m tending to gamma in [1,3],

    (mn)^2[Pmax(m,n)-1/(mn)] ->8.                                (A1)

Equivalently,

    Pmax(m,n)=1/(mn)+8/(mn)^2+o((mn)^-2).                         (A2)

The maximum is over ALL APPT density matrices, without a restriction on spectral levels or eigenvalue multiplicities. For general fixed gamma>=1 we obtain the narrower interval

    max(8,4+gamma) <= liminf D^2[Pmax-1/D]
                     <= limsup D^2[Pmax-1/D] <= max(8,5+gamma),
    D=mn.                                                       (A3)

Thus the bounds match throughout [1,3]. For gamma>=4 they leave a gap of at most one in the leading coefficient. No exact coefficient for gamma>3 is asserted.

The multiscale lower bound 8 and the earlier one-spike/broad-plateau lower bound 4+gamma are proved in MULTISCALE.md and ASYMPTOTIC.md. The new step is the unrestricted upper bound below. Its improvement over UNRESTRICTED_BOUND.md is to use, rather than discard, the weights placed inside the two parts of the rectangular rearrangement.

## 2. Physical test notation

Let lambda_1>=...>=lambda_D be an APPT spectrum and set

    R=m(m-1)/2, S=m(m+1)/2, j=D-S+1,
    b=lambda_j, delta_i=lambda_i-lambda_{D+1-i}, 1<=i<=R.

The physical Schmidt-test derivation in UNRESTRICTED_BOUND.md gives, for EVERY placement of the decreasing nonnegative delta_i on the edges of K_m,

    A_delta <=2b I,    sum_{i<=R}delta_i<=mb.                     (A4)

Here the first inequality is the real symmetric matrix order. To recall the quantum argument: assign the top R eigenvalues to antisymmetric Schmidt-pair vectors, the bottom R to the corresponding symmetric vectors, and the next m smallest eigenvalues to diagonal Schmidt vectors. Those diagonal eigenvalues are all at most b. APPT for this actual unitary orbit gives x^T A_delta x<=2b for every nonnegative unit x. Since A_delta is entrywise nonnegative, its largest eigenvalue has a nonnegative maximizing vector; this proves the full matrix order in (A4). Slots are distinct since m^2<=D. No unproved spectral characterization is assumed.

Put

    h=floor(m/2), l=ceil(m/2), q=hl,
    T=R-q=binom(h,2)+binom(l,2),
    Bq=sum_{i<=q}delta_i, Bt=sum_{q<i<=R}delta_i,
    t=delta_q, w=delta_R.

For m>=3, T>0 and l<=m-1. Write Hq=sum_{i<=q}delta_i^2.

## 3. A strengthened rearrangement inequality

Put the first l differences on a star; (A4) gives

    sum_{i=1}^l delta_i^2<=4b^2.                                 (A5)

For a DIFFERENT assignment of the same differences, put delta_1,...,delta_q row by row into an h-by-l cross matrix C. Assign the largest binom(l,2) of the remaining T differences to the within-l-part edges, and the rest to the within-h-part edges. If B_B is the sum on the larger part, then

    B_B >= [binom(l,2)/T] Bt.

For the unit all-ones vector e in the l-part, its within-part Rayleigh quotient is

    beta=(2/l)B_B >=[(l-1)/T] Bt.                                (A6)

If C e is nonzero, take the unit nonnegative vector u=C e/||C e|| in the h-part. The compression of A_delta to u and e is

    [ alpha   ||Ce|| ]
    [ ||Ce||   beta  ],

where alpha>=0 because u and all within-part entries are nonnegative. The matrix order in (A4) implies

    ||Ce||^2 <=(2b-alpha)(2b-beta)<=2b(2b-beta).

If C e=0, the following bound follows directly as well (beta<=2b by (A4)). As each entry of a row of C is at least every entry of the next row,

    sum_{i=l+1}^q delta_i^2<=||Ce||^2.

Combining with (A5)-(A6),

    Hq <=8b^2-a_m b Bt,    a_m=2(l-1)/T.                         (A7)

The placement inside the parts is essential. Replacing both within-part blocks by zero would lose the term a_m b Bt and the sharper theorem.

For even m=2h, a_m=2/h=m/q. For odd m=2h+1, a_m=2/h>m/q. Since q t<=mb by (A4),

    a_m b-t>=0.

In particular, the whole list of R gaps, not just its first q entries, obeys

    sum_{i=1}^R delta_i^2
      <=Hq+t Bt<=8b^2-(a_m b-t)Bt<=8b^2.                        (A8)

## 4. Center the variance at the last paired interval

Let V=sum_i lambda_i^2-1/D and choose z=(lambda_R+lambda_{D-R+1})/2. For each of the R pairs, u=lambda_i-z and v=z-lambda_{D+1-i} satisfy u,v>=w/2 and u+v=delta_i. Therefore

    u^2+v^2<=delta_i^2-w delta_i+w^2/2.

The other D-2R eigenvalues are within w/2 of z, and centering at the mean can only decrease the total squared distance. Thus

    V<=sum_{i<=R}delta_i^2-w(Bq+Bt)+D w^2/4
     <=8b^2-(a_m b-t+w)Bt-w Bq+D w^2/4.                         (A9)

Use Bt>=T w, Bq>=q t, and the nonnegativity of the coefficient a_m b-t+w. Since a_m T=2(l-1),

    V<=8b^2-2(l-1)b w+(T-q)t w+(D/4-T)w^2.

For both parities, T-q=-h and T+h=q. Since t>=w, this yields the simple finite inequality

    V<=8b^2-2(l-1)b w+(D/4-q)w^2.                               (A10)

One has D/4-q>=0. Also 0<=w<=mb/R by (A4), so the right side is convex as a function of w and is bounded by its endpoint values. Define

    Csharp(m,n)=max{8,
       8-2m(l-1)/R+(D/4-q)m^2/R^2}.

Every APPT spectrum therefore satisfies

    V<=Csharp(m,n)b^2<=Csharp(m,n)/j^2.                          (A11)

If Csharp<j, the same normalization bootstrap as before gives the explicit finite bound

    D^2 V<=Csharp/(1-sqrt(Csharp/j))^2.                          (A12)

No claim that this finite upper bound is exactly attained is made.

## 5. Take the dimension limit only after the uniform bound

For n/m->gamma<infinity,

    Csharp(m,n)->max{8,5+gamma},  j asymptotic to D(1-1/(2gamma)).

Equation (A11) first gives V=O_gamma(D^-2), uniformly for all APPT spectra. If b>1/D, the first j eigenvalues each contribute at least (b-1/D)^2 to V; otherwise b<=1/D. In both cases

    b<=1/D+sqrt(V/j),     Db<=1+o(1).

Insert this into V<=Csharp b^2. Uniformity permits choosing an exact maximizing state at each dimension (the APPT set is compact). This proves

    limsup D^2[Pmax(m,n)-1/D]<=max(8,5+gamma).                    (A13)

The lower bound 8 in MULTISCALE.md holds for each such sequence: its hierarchy parameters and slack are fixed first, then dimensions grow, and only then are the parameters sent to their extremal limits. Therefore for 1<=gamma<=3 both liminf and limsup equal 8. This proves (A1)-(A2). The additional lower construction with coefficient 4+gamma proves (A3).

## 6. Remaining sharpness problem

For 3<gamma<4 the current interval is [8,5+gamma], and for gamma>=4 it is [4+gamma,5+gamma]. It is not justified to pick either endpoint as a new global formula. The upper proof uses only necessary rearrangements; the lower proof constructs actual APPT states. Closing the residual gap requires a stronger unrestricted inequality or a new spectral mechanism.

The exact finite-dimensional maximum, equality cases, absolute separability of the multiscale spectra, efficient finite thresholds and Lean formalization are not resolved here. The finite checker verifies the algebraic rearrangement steps and deliberately invalid alternatives; it does not replace the analytic proof for all dimensions.
