# Spectral rigidity and the transition at aspect ratio four

Analytic research working proof. No new preprint, Release, Lean verification or external peer-review claim. This determines necessary structure of EVERY asymptotically maximizing APPT sequence, not only the previously constructed examples.

## 1. Statements

Let m tend to infinity, n/m tend to a fixed gamma>=1, D=mn, and let lambda be any decreasing APPT spectrum such that

    D^2(sum_i lambda_i^2-1/D) -> K_gamma := max(8,4+gamma).        (R1)

Set R=m(m-1)/2, S=m(m+1)/2, b=lambda_{D-S+1}, h=m-1, and

    g_i=(lambda_i-lambda_{D+1-i})/b, 1<=i<=R,
    w=g_R, eta_i=g_i-w, A=sum_i eta_i.

The normalizer b is positive and Db->1. The following limits hold:

- If gamma<4, then hw->0, sum_{i=1}^h g_i^2->4,
  and sum_{i=h+1}^R eta_i^2->4.
- If gamma>4, then hw->2, sum_{i=1}^h g_i^2->4,
  and sum_{i=h+1}^R eta_i^2->0.
- For EVERY gamma, including gamma=4, A/m->0 and, for every fixed theta>0,

      sum_{i>=ceil(theta m^2)}^R eta_i^2 ->0.                  (R2)

Thus in the gamma<4 phase, four units of paired-gap square mass lie in the first m-1 gaps and another four lie beyond those gaps but below every positive fraction of m^2. This is a necessary concentration statement; it is not a claim that all states have a single rank-one spike or that a specific hierarchy is the unique construction.

The empirical rescaled eigenvalue measures

    mu_m=(1/D) sum_i delta_{m(D lambda_i-1)}                    (R3)

converge in Wasserstein distance W1 as follows:

    gamma<4:   mu_m -> delta_0,
    gamma>4:   mu_m -> (delta_{-1}+delta_1)/2.                   (R4)

At the critical ratio gamma=4 there are exactly two possible subsequential W1 limits: these same two measures. More precisely the W1 distance to their two-element set tends to zero; a sequence can alternate phases. Both limits are realized by actual asymptotically maximizing APPT sequences. No intermediate pair of atoms is allowed.

This is sharper than equality of the scalar maximal-purity coefficients at the transition: it rules out a continuum of intermediate bulk profiles even though the elementary scalar variance bound alone would permit one.

The second empirical moments do NOT follow from (R4). They satisfy instead

    integral x^2 d mu_m -> K_gamma/gamma.                      (R5)

For gamma<4 all of this second moment escapes a bulk concentrated at zero. For gamma>4 the bulk contributes one, while 4/gamma escapes in a vanishing fraction of spectral outliers. W1 convergence is not being incorrectly promoted to W2 convergence.

## 2. Physical graph bound and an exact defect decomposition

The necessary quantum test in SHARP_ASYMPTOTIC.md Section 2 assigns the paired gaps to arbitrary edges of K_m and proves operator norm at most 2b. After division by b every rearranged adjacency matrix has norm at most 2. This assertion follows from physical global-unitary tests, not from a chosen arrangement alone.

If b were zero, the single-edge consequence would give lambda_1=lambda_D, forcing the normalized spectrum to be uniform and b>0, a contradiction. For (R1), the first D-S+1 or the last S coordinates give, according to the sign of b-1/D,

    |Db-1| <= sqrt{D^2 V/min(D-S+1,S)} ->0,
    V=sum_i lambda_i^2-1/D.                                   (R6)

In particular W:=V/b^2 tends to K_gamma.

Place eta_i in decreasing order in the upper triangle row by row, and let G be the resulting zero-diagonal symmetric matrix. Write e=m^(-1/2)(1,...,1), Q=||Ge||^2,

    H=sum_{i=1}^h eta_i^2, T=sum_{i=h+1}^R eta_i^2,
    u=4h/m, C=max(8,4+D/h^2).

The following FOUR defects are all nonnegative:

    s1=4-H,
    s2=4-Q-u w A-h^2 w^2,
    s3=Q-T,
    s4=H+T+w A+D w^2/4-W.                                    (R7)

For s1 use a star arrangement of the h largest original g_i. For s2 use
`|| (G+w A_complete)e ||^2<=4` and expand the background cross term. For s3 use the decreasing triangular degree inequality. For s4 center the eigenvalues at the midpoint of the final top/bottom pair; details are given in Section 5 below. These are the same finite inequalities used in the unrestricted upper bound, here retained with all their defects.

Exact addition gives, when D<=4h^2,

    C-W=(h^2-D/4)w^2+(u-1)w A+s1+s2+s3+s4,                    (R8)

and, when D>=4h^2,

    C-W=(D/4-h^2)(4/h^2-w^2)+(u-1)w A+s1+s2+s3+s4.            (R9)

The all-ones Rayleigh bound gives 0<=hw<=2, so every term displayed is nonnegative. By (R1) and (R6), C-W->0. Hence

    s1,s2,s3,s4 ->0, and w A->0.                              (R10)

For gamma<4, (R8) also forces hw->0; for gamma>4, (R9) forces hw->2. At gamma=4 these scalar expressions alone do not force either endpoint, so a further matrix inequality is required.

## 3. Triangular saturation forces subquadratic-rank concentration

Let E_t be the sum of squared weights in triangular row t (which has m-t entries), and d_t the weighted degree of vertex t. For 1<=t<=m-2, decreasing assignment gives

    d_t^2/m >= kappa_t E_{t+1},
    kappa_t=h^2/[m(m-t-1)] >=1.

Indeed all incoming and outgoing weights at vertex t are at least the smallest weight of row t, whereas every weight of row t+1 is at most that value. Therefore

    Q-T >= sum_{t=1}^{m-2}(kappa_t-1)E_{t+1},
    kappa_t-1=[m(t-1)+1]/[m(m-t-1)].                           (R11)

An edge whose index is at least theta m^2 must occur in row at least theta m, because every row has at most m entries. For all sufficiently large m, (R11) consequently gives the safe bound

    sum_{i>=ceil(theta m^2)} eta_i^2 <= (4/theta)(Q-T).          (R12)

Since s3=Q-T->0, this proves (R2). Also H+T<=8. Splitting A at ceil(theta m^2) and applying Cauchy--Schwarz to each part yields

    limsup A/m <=sqrt(8 theta).

Let theta decrease to zero to obtain A/m->0. This argument works at the critical ratio as well as in both open phases. Put

    alpha=e^T G e=2A/m ->0.                                  (R13)

## 4. A new matrix obstruction rules out intermediate critical profiles

Let B=G+w A_complete. This is a permitted arrangement of the normalized original gaps, so 2I-B is positive semidefinite. Also B and y=Ge are entrywise nonnegative. Applying Cauchy--Schwarz in the positive-semidefinite quadratic form 2I-B gives

    [(2-hw)alpha-Q]^2 <= 2Q(2-alpha-hw).                       (R14)

Here

    e^T(2I-B)e=2-alpha-hw,
    e^T(2I-B)y=(2-hw)alpha-Q,
    y^T(2I-B)y=2Q-y^T B y<=2Q.

Thus (R14) is a finite matrix inequality, not a guessed relation among limiting constants.

Now let gamma=4 and pass to any subsequence on which hw->r in [0,2]. By (R10), s2->0 and w A->0, so Q->4-r^2. Equation (R13) gives alpha->0. If 0<r<2, then Q has a positive limit, and (R14) implies

    4-r^2 <=4-2r,

which is impossible. Hence r is 0 or 2. Compactness proves

    distance(hw,{0,2})->0.                                   (R15)

At gamma<4, s1->0, s2->0 and hw->0 give H->4,Q->4,T->4. At gamma>4 they give H->4,Q->0,T->0. The same alternatives hold along each critical subsequence. Since

    sum_{i=1}^h g_i^2=H+2w sum_{i=1}^h eta_i+h w^2,

the original first h gaps always have square sum tending to four. This completes the gap-energy assertions.

For comparison, the false critical scalar configuration `r=1,Q=T=3,H=4,alpha=0` would make the old leading scalar bound an equality. It violates (R14): 9<=6 is false. The extra matrix test is essential to the two-phase conclusion.

## 5. From gap defects to actual spectral measures

Let z=(lambda_R+lambda_{D-R+1})/2. In each top/bottom pair define

    p_i=(lambda_i-z)/b-w/2 >=0,
    q_i=(z-lambda_{D+1-i})/b-w/2 >=0,
    p_i+q_i=eta_i.

The unpaired middle eigenvalues lie in [z-bw/2,z+bw/2]. The exact identity behind s4 is

    s4=2 sum_i p_i q_i
       +sum_middle [w^2/4-((lambda_i-z)/b)^2]
       +D((z-1/D)/b)^2.                                      (R16)

In particular

    m(z-1/D)/b ->0.                                          (R17)

For clarity, define X_i=m(lambda_i-z)/b and a_m=mw/2, and clip X_i to Y_i in [-a_m,a_m]. The total clipping cost is exactly

    (1/D)sum_i |X_i-Y_i|=m A/D ->0.                           (R18)

The pairs lie at the clipping endpoints, and (R16) gives

    (1/D)sum_i (a_m^2-Y_i^2) <= (m^2/D)s4 ->0.                 (R19)

If hw->0, then a_m->0 and (R18) implies average |X_i|->0. If hw->2, then a_m->1, and (R19) implies that Y_i is, in average distance, supported on the two endpoints. The mean of X_i is m(1/D-z)/b->0; hence those endpoints have asymptotically equal weights. Both statements are in W1, because all the comparisons used average absolute distances, not just weak convergence.

Finally the quantities in (R3) equal

    m(D lambda_i-1)=Db X_i+m(Dz-1).

The first coefficient tends to one by (R6), and the second term tends to zero by (R17). This proves (R4) and the critical two-limit assertion. Formula (R5) follows directly from

    (1/D)sum_i [m(D lambda_i-1)]^2=(m^2/D)D^2 V.

## 6. Both critical phases occur

At n=4m the spike-plus-broad-plateau family in ASYMPTOTIC.md has coefficient 4+n/m->8 and empirical measure in (R3) tending to `(delta_-1+delta_1)/2`. Its single spike has vanishing empirical first-moment weight, while the two broad levels tend to the indicated endpoints.

The hierarchy in MULTISCALE.md gives, for every fixed number of levels and fixed positive safety margin, actual APPT states eventually in m. Its perturbation X=B-I has trace o(m) at each fixed hierarchy. Thus the average absolute rescaled deviation is at most `2m Tr(X)/D=o(1)`. Choose increasing fixed hierarchy lengths and decreasing fixed margins, and then increasing dimensions large enough that both the scaled purity is within the prescribed error of eight and this first-moment bound is small. This diagonal selection produces a bona fide APPT sequence at n=4m with coefficient eight and limit delta_0. The order of limits is maintained; no unverified growing hierarchy is substituted into the compactness theorem.

Therefore the two critical possibilities are genuine, not merely an artifact of an incomplete converse. By (R14) there are no other subsequential empirical limits for near-maximizers, although a sequence may alternate between the two.

## 7. What is and is not classified

These are universal necessary spectral laws for all asymptotic maximizers in every fixed finite aspect ratio. The empirical profiles and the paired-gap energy allocations are determined, including the exclusion of intermediate critical bulk profiles. They explain a discontinuous change in the bulk at gamma=4 despite continuity of the scalar maximum.

They do not specify every outlier eigenvalue, prove that a rank-one spike is necessary, classify all multiscale arrangements, or characterize the exact finite-dimensional maximizers outside EXACT_RECTANGULAR.md. W1 convergence intentionally coexists with escaping second moments. Absolute separability and efficient finite hierarchy certificates remain separate questions. The proof uses the elementary unrestricted upper inequalities already derived from physical APPT tests, plus the new quadratic-form inequality (R14); it does not infer rigidity from sampled spectra.
