# One actual peak and one body loss at every diverging APPT order

Author: Yongxian Zhang (张永贤), South China University of Technology.
ORCID 0009-0000-3864-3536; mxymmxym1@gmail.com. 15 October 2026.
New ordinary author manuscript, pending its own independent ordinary review.
No external funding. OpenAI AI assistants assisted research and writing.
Copyright2026 Yongxian Zhang; original material all rights reserved,
third-party notices retained. No new Lean scope, historical-first claim,
submission, release or completed major-problem count is asserted.

## 1. Original domain, benchmark, and what is actually reduced

Consider EVERY sequence of original complex PSD trace-one densities rho on
C^m tensor C^n which remain PPT after EVERY global unitary conjugation, with

    integers2<=m<=n, m->infinity, realalpha->infinity.          (1.1)

There is NO relation assumed among alpha,m,n,D=mn. In particular alpha/m
may approach zero, remain finite positive, diverge, or alternate between
such regimes; alpha may exceed D arbitrarily. The larger dimension has
no growth restriction. All formulas below are used after alpha>=2,m>=3,
which hold eventually. Logarithms are natural.

Let lambda_i be the decreasing ACTUAL eigenvalues, y_i=Dlambda_i, and put

    M=D^-1 sum_i y_i^alpha,
    M*=max_actual_APPT M,
    e_alpha=log D-S_alpha(rho)=log M/(alpha-1),
    E_alpha=max_actual_APPT e_alpha=log M*/(alpha-1),
    u=u_D=3D/(D+2), r=u^alpha/D, chi=log r.                  (1.2)

The original compactness/continuity arguments give the maxima. Jensen
gives M>=1. The physical cap y_1<=u is retained EXACTLY; replacing u by3
under an unbounded exponent is not permitted.

The optimized VALUE benchmark is the already proved finite scalar V from
the captured complete ALL_ORDER_VARIATIONAL.md. For0<=kappa<=2/(m-1),
0<=theta<=1 put

    eta_m(kappa)=2(m-2)kappa^2/[2-(m-3)kappa],
    V(kappa,theta)
      =[1+theta((1+kappa)^alpha-1)
           +r((3-eta_m(kappa))/3)^alpha]/(1+kappa theta)^alpha,
    V*=max_(kappa,theta) V(kappa,theta)>1.                   (1.3)

This is a credited approximating VALUE theorem over the original actual
APPT set, not a premise restricting actual spectra to its candidate family.
Section3 explains why its relative EXCESS, not merely its raw moment,
is valid across every path(1.1). The core reduction assumes no S5/S6/S7/S8
or phase4 theorem; its separate moving-tie illustration explicitly credits
the mature phase geometry. The proof uses the established G physical inequalities, G1 and
V1/V18 value theorems, and an exact chord identity already used by FAST.

The new reduction removes every exceptional eigenvalue other than the actual
largest one, uniformly at BOTH optimality scales. The middle contribution
is then represented exactly by its actual mean, width, fraction and one
bounded size-biased chord loss. It is not simply the original full moment
renamed: the nonleading exceptional coordinates are proved irrelevant,
and no assumption of an endpoint spectrum is made for the actual body.

## 2. Finite actual spectral data and a nonnegative compressed excess

Retain the common physical middle set

    R=m(m-1)/2, K_m=m(m+1)/2, j=D-K_m+1,
    B={R,...,j}, N=D-m^2+2, E={1,...,D}\B.

For all sufficiently large m, the actual pivot is positive. Define

    A=y_j>0, Aplus=y_R, kappa=Aplus/A-1 in[0,2/(m-1)],
    mu=N^-1 sum_(i in B)y_i,
    theta=(mu/A-1)/kappa ifkappa>0, otherwise theta=0.        (2.1)

Thus A=mu/(1+kappa theta) exactly, includingkappa0. For kappa>0 let

    x_i=(y_i-A)/(A kappa) in[0,1], mean_mid x_i=theta>0,
    Z_kappa=(1+kappa)^alpha-1,
    h_(alpha,kappa)(x)=[(1+kappa x)^alpha-1]/(x Z_kappa)
          forx>0,
    h_(alpha,kappa)(0)=alpha kappa/Z_kappa,
    Lambda=1-[sum_mid x_i h_(alpha,kappa)(x_i)]/[sum_mid x_i]. (2.2)

Both endpoints are attained in the actual middle set, so theta>0 and
the denominator is positive whenkappa>0. Convexity gives0<=h<=1 and
0<=Lambda<=1. Ifkappa0 setLambda1; its coefficient below is zero.
No fictitious order, multiplicity or rank is added to the actual state.

For alpha>=2 put H_alpha(y)=y^alpha-1-alpha(y-1)>=0 and define

    Z(rho)={ H_alpha(y_1)
       +N[ (mu/(1+kappa theta))^alpha
                  (1+theta Z_kappa(1-Lambda))
             -1-alpha(mu-1)] }/D,
    C(rho)=1+Z(rho).                                        (2.3)

For kappa0 interpret theta Z_kappa aszero; its Z_kappa is alsozero.
The bracket is exactly the mean of H_alpha over the ACTUAL middle spectrum,
so Z>=0 and C>=1. In particular a constant body with kappa0 does NOT
justify setting this bracket tozero: its mean mu need not equalone.
The terms alpha(mu-1),alpha(y_1-1) remain intact at arbitrarily largealpha.

Only y_1 and the four actual body scalars mu,kappa,theta,Lambda enter(2.3).
Lambda is an explicit spectral functional, not an assumption that it
vanishes. At sublinear orders Lambda may tend tozero while its small
contribution still changes the FIRST NONZERO excess; it cannot be dropped.

## 3. Exact claims and the first-nonzero benchmark

**Theorem A (uniform physical reduction).** There are universal constants
and common m/alpha thresholds such that, with rho0=15/16, for EVERY allowed
dimension/order pair and actual APPT state,

    0<= [M-C(rho)]/[M*-1] <=C_0 alpha^2 rho0^alpha,         (3.1)

and

    0<= [log M-log C(rho)]/log M*
       <=C_1[alpha^2 rho0^(alpha/2)+log(1+alpha)/alpha].     (3.2)

These are all-state bounds without an alpha/m or alpha/D hypothesis.
They cover arbitrarily small M*-1 as well as diverging log M*.

**Theorem B (explicit-benchmark necessary and sufficient criteria).** For
EVERY path(1.1),

    (M*-1)/(V*-1)->1, log M*/log V*->1,                    (3.3)

where(3.3) is a consequence of the credited value theorems, not a new
optimization claim. The complete actual-state tests are

    [M(rho)-1]/[M*-1]->1
         iff Z(rho)/[V*-1]->1;                             (3.4)

    e_alpha(rho)/E_alpha->1
         iff log[1+Z(rho)]/log V*->1.                       (3.5)

All statements are uniform in n and arbitrary order/dimension oscillation.
Equivalently, for everyL_m->infinity, the errors in(3.1)-(3.3) tend tozero
uniformly for n>=m,alpha>=L_m as m->infinity. This does not requireL_m/m
to tend toanything.

These are different scales: (3.5) must not be replaced by(3.4), and raw
M/M* may be vacuous whenM*->1. The tests contain scalar VALUE comparisons,
not distance to the instantaneous exact scalar argmax. They therefore do
not exclude states approaching a moving first-order coexistence tie from
the other side. They do not claim a new full geometric classification of
every order or a theorem for bounded positive alpha oralpha->0.

To justify(3.3) before using it, the mature G1 and V18 theorems give

    M*-1 ~ r+alpha(alpha-1)/(2m^2) ~ V*-1

on everyalpha->infinity,alpha/m->0 path, uniformly overn>=m. For each
fixedepsilon>0, V1 givesM*/V*->1 uniformlyalpha>=epsilon m. The explicit
bulk lower choice V17 makesV*-1 uniformly bounded BELOW by a positive
constant on that range for sufficiently largem. Hence there also
(M*-1)/(V*-1)->1. Any failure of the all-path or uniform statement has
a bad subsequence whosealpha/m either tends tozero or is bounded below
by a positiveepsilon; these two established cases contradict it. This
proves the relative excess claim without silently deriving it from raw
moment accuracy when both moments approachone.

IfpositiveW satisfies(M*-1)/W->1, concavity oflog(1+x) bounds
log M*/log(1+W) between1-o(1) and1+o(1), uniformlyW>0. Apply this with
W=V*-1 to prove the second statement in(3.3), even at vanishing deficit.
No new all-order VALUE input is assumed beyond those explicitly credited.

## 4. Exact centered identity and the exceptional square-mass input

The mature physical G proof gives, uniformly every n>=m and actual state
as m->infinity,

    y_1<=u, y_2<=v_m->1+sqrt(2)<3,
    Q_E=sum_(i in E)(y_i-1)^2<=C_m=O(1).                    (4.1)

The pivot positivity and width in(2.1) are the same every-global-unitary
inputs. All their ordinary physical proofs are credited, not enlarged
into a new Lean audit. For large enoughm, takev_m<=5/2,u>=8/3 andC_m
bounded by a universal constant. These common thresholds do not depend
onalpha,n or the state.

Foralpha>=2 the exact integral formula is

    H_alpha(y)=alpha(alpha-1)(y-1)^2
          integral_0^1(1-s)(1+s(y-1))^(alpha-2) ds.           (4.2)

It is valid atzero eigenvalues. It gives H_alpha>=0, and if0<=y<=V,V>=1,

    H_alpha(y)<=a_alpha(y-1)^2 V^(alpha-2),
    a_alpha=alpha(alpha-1)/2.                               (4.3)

Trace one supplies the exact centered identity

    D(M-1)=sum_i H_alpha(y_i).                              (4.4)

The actual chord definition in(2.2) gives exactly

    sum_(i in B)y_i^alpha
       =N A^alpha[1+theta Z_kappa(1-Lambda)].               (4.5)

For kappa0, the same identity readsN A^alpha. Since sum_mid y_i=Nmu,
(4.5) shows that (2.3) is precisely the sum of the actual peak kernel
and all actual middle kernels, divided byD. Thus with

    R_E=sum_(i in E,i!=1)H_alpha(y_i)>=0

one has the EXACT relation

    M=C(rho)+R_E/D.                                        (4.6)

Using the actual second peak and bounded square sum rather than the
cardinalitym^2-2, (4.3) yields

    R_E<=a_alpha C_m v_m^(alpha-2)
        <=C_2 alpha^2 rho0^alpha u^alpha.                  (4.7)

The other exceptional eigenvalues are not set tozero; their full centered
power contribution is bounded at its appropriate scale.

## 5. A true optimum lower bound at arbitrarily tiny excess

The credited physical spike rho_sp=(I+2vv*)/(D+2) is APPT under every
global unitary, since the least eigenvalue of any partially transposed
pure projector is at least-1/2. Its exact moment is

    M_sp=[u^alpha+(D-1)t_D^alpha]/D, t_D=D/(D+2).

For realalpha>=1, Bernoulli/convexity gives1-t_D^alpha<=alpha(1-t_D), so

    D(M_sp-1)>=u^alpha-1-2alpha.

Becauseu>=8/3 for large enoughm, (1+2alpha)/u^alpha->0 uniformlyalpha->infinity.
After a universalalpha threshold this gives

    M*-1>=r/2>0,
    L*=log M*>=log(1+r/2).                                 (5.1)

Noalpha/D expansion was used. Combining(4.7) and(5.1) proves(3.1).
This retains the first nonzero scale whenr is extremely small, regardless
of whether the true optimum is governed instead by a much larger body term.

## 6. A polynomial actual-peak comparison for EVERY state

Taking a logarithm of(3.1) alone would not prove(3.2) whenM* is large.
We need a different all-state bound, valid without assuming the actual
peak is near its cap. Putx_1=y_1-1>=0 andH_1=H_alpha(y_1).

Forx>=0, (4.2) showsH_alpha(1+x)/x^2 is nondecreasing inx whenalpha>=2.
For negative deviations-1<=x<=0, the same identity gives
H_alpha(1+x)<=a_alpha x^2.

Ifx_1>=1/alpha, all positive other exceptional deviations satisfy

    H_alpha(y_i)<= (y_i-1)^2 H_1/x_1^2
                 <=alpha^2(y_i-1)^2 H_1.

Their square sum is bounded by(4.1), while all negative ones contribute
at mostC_m a_alpha. ThereforeR_E<=C alpha^2(1+H_1).
Ifx_1<1/alpha instead, every positive deviation obeys
(1+x_i)^(alpha-2)<=exp(1), so(4.3) gives the same bound (in fact
R_E<=C alpha^2). This also handlesx_1=0; trace one then makes all
eigenvalues uniform.

We have consequently proved, uniformly EVERY actual state,

    R_E<=C_3 alpha^2[1+H_1].                               (6.1)

The exact positivityD C(rho)=D+H_1+sum_mid H_alpha(y_i)>=1+H_1 now gives

    1<=M/C(rho)<=1+C_3 alpha^2,
    0<=log M-log C(rho)<=log(1+C_3 alpha^2).                (6.2)

This bound uses no actual y_1->3 assumption. It includes negative-hole
states, a constant actual middle, and states with an exceptionally small
true deficit. The inequality relies onalpha>=2, explicitly eventual in(1.1).

## 7. Three exhaustive log regimes and uniform entropy error

Writeeta=-log rho0>0. Equations(4.6)-(4.7) give

    0<=Delta:=log M-log C(rho)
       <=R_E/D<=C_2 alpha^2 exp(chi-eta alpha),             (7.1)

usingC(rho)>=1. In addition(6.2) givesDelta=O(log(1+alpha)).
The following cases exhaust EVERY dimension/order pair:

1. Ifchi<=0, thenr<=1 and(5.1) givesL*>=r/3. Divide(7.1) by this
   lower bound to getDelta/L*<=3C_2 alpha^2 exp(-eta alpha).
2. If0<chi<=eta alpha/2, thenL*>=log(3/2), while(7.1) is at most
   C_2 alpha^2 exp(-eta alpha/2). ThusDelta/L* has the same vanishing
   bound up to a universal constant.
3. Ifchi>eta alpha/2, then(5.1) givesL*>=chi-log2>=eta alpha/4 for
   largealpha. The polynomial comparison(6.2), rather than a coarse
   optimum-relative moment error, now givesDelta/L*=O(log(1+alpha)/alpha).

This proves the explicit bound(3.2). Constants and thresholds are common,
not chosen after fixing a relation betweenalpha andm or a state. Asalpha
diverges the bound vanishes even on paths which alternate among all three
regimes. In particular no division by a tinyL* was left uncontrolled:
the r factor cancels in the first regime using the actual spike lower bound.
In the last regime the logarithmic benchmark is at least a fixed multiple
ofalpha, making the polynomial actual-peak comparison sufficient.

## 8. Necessary and sufficient criteria and why the losses remain

BecauseZ=C(rho)-1, (3.1) gives uniformly

    (M-1)/(M*-1)-Z/(M*-1)->0.

The benchmark(3.3) proves both directions of(3.4). Since
e_alpha/E_alpha=log M/log M*, the uniform logarithmic bound(3.2) and
the second part of(3.3) prove both directions of(3.5). These are exact
criteria for EVERY actual state path, not only a lower-bound construction.

The body in(2.3) cannot be reconstructed from width and mean alone:
Lambda retains its power-law departure from the convex endpoint chord.
Its definition resolves the entire upper layer at superlinear orders,
and at sublinear orders retains effects at the small quadratic excess
scale even whenLambda itself tends tozero. Omitting it assumes an
endpoint body without a physical reason. Likewise replacingmu byone
before exponentiating or discardingalpha(mu-1) is invalid at unrestricted
alpha. The finite regressions retain actual mean errors and actual
nonzero chord losses; they do not prove the universal theorem.

One may NOT replace(3.5) by raw moment optimality. The earlier actual
G protected-spike example in square dimensions,alpha=m andrho proportional
toI+(2-alpha^-1/2)vv*, has entropy ratio tending toone but loses its
whole sharp moment ratio. Conversely rawM/M* nearone need not establish
either first-nonzero optimum: the actual maximally mixed state with
m=n,alpha=log log m hasM=1,M*->1,soM/M*->1, butZ=0 and its entropy
deficit iszero. These credited/elementary actual examples expose both errors.

Finally an instantaneous exact argmax distance is not interchangeable with
these value tests at moving coexistence. A separate COVERAGE_AND_LIMITS.md
records a full actual-state counterexample from the already established
finite-window geometry. No such distance substitution occurs in(3.4)-(3.5).

## 9. Exact limitations and attribution

This is a global diverging-order PHYSICAL REDUCTION, not a new solution of
the underlying value optimization or a complete geometric all-positive-order
classification. The benchmark is the explicit credited finite scalar V*;
the four body quantities are computed from each actual state, and the
nonnegative centered representation is proved before using optimality.
It neither supposes that every tuple of these quantities is APPT nor
claims that the peak and body can independently be saturated.

All existing explicit geometric criteria in their proper ranges retain
their separate sources and review status. Pending S6/S7/S8 and root's
developing zero-order path work are not used or automatically certified.
No finite-positive orzero-order theorem, fixed-m path, exact finite
optimizer, eigenvector rigidity, absolute separability, historical priority
or new Lean audit is inferred. SOURCE_INPUTS.json and THEOREM_MAP.md bind
the mature inputs and this new scope. Ordinary finite controls supplement
the proof but cannot replace all-state uniform estimates. Independent
ordinary review of THIS complete new argument remains pending.
