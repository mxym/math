# A uniform entropy formula for every dimension and growing Renyi order

Yongxian Zhang (张永贤), South China University of Technology.
15 October 2026, Asia/Shanghai. Complete author manuscript; independent
ordinary read pending. This P0-P2 target has its own quantifiers and does
not inherit a PASS from the fixed-order or onset-optimization manuscripts.

## 1. Original domain and explicit finite theorem

Let APPT(m,n) be the actual complex PSD trace-one matrices on C^m tensor
C^n remaining PPT after EVERY global unitary, with integers 2<=m<=n.
Write D=mn, E_alpha=max_APPT(log D-S_alpha), q=(m+1)/(m-1), and use
natural logarithms throughout. For EVERY real alpha>=2 set a=alpha-1 and

    T(m,D,alpha)=max{log q, log3-logD/a},
    L(D,alpha)=log(2alpha)/a+4/alpha+4/D,
    U(m,D,alpha)=2m/(D-m)+2exp(-sqrt a)+2/sqrt a+log48/a.

**P0.** The following are actual finite inequalities, with no hidden
dimension or order threshold:

    T-L <= E_alpha(m,n) <= T+U.                            (1)

**P1.** Consequently, whenever D->infinity and alpha->infinity,

    E_alpha(m,n)
      =max{log((m+1)/(m-1)),log3-logD/(alpha-1)}+o(1),      (2)

UNIFORMLY over all integer 2<=m<=n and all simultaneous growth patterns.
The smaller dimension may be fixed, grow or oscillate. This is absolute
o(1), not a relative equivalent when the displayed value tends to zero.

## 2. Finite physical spectral inputs, with no large-aspect hypothesis

Order the actual spectrum lambda_1>=...>=lambda_D and set

    R=m(m-1)/2, K=m(m+1)/2, b=lambda_(D-K+1),
    x_i=lambda_i/b, kappa=x_R-1, t=2/(m-1),
    p_i=x_i-1-kappa (i<=R), beta_j=1-x_(D+1-j) (j<=K).

The following exact finite physical inequalities are credited to
SHARP_ASYMPTOTIC.md Sections 2-4 and the cubic-entropy proof Section 4:

    b>0, 0<=kappa<=t, sum p+sum beta<=m,
    0<=x_i<=3, sum_(i<=R) p_i^2<=8.                       (3)

They do not require D comparable to m^3 or bounded c=m^2(t-kappa).
For clarity, the maximally entangled witness has disjoint top-R and
bottom-K slots because m^2<=D; it gives the first budget. The arbitrary
edge rearrangement tests give a star bound four and a row-degree-square
bound four for the shifted pair gaps eta_i, hence sum eta_i^2<=8.
Here eta_i=p_i+beta_i-beta_R>=p_i, proving the last inequality.
The single-edge witness gives lambda_1-lambda_D<=2b, which forces b>0
and x_i<=3. These are necessary tests of actual all-unitary APPT, not an
assumption that the outer spectral constraints are sufficient.
For m=2, R=1 and p_1=0, so the last bound holds directly; the other witness
bounds remain valid. No old Lean audit is enlarged or rerun.

Let s=D^-1 sum x_i be the EXACT raw mean. Only the bottom-K slots can
be below one, so the full budget in (3) yields

    s>=1-m/D>0.                                         (4)

We keep this D-dependent bound instead of replacing it by 1-O(1/m).
It is the reason fixed-m sequences are included in (2).

## 3. Uniform upper bound for the whole quantum feasible set

Take epsilon=exp(-sqrt a). If x_i>q+epsilon, then i<=R and p_i>epsilon,
since 1+kappa<=q. Equation (3) therefore bounds the number of these
indices by 8/epsilon^2, regardless of dimension, order or multiplicities.
All other indices have x_i<=q+epsilon; every index has x_i<=3. Thus

    D^-1 sum x_i^alpha
       <=(q+epsilon)^alpha+(8/epsilon^2)*3^alpha/D.         (5)

Normalize by the ACTUAL s. For each density,

    e_alpha=log D-S_alpha
          ={log[D^-1 sum x_i^alpha]-alpha log s}/a.        (6)

Using log(A+B)<=max(logA,logB)+log2 in (5) gives

    e_alpha<=-(alpha/a)log s + max{
       (alpha/a)log(q+epsilon),
       log3-logD/a+(log24)/a+2/sqrt a}+log2/a.             (7)

Here alpha/a<=2. Since 1<q<=3,

    (alpha/a)log(q+epsilon)
       <=log q+(log3)/a+2epsilon.

The two branches in (7) are therefore bounded by their respective
branches in T plus the common error 2epsilon+2/sqrt a+log24/a.
By (4) and -log(1-u)<=u/(1-u), the mean term is <=2m/(D-m).
The remaining log2/a combines with log24/a to give log48/a. This proves
the upper inequality in (1) for EVERY actual density, and hence its
attained maximum. No spectral ansatz or upper bound on anomaly count
independent of epsilon was assumed.

## 4. Two actual-state lower bounds, including integer ranks

Both constructions used below are genuinely all-global-unitary APPT.
For a unit vector v, the partial transpose of |v><v| has eigenvalues
s_i^2 and +/-s_i*s_j from its Schmidt coefficients. Since s_i*s_j<=1/2,
I+2|v><v| remains PSD after partial transpose for every global-unitary
image of v. Thus its normalization by D+2 is APPT. Its spectrum is
3/(D+2) once and 1/(D+2) repeated D-1 times, so

    E_alpha>= {log[(3^alpha+D-1)/D]-alpha log(1+2/D)}/a
             >=log3-logD/a-4/D.                          (8)

The last uses alpha/a<=2 and log(1+2/D)<=2/D.

For ANY actual projection P, I+tP is also all-global-unitary APPT:
if W is the partial transpose of a unit-vector projector, then
Tr(PW)>=sum_(negative eigenvalues of W) eigenvalue
       >=-(m-1)/2.
The latter follows from ((sum s_i)^2-1)/2<=(m-1)/2. Thus
Tr[(I+tP)W]>=1-t(m-1)/2=0 for every vector and every unitary image of P.
Normalize by D+t*k, retaining its INTEGER rank k. Choose

    k=max{1,floor(D/alpha)}, theta=k/D.

For D>=4 and alpha>=2, 1<=k<D and

    theta>=1/(2alpha), theta<=1/alpha+1/D.

If D/alpha>=2, the lower bound follows by floor(D/alpha)>=D/(2alpha);
if D/alpha<2, it follows from k>=1 and D<2alpha. The upper bound is
immediate in both cases. The exact entropy deficit of this state is

    {log[1+theta(q^alpha-1)]-alpha log(1+t*theta)}/a
     >=log q-log(2alpha)/a-4/alpha-4/D,                   (9)

since 1+theta(q^alpha-1)>=theta*q^alpha, t<=2, and alpha/a<=2.
This argument uses a real physical integer rank even when alpha exceeds
D; it never substitutes a fractional rank D/alpha smaller than one.

Combining (8)-(9), and allowing the larger error L on both branches,
proves E_alpha>=T-L. This completes all of P0. In particular the trace
loss, the case alpha>D, both actual matrices and all dimensions remain.

## 5. Uniform limit and logarithmic-order transitions

Because m<=sqrt D, m/(D-m)<=1/(sqrt D-1). Every term of L and U tends
to zero uniformly when D->infinity and alpha->infinity, proving P1.
No assumption on alpha/logD, m/n, or a fixed smaller dimension is needed.

**P2.** If m->infinity and alpha/logD->c in (0,infinity], (2) gives

    E_alpha -> max{0,log3-1/c},                            (10)

with 1/infinity=0. Thus logarithmic order has the leading transition
c=1/log3. At the critical value the limit is zero; no sharp relative
next-scale law there follows from (1).

If m is fixed, alpha->infinity and alpha/logD->c in [0,infinity], the
limit instead is

    max{log((m+1)/(m-1)),log3-1/c},                        (11)

where the second term is -infinity at c=0. For m=2 the bulk term is
already log3. For m>=3 the finite-c crossing is at
c=1/log[3(m-1)/(m+1)]. No fixed-m bounded-order limit is asserted here.

For m->infinity the c=0 conclusion E_alpha->0 also holds without assuming
alpha->infinity: set beta=alpha+sqrt(logD)>=alpha. Then beta->infinity,
beta/logD->0, and (2) gives E_beta->0. Renyi deficit is nondecreasing
in the positive order for every state, hence also after maximizing over
the same actual feasible set. Thus 0<=E_alpha<=E_beta->0. This covers
arbitrarily tiny or oscillating positive orders in this particular regime.

## 6. Evidence and exact limitations

This is a complete ordinary proof of explicit finite bounds and a uniform
absolute growing-order formula. It does not give an exact finite maximum,
every equality spectrum, sharp next terms, effective relative accuracy at
a vanishing leading value, or the fixed-order small-deficit asymptotic.
The exact physical graph bounds are credited existing inputs; no old
formalized root set is widened. Prior fixed-order/onset reviews do not
certify P0-P2 without its own source-bound read. Current primary abstract
screens found no matching growing-order statement, but are bounded and
are not a priority certificate. Independent ordinary review is pending.

No new Lean, external human peer review, major-conjecture count, external
submission, email, Release or DOI. No external funding; OpenAI AI
assistants assisted. Original rights reserved, third-party notices retained.
