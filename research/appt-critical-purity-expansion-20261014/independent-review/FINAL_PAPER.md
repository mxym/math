# Uniform two-order critical APPT purity and every optimizing head/rank

Ordinary written proof, 14 October 2026. Independently reviewed.
The feasible set is the original complex all-global-unitary APPT density set.
No new Lean execution, audit expansion, or absolute-separability assertion.

## 1. The full uniform critical statement

Let D=mn, 3<=m<=n, and P_max(m,n) be maximal actual APPT purity. Let
P_G(m,n) be the exact best integer-rank q-projection purity,
q=(m+1)/(m-1). Fix any A>0, put

    a_m=(n-m^2/4)/m, |a_m|<=A, [x]_+=max(0,x).          (1)

**Theorem B0-B2.** Uniformly over EVERY integer pair in (1), as m->infinity,

    D^2(P_max-P_G)
      =[(5-4a_m)/m+(16a_m^2-44a_m+37)/m^2]_+
                                                    +O_A(m^-3). (2)

That is, one constant and one dimension cutoff work for all these pairs.
The statement includes arbitrary changes of a_m and repeated crossings.
It concerns the ACTUAL maximum, not solely a trial spectrum.

For every below-onset pair n<N_2(m)=ceil((m^2+5m+7)/4) in this window,
the reviewed exact W0-W3 theorem says every optimizing matrix is

    rho=(I+kappa Pi+p|v><v|)/(D+kappa k+p),
    kappa=2/(m-1+z), p=(2+kappa)z/(z+2),
    c=m^2[2/(m-1)-kappa],                              (3)

with Pi a rank-k orthogonal projection and unit v in its range. EVERY
genuine optimizing scalar/rank pair satisfies, uniformly,

    z=2+(28-16a_m)/m+O_A(m^-2),
    p=1+(8-4a_m)/m+O_A(m^-2),
    c=4+(56-32a_m)/m+O_A(m^-2),
    k=(m-1)n/2-3m/4+O_A(1).                            (4)

All actual integer ties and unitary conjugates are retained. No unique
integer or scalar winner is claimed below onset. Above onset the already
reviewed unique-rank q family remains the exact optimizer.

Credited immutable inputs are Q0-Q3
`appt-exact-purity-onset-20261014/PAPER.md` and W0-W3
`appt-critical-purity-optimizer-20261014/PAPER.md`. W gives an exact full-set
finite critical-window formula and every equality matrix; Q gives the
exact eventual integer onset. Those are substantive inputs, not conclusions
reproved by a scalar ansatz here. Their independent ordinary reviews and
the original Lean audits remain separate.

## 2. Exact continuous comparison and uniform integer loss

For z in [1,3] put t=2/(m-1), kappa=2/(m-1+z), p=(2+kappa)z/(z+2),

    c=2m^2 z/[(m-1)(m-1+z)], b_m=(m^2-1)/(4m^3),
    B'=D(1+kappa)-kappa p-p^2,
    P_bound(z)=(2+kappa)^2/(4B'),
    P_B=(2+t)^2/[4D(1+t)].                             (5)

Every endpoint one-head state is genuinely APPT; W proves that its
exact integer-rank maximum, together with P_G, equals P_max. The continuous
trace optimum P_bound need not be an actual integer-rank state. Define

    F_m(z,a)=D^2[P_bound(z)-P_B]=R_m V_m,
    V_m=p^2+kappa p-(1/4+a/m)(c-b_m c^2),
    R_m=(2+t)^2/{4(1+t)[1+kappa-(kappa p+p^2)/D]},
    D=m^3(1/4+a/m), a=a_m.                            (6)

These are EXACT identities from Q's signed trace-normalized comparison.
For bounded a and large m all denominators are positive uniformly on
z in [1,3]. Writing u=1/m, every displayed rational function is analytic
in u,z,a at u=0 after replacing 1/D by u^3/(1/4+a u).

Let P_one be the ACTUAL scalar/integer maximum in W. At each z the raw
trace is S=D+kappa k+p. Its optimal real trace is S_*=2B'/(2+kappa), and
its exact integer loss is

    P_bound(z)-P(z,k)
        =(2+kappa)^2(S-S_*)^2/(4B'S^2).                (7)

A nearest integer to the real optimal rank gives |S-S_*|<=kappa/2.
Both adjacent ranks fit the physical counts uniformly on [1,3], by W.
The winning rank is the better of the TWO actual branch values, rather
than a presumed nearest-only rule. Thus uniformly

    0<=max_z F_m(z,a)-D^2(P_one-P_B)<=C_A m^-5.         (8)

Indeed kappa=O(m^-1), B',S are comparable to D~m^3/4, and (7) costs
O(kappa^2/D^3); multiplication by D^2 gives O(m^-5). The exact q-rank
loss similarly gives 0<=D^2(P_B-P_G)<=C_A m^-5.
Since W proves P_max=max(P_G,P_one),

    D^2(P_max-P_G)=[max_z F_m(z,a)]_+ +O_A(m^-5).       (9)

The positive-part operation is one-Lipschitz. This step connects all the
following scalar analysis to the ENTIRE physical maximum, across the
phase transition and with actual trace/rank normalization intact.

## 3. Uniform rational coefficients and their maximization

Expand (6) uniformly on compact z,a sets, also in its first two z derivatives:

    F_m(z,a)=f_0(z)+u f_1(z,a)+u^2 f_2(z,a)+O_A(u^3),
    f_0(z)=-z(z-2)^2/[2(z+2)^2].                       (10)

The coefficients needed at its unique zero maximum z=2 are

    f_0''(2)=-1/8,
    f_1(2,a)=5-4a, partial_z f_1(2,a)=7/2-2a,
    f_2(2,a)=12a-12.                                   (11)

Here is a direct rational computation that makes the coefficients
reproducible. With u=1/m, substitute

    t=2u/(1-u), kappa=2u/[1+(z-1)u],
    p=(2+kappa)z/(z+2), c=2z/{(1-u)[1+(z-1)u]},
    b_m=(u-u^3)/4, delta=1/4+a u

in (6). R_m=1-2u+(2z+3)u^2+O_A(u^3). Multiplication by
V_m gives f_0 in (10). At z=2 the first two V coefficients are
5-4a and 4a-2, so f_2(2,a)=(4a-2)-2(5-4a)=12a-12.
Differentiation before setting z=2 gives the derivative in (11).
All remainders and their z derivatives are uniform because the rational
denominators stay bounded away from zero for |a|<=A and z in [1,3].

Outside any fixed small neighborhood of 2, f_0 has a uniform strictly
negative maximum. Inside a sufficiently small neighborhood f_0''<0.
Thus for small u uniformly in |a|<=A, every maximum of F_m lies inside
that neighborhood and F_m'' is bounded above by a fixed negative constant.
There is a UNIQUE real compact-interval maximizer z_c. Its stationary
equation gives first z_c-2=O_A(u), then

    z_c=2+(28-16a)u+O_A(u^2).                          (12)

Taylor expansion at this maximizer, using (11), proves

    max_z F_m
      =(5-4a)u+{12a-12+4(7/2-2a)^2}u^2+O_A(u^3)
      =(5-4a)u+(16a^2-44a+37)u^2+O_A(u^3).             (13)

The stationary displacement contributes 4(7/2-2a)^2; keeping z=2
would miss this essential nonzero second-order term. Equations (9) and
(13), with the one-Lipschitz positive part, prove (2) uniformly.
At a=5/4 the second coefficient is 7, consistent with the constant
7/4 in the separate exact integer onset; neither replaces its full proof.

## 4. EVERY actual optimizing head and integer rank

Consider a below-onset optimizing pair (z,k). W establishes its exact
nonbulk family and puts z in [1,3]. By (8), its continuous value is
within C_A m^-5 of max_z F_m. All such z are therefore in the same strict
curvature neighborhood eventually. At its stationary maximizer z_c,

    max_z F_m-F_m(z,a)>=c_A|z-z_c|^2, c_A>0.            (14)

Consequently EVERY genuine integer/scalar winner has
|z-z_c|=O_A(m^(-5/2)), whether or not there are ties. In combination with
(12) this gives the z formula in (4). Substitution into the exact p and
c expressions in (3),(5) gives the other two continuous formulas in (4).
No derivative of a discontinuous selected integer-rank branch is used.

For every fixed z the integer winner is floor or ceiling of

    k_* =D/(2+kappa)-p(2+kappa+2kappa+2p)/[(2+kappa)kappa].

The exact identity
D/(2+kappa)-(m-1)n/2=n z/[2(m+z)]
has right side m/4+O_A(1) by (4). The second term in k_* is m+O_A(1).
Rounding changes the rank by at most one. Hence every winning rank is
(m-1)n/2-3m/4+O_A(1), including all true integer ties. This completes B1/B2.

## 5. Scope and verification status

The theorem is uniform on each stated linear-width critical window, with
no effective cutoff or error constant supplied. It is not a next-order
purity theorem for all possible dimension-growth regimes. The exact q
parity value, exact eventual threshold, and finite one-head classification
are credited prior results. Here the new conclusions are the uniform
two-order actual critical value and rates for EVERY optimizing head/rank.

All original quantum definitions, prior manuscripts, Gaussian worktree
changes, and formal audit roots remain unchanged. No complete entropy-axis
or ASEP theorem, scalar uniqueness below onset, new major-conjecture count,
external human review, submission, Release, or Lean certificate is asserted.
Complete independent ordinary review passed with source-bound coverage; exact
symbolic and finite controls supplement that review rather than replace it.
