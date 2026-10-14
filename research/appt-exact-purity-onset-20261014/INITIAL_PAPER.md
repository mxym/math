# The exact eventual rectangular onset of maximal APPT purity

Ordinary written proof, 14 October 2026. Proposed; independent review pending.
All matrices are the original complex all-global-unitary APPT density matrices.
No new Lean execution, new audit root, or absolute-separability claim.

## 1. Statement and credited inputs

For integers 3<=m<=n let D=mn and let P_max(m,n) maximize Tr(rho^2)
over density matrices whose partial transpose is positive after EVERY
global unitary. Set t=2/(m-1). Let P_G(m,n) be the exact maximum among

    rho_k=(I+t Pi_k)/(D+t k), integer 0<=k<=D,             (1)

where Pi_k is any rank-k orthogonal projection. These are actual APPT.
Define the minimal EVENTUAL onset

    N_2(m)=min{integer N>=m: EVERY integer n>=N
                                    has P_max(m,n)=P_G(m,n)}.   (2)

Its existence is a credited consequence of the previously reviewed
fixed-m all-positive-order theorem. The new result is as follows.

**Theorem Q0-Q3.** There exists an integer M such that, for EVERY integer
m>=M,

    N_2(m)=ceil(B_m), B_m=(m^2+5m+7)/4.                  (3)

For all such m and EVERY n>=ceil(B_m), every maximizing matrix, and only
such a matrix, is (1) with the UNIQUE rank

    k=ceil((m-1)n/2).                                   (4)

Writing H=n(m^2-1), its exact purity is

    P_max(m,n)=m/H                         if (m-1)n is even;
    P_max(m,n)=m(H+2)/(H+1)^2               if (m-1)n is odd.     (5)

An actual APPT state strictly beats P_G at n=ceil(B_m)-1 for each m>=M.
Thus (3) concerns the minimal onset for ALL larger n, not only a sufficient
region or a crossing within a selected family. M is not made effective.
The assertion is false if extended indiscriminately to every small m.

We credit the immutable ordinary manuscripts
`research/appt-cubic-entropy-20261014/PAPER.md` (C0-C4) and
`research/appt-exact-cubic-bulk-20261014/PAPER.md` (E0-E4).
Their full physical upper, critical compactness, exact graph witness,
relative entropy estimate, and all-larger-n coarse onset are used below.
The older scalar q-rank optimization underlying (5) is also credited;
the new claim is its exact minimal EVENTUAL domain (3).

## 2. Physical coordinates and an exact purity comparison

Use the physical coordinates already established in C0/E0. For any actual
APPT eigenvalue list lambda, decreasing and of trace one, put

    R=m(m-1)/2, K=m(m+1)/2, b=lambda_(D-K+1)>0,
    x_i=lambda_i/b, kappa=x_R-1, c=m^2(t-kappa),
    p_i=x_i-1-kappa (i<=R), beta_j=1-x_(D+1-j) (j<=K),
    T=sum p_i+sum beta_j, E=sum p_i^2+sum beta_j^2.        (6)

Both lists are decreasing nonnegative; pad them with zeros when comparing
across dimensions. Their exact finite bounds are

    0<=kappa<=t, T<=c/2, T<=m, E<=34, 0<=x_i<=3.          (7)

Clip x to [1,1+kappa], obtaining y. Let S=sum x_i and
Delta=sum p_i-sum beta_j. Then sum y_i=S-Delta. The endpoint chord gives

    sum y_i^2 <=(2+kappa)sum y_i-D(1+kappa).

The raw square-sum increment is exactly
2 Delta+2 kappa sum p_i+E. Consequently, with a=2+kappa,

    sum x_i^2 <=a S-B', B'=D(1+kappa)-kappa T-E.          (8)

Whenever c is bounded and D is of order m^3, B'>0 for all sufficiently
large m. Maximizing the right side of (8)/S^2 over real S>0 gives

    P(rho)<=a^2/(4B')=:P_bound.                         (9)

The real-rank q-body maximum is

    P_B(t)= (2+t)^2/[4D(1+t)]=m^2/[D(m^2-1)].           (10)

It is an upper bound on P_G, not necessarily an actual integer-rank state.
Let delta_m=D/m^3=n/m^2 and b_m=(m^2-1)/(4m^3). The following signed
comparison is EXACT, without an asymptotic normalization replacement:

    V=E+kappa T-delta_m(c-b_m c^2),
    P_bound-P_B(t)=(2+t)^2 V/[4D(1+t)B'].               (11)

Indeed
(2+t)^2(1+kappa)-(2+kappa)^2(1+t)
=(t-kappa)(t+kappa+t kappa), and multiplication by D/(2+t)^2
equals delta_m(c-b_m c^2). This proves (11).

## 3. Every potentially profitable spectrum is localized

The credited E0-E4 alpha2 theorem gives a constant A, enlarged if needed
to A>3, such that all n>=m^2/4+A m have exact bulk equality and precisely
its equality matrices. It remains to prove the upper in the band

    ceil(B_m)<=n<=m^2/4+A m.                            (12)

Throughout this band delta_m->1/4 uniformly. Consider ANY actual APPT
state with P(rho)>=P_G. Equivalently its order-two deficit e_2=log(D P)
is at least G_2=log(D P_G). E0 Section 5 gives c bounded by one fixed
constant, uniformly over these states and the entire band.

We must exclude convergence to the empty critical profile when c>0.
The E0 relative comparison, its exact integer interval maximum, and its
body-loss bound give

    D[e_2(rho)-G_2] <= E-delta_m c(1-C/m)+C c/m
                       <=c^2/4-delta_m c+C'c/m,         (13)

using E<=T^2<=c^2/4. Constants are uniform at bounded c and delta_m in a
fixed compact neighborhood of 1/4; the errors remain proportional to c.
For all large m the right side is strictly negative for 0<c<=1/4.
Thus a potentially profitable state with c>0 has c>1/4.

C0 says the largest D(e_2-G_2) tends to F_2(1/4)=0. Hence every sequence
of the potentially profitable states just considered has D(e_2-G_2)->0.
C4 applies to their ENTIRE actual spectra. Its critical maximizing set is

    empty lists, c=0; or p=(1,0,...), beta=0, c=4.       (14)

The first branch is excluded by (13). It follows that, UNIFORMLY over
all potentially profitable actual states with c>0 in (12),

    p:=p_1->1, c->4, tau:=T-p->0.                       (15)

Uniformity follows by sequential contradiction: any failures at arbitrarily
large m give an actual sequence in the cubic regime to which C0/C4 apply.
In particular eventually 0.9<=p<=1.1, and every other positive or negative
anomaly is at most eta=1/100. None of this assumes a finite-head optimizer
or an a priori one-positive-head reduction.

## 4. Exact domination of ALL remaining anomaly mass

The actual Schmidt witness for any assignment of the two lists to the
negative edges and positive edges/diagonals is

    (2+kappa)I-kappa 11^T-P >=0,                        (16)

where P is symmetric nonnegative, its off-diagonal weights are the
assigned positive plus negative anomalies, and its diagonal is 2 beta.
Necessity for every assignment is an original all-unitary APPT consequence,
as proved in C0 Section 6. At bounded c and large m, kappa>0 and aI-P is
positive definite. The exact rank-one identity is

    c>= [kappa m^2 a/(m-1)] K_a(P),
    K_a(P)=1^T(aI-P)^(-1)1-m/a.                         (17)

Put p on one edge. Fill EVERY remaining slot with every other original
anomaly. The nonnegative walk expansion preserves all walks from this
edge and the first walk from the rest, giving

    c>=C_eff(kappa,p)+g_eff(kappa)tau,
    C_eff=2 kappa m^2 p/[(m-1)(2+kappa-p)],
    g_eff=2 kappa m^2/[(m-1)(2+kappa)].                  (18)

There is no discarded growing tail, no unfilled physical slot, and no
additive error independent of tau. This bound also covers overlap between
the other anomalies and the selected edge.

For 0.9<=p<=1.1 let c_0=c_0,m(p) be the unique solution on (0,m^2 t) of

    c_0=C_eff(t-c_0/m^2,p), kappa_0=t-c_0/m^2.          (19)

Existence and uniqueness follow from the endpoint signs and the derivative
of F(c)=c-C_eff(t-c/m^2,p):

    F'(c)=1+2p(2-p)/[(m-1)(2+kappa-p)^2]>1.             (20)

Uniformly in this p interval, c_0->4p/(2-p) and is bounded. Also
1<=F'<=1.1 eventually on the segment from c_0 to bounded c, and
g_eff>=1.8. Equations (18)-(20) therefore imply

    c>=c_0, c-c_0>=1.6 tau.                            (21)

Define the exact one-head relaxed profit

    V_0(p)=p^2+kappa_0 p-delta_m(c_0-b_m c_0^2).         (22)

Since all the other anomalies are at most eta, E<=p^2+eta tau. Direct
subtraction of (22) from (11), using kappa-kappa_0=-(c-c_0)/m^2, gives

    V-V_0 <=(eta+kappa)tau-p(c-c_0)/m^2
              -delta_m[(c-b_m c^2)-(c_0-b_m c_0^2)].

For large m, kappa<=1/100, delta_m>=0.24, and 1-2b_m u>=0.9 along the
bounded segment c_0<=u<=c. Hence by (21)

    V<=V_0-tau/4.                                     (23)

This is a strict full-list cost comparison. It permits scalar upper
analysis only AFTER the unrestricted actual critical localization and
the retained tail bound; it is not a trial-family assumption.

## 5. The finite one-head crossing to constant order

Parameterize (19) by z>0. The exact formulas are

    kappa_0=2/(m-1+z), a_0=2+kappa_0,
    p=a_0 z/(z+2)=2z(m+z)/[(m-1+z)(z+2)],
    c_0=2m^2 z/[(m-1)(m-1+z)],
    c_0-b_m c_0^2=m z(2m+z)/(m-1+z)^2.                 (24)

For the p interval above and large m the corresponding z lies in [1,3].
Solving V_0=0 for n gives

    h_m(z)=4m(m+z)[z(m+z+1)+2]/[(2m+z)(z+2)^2],
    V_0=(c_0-b_m c_0^2)[h_m(z)-n]/m^2.                 (25)

We need its maximum on this compact interval, not a universal assertion
that one head optimizes every finite APPT system. With u=1/m, uniformly
in z in [1,3] together with its first two z derivatives,

    h_m(z)/m^2=r_0(z)+u r_1(z)+u^2 r_2(z)+O(u^3),
    r_0=2z/(z+2)^2,
    r_1=(3z^2+2z+4)/(z+2)^2,
    r_2=(z^3/2+z^2+2z)/(z+2)^2.                        (26)

The rational denominator is bounded away from zero after dividing by its
appropriate m powers, proving this uniform analytic expansion. r_0 has
its unique maximum at z=2, r_0''(2)=-1/32. Its derivative has one positive
then negative sign change. Thus away from any small fixed neighborhood of
2 its maximum has a fixed strict gap and its derivative has a fixed sign.
Inside a sufficiently small neighborhood its second derivative is negative.
For small u these properties persist, giving a unique compact-interval
maximizer z_m^*. The implicit function theorem at (z,u)=(2,0), or Taylor
expansion of the critical equation, gives

    z_m^*=2+8/m+O(m^-2),
    max_(1<=z<=3) h_m(z)
        =m^2/4+5m/4+7/4+O(m^-1)=B_m+O(m^-1).          (27)

Here r_1(2)=5/4, r_1'(2)=1/4, r_2(2)=3/4; the displacement adds
r_1'(2)*8+r_0''(2)*8^2/2=1 to the constant term.

For the lower we need no algebraic optimal root. Use the RATIONAL choice
z_m=2+8/m. Exact subtraction gives

    h_m(z_m)-B_m
       =(21m^3+24m^2+36m-112)
                         /[4(m+2)^2(m^2+m+4)]=O(m^-1).          (28)

The displayed remainder is positive for every integer m>=2.

## 6. Integer locking and the unrestricted all-larger-n upper

For integer m, the fractional part of B_m is 1/4 or 3/4: it is 3/4
when m mod4 is 0 or 3, and 1/4 when it is 1 or 2. Therefore

    ceil(B_m)-B_m>=1/4,
    B_m-[ceil(B_m)-1]>=1/4.                             (29)

By (27), for all large m and every n>=ceil(B_m), h_m(z)-n<=-1/8 throughout
[1,3]. The positive coefficient c_0-b_m c_0^2 is bounded below by a
fixed constant on that interval. Thus V_0<=-a_1/m^2 there, with a_1>0.
For any potentially profitable state with c>0 in (12), (23) implies the
same strict negative bound on V. Since B' is comparable to D, (9)-(11)
give

    P(rho)<=P_B(t)-a_2/(m^2 D^2), a_2>0.                (30)

The exact integer q-body rounding loss is

    P_B(t)-P_G=0                           if (m-1)n is even;
    P_B(t)-P_G=m/[H(H+1)^2], H=n(m^2-1)    if (m-1)n is odd.    (31)

Within (12), this is O(m^-11), whereas the strict margin in (30) is of
order m^-8 uniformly. Thus (30) contradicts P(rho)>=P_G eventually.
Every potentially profitable state must have c=0, whence T=0 and
kappa=t by (7), and its entire raw spectrum lies in [1,1+t]. The exact
integer interval theorem E0 Section 2 classifies every equality as (1).
Above the band the credited E0 theorem applies. These overlapping regions
cover EVERY n>=ceil(B_m), without an upper restriction on n.

For completeness the unique rank and (31) follow directly from the old
scalar q optimization. P(rho_k)=[D+(2t+t^2)k]/(D+t k)^2. Its real optimum
is k_0=D/(2+t)=(m-1)n/2 and its loss is

    P_B(t)-P(rho_k)
      =(2+t)^2 t^2(k-k_0)^2/[4D(1+t)(D+t k)^2].        (32)

The derivative has one sign change; only floor/ceil(k_0) can win. If k_0
is a half integer their numerators in (32) agree, and the larger rank has
the larger denominator, so ceil(k_0) wins strictly. If k_0 is an integer
it wins uniquely. Substitution gives (5) and (31). Strict convexity of
purity in the normalized endpoint-vertex decomposition gives exactly the
equality matrices already stated, including every unitary conjugate.

## 7. Actual boundary-PSD lower and exact trace rounding

Set n=ceil(B_m)-1, z=z_m=2+8/m, and choose kappa,p,c by (24). These are
rational and c->4. Take one raw upper value 1+kappa+p, k-1 further values
1+kappa, and D-k values 1, with k selected below. This state, after actual
trace normalization, is APPT provided both endpoint counts exceed R,K.

Here is the ORIGINAL all-unitary sufficiency at the boundary. For an
arbitrary nonnegative Schmidt vector s in m coordinates, the eigenvalues
of the transposed pure witness are s_i^2 and +/-s_i s_j, with other zeros.
The least possible spectral pairing assigns all top R values to negative
directions and all bottom K to positive directions. The excess p is on
one of the negative edges. The resulting witness is (16) with just that
one edge; all such matrices are permutation-congruent. Let P be its
single-edge matrix and a=2+kappa. Since p<a, aI-P is positive definite,
and direct inversion gives

    1^T(aI-P)^(-1)1=(m+z)/a,
    kappa(m+z)/a=1.                                   (33)

The rank-one criterion makes (16) positive SEMIDEFINITE, with equality
allowed. Therefore every Schmidt witness and every global unitary passes.
The spectral rearrangement also covers zero Schmidt coordinates. This
proves genuine physical APPT; no strict sufficient margin or necessary
relaxation has replaced the original definition.

Let B'=D(1+kappa)-kappa p-p^2. For this endpoint spectrum the chord in
(8) is equality at every k. Its trace is S=D+kappa k+p; the real optimal
trace and rank are

    S_*=2B'/a, k_*=(S_*-D-p)/kappa=D/a-O(m).             (34)

Here kappa is of order 1/m and p is bounded, so k_*/D=1/2+O(1/m).
Choose an integer k nearest k_*. For all large m this lies in [R,D-K],
which verifies the endpoint counts used in (33). Its ACTUAL purity obeys
the exact identity

    P_bound-P(rho_k)=a^2(S-S_*)^2/(4B' S^2)
                                  =O(kappa^2/D^3)=O(m^-11),    (35)

since |S-S_*|<=kappa/2. No real rank has been substituted for k.

Equations (25), (28)-(29) give V_0>=a_3/m^2 for a_3>0 eventually at
this n. By (11) the real trace optimum exceeds P_B(t) by at least
a_4/(m^2 D^2), of order m^-8. The rounding loss (35) is smaller. Hence
the actual state has P(rho_k)>P_B(t)>=P_G(m,n). This is a strict physical
counterexample to bulk equality at n=ceil(B_m)-1 for EVERY large m.
Combined with the all-larger-n upper, it proves minimality in (3).

## 8. Scope, false extension, and verification status

At m=3, the proposed indiscriminate all-m threshold would be ceil(31/4)=8.
For n=8,D=24, the actual APPT pole spectrum has raw values 3,1,...,1,
normalizing trace 26. Its purity 32/676 exceeds the q-body 3/64. APPT
follows, for example, because the minimum transposed pure-witness
eigenvalue is at least -1/2, so I+2|v><v| remains PPT for every v.
Thus the eventual qualification in Q0 cannot be removed from this proof.

The full purity leading asymptotic, complete cubic correction, and the
coarse all-positive-order onset remain separate immutable prior results.
This theorem sharpens the purity onset by controlling all actual critical
spectra, exact finite costs, second-order scalar displacement, and integer
locking. It does not supply an effective M, every finite-m onset, a next
purity expansion below onset, a varying-order entropy theorem, or ASEP.
The full manuscript needs a separate source-bound independent ordinary
review; finite controls alone are not a whole-domain certificate.
