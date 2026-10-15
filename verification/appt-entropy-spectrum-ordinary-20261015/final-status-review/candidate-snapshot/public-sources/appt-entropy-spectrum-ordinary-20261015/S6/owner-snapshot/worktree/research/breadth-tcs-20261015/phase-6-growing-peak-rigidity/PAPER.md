# Physical peak rigidity above the growing APPT moment window

Author: Yongxian Zhang (张永贤), South China University of Technology.
ORCID 0009-0000-3864-3536; mxymmxym1@gmail.com. 15 October 2026.
Author manuscript, pending independent ordinary review. No external funding.
OpenAI AI assistants assisted research and writing. Copyright 2026 Yongxian
Zhang; original material all rights reserved, third-party notices retained.
No new Lean coverage, historical-first certificate, submission or major-problem
resolution is asserted.

## 1. Original quantum domain and the precise additional range

Fix ANY finite C>0. Consider EVERY sequence of actual complex PSD trace-one
densities rho on C^m tensor C^n which remain PPT after EVERY global unitary
conjugation, for integers 2<=m<=n, and real orders satisfying

    m->infinity, alpha->infinity, alpha<=C m,
    chi=alpha log u_D-log D -> +infinity,
    D=mn, u_D=3D/(D+2).                                      (1.1)

The bound alpha<=Cm need only hold eventually. The aspect ratio n/m need
not have a limit or be bounded. Neither does alpha/m need to converge.
In particular this includes every alpha/m->c in (0,infinity) with
3^alpha/D->infinity, and arbitrary oscillation among bounded order ratios.
Since alpha/D<=C/m, replacing u_D^alpha/D by 3^alpha/D changes it by a
factor tending to one throughout (1.1). We retain u_D to measure the exact
physical peak ceiling. The eventual domain alpha>1 is essential below.

Let lambda_1>=...>=lambda_D be the ACTUAL eigenvalues, y_i=D lambda_i,
and define

    M=M_alpha(rho)=D^-1 sum_i y_i^alpha,
    M*=max_actual_APPT M_alpha,
    e_alpha(rho)=log D-S_alpha(rho)=log M/(alpha-1),
    E_alpha=max_actual_APPT e_alpha=log M*/(alpha-1),
    r=u_D^alpha/D=exp(chi), h=alpha log(u_D/y_1)>=0.          (1.2)

All logarithms are natural. The maximum exists by the credited compactness
and continuity arguments for the original APPT density set. Jensen gives
M>=1. The physical bound y_1<=u_D supplies the sign of h; no arbitrary
spectral candidate replaces the actual state in these definitions.

The full all-order VALUE inputs L/V and the bounded-aspect growing-order
theorem G already imply the value in the special subranges they cover.
The all-aspect uniform value profiles are credited, not claimed anew here.
The original actual-spectrum theorem S has finite 3^alpha/D, the FAST
spectral theorem has alpha/m->infinity, and G's arbitrary-growing-order
spectral criterion has bounded aspect. Thus none supplies the all-aspect
actual-spectrum statement in (1.1) by merely substituting r=infinity.
The phase-5 sublinear rigidity manuscript overlaps the alpha/m->0 part,
but it is NOT a dependency of the independent proof given here.

## 2. Complete actual-state criteria

**Theorem A (uniform actual moment profile).** In (1.1),

    M*/r ->1,                       log M*=chi+o(1),        (2.1)
    M_alpha(rho)/r =exp(-h)+o(1).                            (2.2)

The error in (2.2) is uniform over ALL original APPT densities at each
allowed dimension/order pair. Consequently

    M/M* ->1   iff   (M-1)/(M*-1)->1   iff   h->0.          (2.3)

The relative moment and first-nonzero excess criteria agree here precisely
because r and M* tend to infinity.

**Theorem B (relative entropy deficit).** For every such actual state path,

    e_alpha(rho)/E_alpha ->1    iff    h/chi ->0.            (2.4)

This is weaker than h->0. The denominator chi is positive eventually;
it is not replaced by alpha unless a separate chi/alpha lower bound is
available. Thus paths very close in relative terms to the growing peak
window retain the correct logarithmic resolution.

**Theorem C (the physical tail and actual moment concentration).** Either
nearoptimality in (2.3) or (2.4) implies all of

    y_1->3,
    max_(2<=i<=D)|y_i-1|->0,
    (y_2/y_1)^alpha->0,
    M/[y_1^alpha/D]->1,
    [sum_(i>=2)y_i^alpha]/y_1^alpha->0.                    (2.5)

In particular the actual state is eventually full rank. Uniform flatness
of the physical tail alone is not used to bound the SUM of its powers:
the exceptional-energy estimate and the bounded middle contribution are
needed to prove the last two assertions despite growing D.

These statements allow every aspect ratio and every bounded alpha/m
oscillation in (1.1). They impose no J/body-spread saturation condition.
The middle contribution is O_C(1), while the required actual peak moment
diverges. This is a distinct scaling fact, not an extension of the finite-r
S criterion with its three nonnegative losses left unexamined.

## 3. Credited physical facts and exact centered powers

For clarity record precisely the physical inputs used. They are G7-G18 of
the captured complete research/appt-growing-renyi/PAPER.md, not additional
assumptions on a surrogate set. For m>=3 put

    R=m(m-1)/2, K=m(m+1)/2, j=D-K+1,
    B={R,...,j}, E={1,...,D}\B,
    b=lambda_j>0, t=1/(Db),
    a_i=lambda_i/b-1, beta_i=1-lambda_(D+1-i)/b,
    g_i=a_i+beta_i for i<=R.                                (3.1)

The positivity, every-unitary witness, rearrangement and trace proofs in G
give, uniformly over every n>=m and actual APPT state as m->infinity,

    |t-1|<=nu_m=1/m+2/(m-1)->0,
    sum_(i<=m-1)g_i^2<=4,
    g_R<=2/(m-1), 0<=a_i,beta_i<=g_i for i<=R,
    y_1<=u_D,
    y_2<=v_m->1+sqrt(2)<3,
    |y_i-1|<=delta_m=O(1/m) for i in B,
    Q_E=sum_(i in E)(y_i-1)^2<=C_m=O(1),
    Q=sum_i(y_i-1)^2<=zeta_m(gamma+8),
    gamma=n/m, zeta_m->1.                                  (3.2)

The constants in O(1/m) and O(1) are independent of n and the state. We use
only sufficiently large m, after the common thresholds of G. In particular
we may arrange v_m<=5/2, u_D>=8/3 and C_m,zeta_m bounded. The set E has
m^2-2 entries, but the exceptional square sum C_m is bounded independently
of that cardinality. Omitting this distinction would invalidate the proof.

Write a_alpha=alpha(alpha-1)/2 and

    H_alpha(y)=y^alpha-1-alpha(y-1), y>=0.

For real alpha>=2 the exact integral identity is

    H_alpha(y)=alpha(alpha-1)(y-1)^2
                 integral_0^1(1-s)(1+s(y-1))^(alpha-2) ds.

Thus H_alpha>=0; for 0<=y<=V, V>=1,

    H_alpha(y)<=a_alpha (y-1)^2 V^(alpha-2).                (3.3)

Trace one gives the exact identity

    D(M-1)=sum_i H_alpha(y_i).                              (3.4)

These elementary real-power identities are valid also at zero eigenvalues.
They do not assume full rank. For all sufficiently large m, index 1 belongs
to E; separate it from the other exceptional entries in (3.4).

## 4. Uniform bounded middle term and Theorem A

Let R_B=sum_(i in B)H_alpha(y_i) and
R_E=sum_(i in E,i!=1)H_alpha(y_i). Since alpha<=Cm and delta_m=O(1/m),
(1+delta_m)^(alpha-2) is bounded by a constant depending only on C. Thus

    0<=R_B/D
       <=a_alpha(1+delta_m)^(alpha-2) Q_B/D
       <=K_C,                                              (4.1)

where K_C is independent of n, alpha, and the state after one common
large-m threshold. Indeed Q_B<=zeta_m(gamma+8),
gamma/D=1/m^2, and 1/D<=1/m^2. This explains why unrestricted n is allowed.
By the ACTUAL second-eigenvalue bound and exceptional square sum,

    0<=R_E<=a_alpha C_m v_m^(alpha-2).                       (4.2)

The exact form of (3.4) is

    M=1+y_1^alpha/D-[1+alpha(y_1-1)]/D+(R_B+R_E)/D.        (4.3)

Since 1<=y_1<=3, divide (4.3) by r to obtain

    |M/r-(y_1/u_D)^alpha|
     <=(1+K_C)/r+(1+2alpha)/u_D^alpha
                    +a_alpha C_m v_m^(alpha-2)/u_D^alpha. (4.4)

All three errors tend to zero: r->infinity by (1.1), alpha->infinity,
and the last ratio is O(alpha^2(15/16)^alpha). This is an explicit all-state
bound, proving (2.2) with the stated uniformity. In particular the supremum
over actual states has limsup M*/r<=1.

For the matching lower bound use the credited ACTUAL APPT state

    rho_sp=(I+2vv*)/(D+2).

For every global U the partially transposed pure projector Uvv*U* has least
eigenvalue at least -1/2, proving its original APPT property. Its exact
moment is

    M_sp=[u_D^alpha+(D-1)(D/(D+2))^alpha]/D>=r.

Thus M*/r->1 and log M*=chi+o(1). Formula (4.4) and h>=0 now prove
M/M*->1 iff exp(-h)->1 iff h->0. As M*->infinity and M>=1,
replacing M/M* by (M-1)/(M*-1) changes it by o(1), proving (2.3).

The lower bound is an actual density construction; it does not assert that
every list obeying (3.2) is APPT, nor that this finite-dimensional spike is
an exact maximizer at every allowed finite dimension/order.

## 5. Relative entropy: necessity of a physical peak

Because alpha>1, e_alpha/E_alpha=log M/log M* exactly. First prove that
this ratio tending to one forces y_1->3; one cannot obtain the needed
logarithmic error by simply taking logarithms in (2.2).

Suppose on a subsequence y_1<=3-epsilon, for some epsilon>0. Since
u_D->3 there exists eta>0 with log(u_D/y_1)>=eta eventually on it.
Apply (3.3) to ALL exceptional entries with the actual ceiling y_1>=1,
retaining (4.1) separately for the middle. It follows that

    M<=1+K_C+a_alpha C_m y_1^(alpha-2)/D
      <=1+K_C+O(alpha^2) exp(chi-eta alpha)
      <=1+K_C+exp(chi-eta alpha/2)                          (5.1)

eventually. The last absorption is legitimate because alpha->infinity,
not because log alpha is presumed small relative to chi. Since
chi<=alpha log3 and chi->infinity, taking logarithms of the SUM gives

    limsup log M/chi <=max{0,1-eta/(2log3)}<1,              (5.2)

where replacing the right-hand expression by a slightly larger number
below one is harmless if needed. More explicitly,
log[1+K_C+exp(chi-eta alpha/2)] is at most a fixed constant plus
(chi-eta alpha/2)_+, and the latter is at most
chi max{0,1-eta/(2log3)}. This contradicts log M*=chi+o(1)
and entropy nearoptimality. Therefore y_1->3 is necessary.

## 6. The logarithmic profile at an actual near-ceiling peak

Whenever y_1->3 (without assuming nearoptimality), one eventually has
y_1>=8/3. Dividing (4.2) by y_1^alpha gives

    R_E/y_1^alpha<=O(alpha^2(15/16)^alpha)->0.              (6.1)

Also [1+alpha(y_1-1)]/D=O(alpha/D)=o(1), using alpha<=Cm,
D>=m^2. Put T_p=y_1^alpha/D=exp(chi-h). From (4.3), (4.1),
(6.1), and the elementary exact bounds M>=1 and M>=T_p, we get

    max{1,T_p}<=M<=T_p[1+epsilon_m]+1+K_C,
    epsilon_m->0.                                         (6.2)

Consequently

    log M=(chi-h)_++O_C(1)                                (6.3)

along every such path. The O_C(1) is an absolute logarithmic bound,
uniform over actual near-ceiling states once y_1>=8/3. It is sufficient
because chi->infinity, even if chi/alpha->0.

If entropy nearoptimality holds, Section 5 first gives y_1->3, so (6.3)
and log M*=chi+o(1) imply

    (chi-h)_+/chi->1.

For h>=0, chi>0 this is equivalent to h/chi->0. Conversely suppose
h/chi->0. Since 0<chi<=alpha log3 eventually,

    0<=h/alpha<=log3 (h/chi)->0,

so y_1=u_D exp(-h/alpha)->3. Formula (6.3) applies and proves
log M/log M*->1. This proves both directions of (2.4), with no assumption
that chi is comparable to alpha and no finite-r extrapolation.

In either nearoptimality, (2.3) or (2.4) gives h/chi->0; hence
T_p=exp[chi(1-o(1))]->infinity. Divide the exact form (4.3) by T_p.
The middle contribution is at most K_C/T_p->0; the other exceptional
contribution tends to zero by (6.1); and the baseline and linear terms
also vanish. Thus M/T_p->1. Subtracting the actual top power in the
definition of M proves the last assertion in (2.5). This argument accounts
for the whole growing tail, rather than multiplying a two-peak estimate
by the unchecked cardinality m^2 or D.

## 7. Uniform flattening of the ACTUAL nonpeak spectrum

Either criterion already gives y_1->3. From t->1 in (3.2),

    a_1=t y_1-1->2.

Since g_1=a_1+beta_1<=2 and beta_1>=0, it follows that
g_1->2 and beta_1->0. The physical star sum in (3.2) then gives

    0<=g_2^2<=4-g_1^2->0.

For every i>=2 with i<=R, sorting gives
0<=a_i<=a_2<=g_2->0. For all lower slots, the pivot deviation is bounded
in magnitude by beta_1->0. All remaining upper middle slots have deviation
at most 2/(m-1) by G9. Thus

    max_(i>=2)|lambda_i/b-1|->0.

Finally y_i=(lambda_i/b)/t and t->1, proving
max_(i>=2)|y_i-1|->0. In particular the least y_D is eventually positive.
Moreover y_2/y_1->1/3, and alpha->infinity yields
(y_2/y_1)^alpha->0. This proves all of Theorem C using necessary physical
witness inequalities of the original state, rather than weak empirical
convergence or a presumed one-spike model.

## 8. Necessary distinctions and scope boundaries

The credited G example rho proportional to I+(2-alpha^-1/2)vv*, in square
dimensions with alpha=m, has h asymptotic to sqrt(alpha)/3 and chi asymptotic
to alpha log3. It is an actual APPT density because the pure-projector
coefficient stays below two. It satisfies (2.4), whereas exp(-h)->0 in
(2.2). It therefore rejects replacing the entropy criterion by h->0.
This example is credited to G rather than counted as a new theorem.

Conversely bare y_1->3 is too weak even for the relative entropy criterion
when chi/alpha->0. To exhibit an actual sequence in (1.1), let integer
k->infinity, m=k^2, alpha=m, and choose

    n=ceil(3^m exp(-k)/m), D=mn.

Then chi=k+o(1). Take rho proportional to I+(2-3/k)vv*, with k>=3.
Its peak satisfies log(u_D/y_1)=1/k+O(1/k^2)+O(1/D), so h=k+O(1),
while y_1->3. Thus h/chi->1, and its relative entropy deficit tends to
zero relative to the optimum. This last conclusion also follows directly
from (6.3): log M=O(1), while log M*~k. This rejects replacing h/chi by
h/alpha. The exact real exponential/ceiling definitions specify actual
integer dimensions; no rank is silently rounded away in a density.

There is no assertion here about alpha/m->infinity, fixed m, bounded alpha,
alpha->0, finite chi, exact finite optimizers, or the entire all-diverging-
alpha synthesis. Those require their own already existing or separately
reviewed inputs. In particular this paper does not combine the pending
phase-5 scope into an independently reviewed full-axis result. The exact
physical endpoint, star and rectangular estimates, kernel identity and
earlier value results remain credited external written inputs to this
ordinary proof; no extra Lean declaration or audited root is introduced.

SOURCE_INPUTS.json and THEOREM_MAP.md give the precise bound source bytes
and proof dependencies. Bounded official-primary-domain searches and the
local theorem-map screen are recorded separately; absence of a matching
search result is not historical-priority certification. Finite exact
controls are regressions for the normalization and two actual examples,
not a substitute for the quantified proofs in Sections 3-7. All statuses
remain author-only pending a new independent ordinary review of this
scope, with no submission, public release, DOI or index promotion here.
