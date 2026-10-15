# APPT fast-order spectra: two sharp moment branches and the entropy criterion

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology. ORCID 0009-0000-3864-3536;
mxymmxym1@gmail.com. 14 October 2026, Asia/Shanghai.
No external funding. OpenAI AI assistants assisted research and writing.
Copyright 2026 Yongxian Zhang; all rights reserved for original material.

This classifies sharp moment near-maximizers on every aspect ratio when
alpha/m tends to infinity. It also gives an exact criterion for the weaker
relative entropy-deficit optimum. The conclusions concern actual APPT
densities, with no restriction to a proposed spectral family. They are new
ordinary written analysis of the same APPT direction, not new Lean coverage.

## 1. Actual spectral quantities and the full statement

Use [FAST_ORDER_VALUE.md](FAST_ORDER_VALUE.md). Throughout m->infinity,
alpha/m=c->infinity, n>=m is arbitrary, y_i=D lambda_i are ordered actual
APPT eigenvalues, P=u_D^alpha/D, B is the exact scalar bulk maximum F1, and

    F=max{P,B}, w_p=P/F, w_b=B/F, L_*=log F.

The moment optimum satisfies M*_alpha~F and L_*->infinity. Retain the actual
physical middle definitions from the previous proof:

    R_0=m(m-1)/2, S_0=m(m+1)/2, j=D-S_0+1,
    I_mid={R_0,...,j}, N=D-m^2+2,
    A=y_j>0, A^+=y_(R_0), k=A^+/A-1 in [0,k_0],
    mu=(1/N)sum_(i in I_mid)y_i.

If k>0 put

    x_i=(y_i-A)/(A*k) in [0,1],
    q=(1/N)sum_(i in I_mid)x_i=(mu-A)/(A^+-A).

The actual two endpoints belong to I_mid, so q>0 when k>0. If k=0 set q=0.
For k>0, Z_k=(1+k)^alpha-1 and define

    H_(alpha,k)(x)=[(1+kx)^alpha-1]/(x Z_k)       if x>0,
    H_(alpha,k)(0)=alpha*k/Z_k,

    loss=1-[sum_(i in I_mid)x_i H_(alpha,k)(x_i)]/[sum_(i in I_mid)x_i],
    G=alpha log[(1+k_0)/(1+k)], t=alpha*k*q,
    d_b=G+|t-1|+loss.                                                (R1)

For k=0 set loss=1. Convexity makes 0<=H<=1, so all defects are nonnegative.
The exact peak defect is

    h=alpha log(u_D/y_1)>=0.                                         (R2)

**Theorem R1 (complete sharp-moment criterion, every aspect).** For every
actual APPT sequence in this range, including arbitrarily oscillating P/B,

    M_alpha(rho)/M*_alpha ->1

if and only if

    min{(1-w_p)+min{1,h}, (1-w_b)+min{1,d_b}} ->0.                    (R3)

Since M*_alpha->infinity, the same equivalence holds for
(M_alpha(rho)-1)/(M*_alpha-1)->1. In particular:

* If P/B tends to r<1, the criterion is exactly d_b->0.
* If P/B tends to r>1, including infinity, it is exactly h->0.
* If P/B tends to one, it is min{h,d_b}->0; the two branches may alternate.

The bulk condition resolves the full physical width to G->0, selects a rare
upper-level mean fraction q~1/(alpha*k), and places its size-biased spectral
weight within an upper-edge layer of width o(1/alpha). More explicitly, once
G->0 and t->1, loss->0 is equivalent to, for every eps>0,

    sum_i x_i 1_{alpha*k*(1-x_i)>eps} / sum_i x_i ->0.                 (R4)

The sums in R4 run over I_mid. These are spectral conditions, not a
caller-supplied SDP certificate. They do not require every tail eigenvalue
to belong exactly to either endpoint at finite dimension.

**Theorem R2 (complete relative entropy-deficit criterion).** Let

    T_p=y_1^alpha/D,
    T_b=(1/D)sum_(i in I_mid)y_i^alpha,
    ell(rho)=max{0,log T_p,log T_b}.

Then, uniformly over all actual states on every such dimension/order path,

    |log M_alpha(rho)-ell(rho)|/L_* ->0.                              (R5)

Consequently

    [log D-S_alpha(rho)]/E_alpha ->1
           if and only if ell(rho)/L_* ->1.                          (R6)

The benchmark L_* is the explicit closed formula in FAST_ORDER_VALUE.md.
Only the actual peak and the middle spectral Laplace contribution remain
in R6; the entire other exceptional spectrum is proved irrelevant at this
logarithmic scale. R6 permits a much larger loss of normalized moment than
R3. Section 6 gives an actual APPT separation.

## 2. When bulk competition matters the actual mean error is harmless

Use the prior all-order dimension dichotomy. With delta_m=O(1/m) from the
actual middle bound and T=(1+delta_m)^alpha, whenever P<=K T for a fixed K,

    D>=2^alpha/K, alpha*m^2/D->0,
    mu^alpha=1+o(1), N/D->1.                                        (R7)

The bounds hold uniformly over the actual state. Since B<=T, every bounded
P/B path lies in this range. Every exceptional entry other than the first
has y_i<=v_m->1+sqrt(2)<3, and its total divided by P is at most
m^2(v_m/u_D)^alpha->0. These are actual physical bounds from
[PAPER.md](../appt-growing-renyi/PAPER.md); they are not hypotheses on
arbitrary spectral lists.

For k>0 the exact actual-middle identity is

    T_b=(N/D) mu^alpha S_k(q) C_k,
    S_k(q)=(1+q Z_k)/(1+kq)^alpha,
    C_k=(1+q Z_k(1-loss))/(1+q Z_k) in [0,1].                        (R8)

It follows simply by summing 1+x_i Z_k H(x_i), using the actual q, and
A=mu/(1+kq). For k=0 the middle is constant and R8 holds with S=1,C=1.

On every bounded-P/B path, R7-R8 prove

    T_b/B ->1   if and only if   d_b->0.                             (R9)

The details of this equivalence, including the rare mass, follow next.

## 3. Full necessity and sufficiency of the bulk defect

First S_k(q)<=B_alpha(k)<=B exactly. If S_k(q)/B->1, it forces
alpha*k->infinity and k/k_0->1. To see this without assuming a limit,
split at eps=c^(-1/4) as in the value proof. For k<=eps*k_0 the ratio tends
to zero by F9. For k>=eps*k_0, alpha*k>=2c^(3/4)->infinity, and F8 gives

    B_alpha(k)/B=(k_0/k) exp(-G)[1+o(1)].                            (R10)

Putting s=k/k_0, one has
G>=alpha*k_0(1-s)/(1+k_0)>=c(1-s) eventually. For s<=1-eta the exponential
loss dominates k_0/k<=c^(1/4). Thus near-equality forces s->1. In R10 the
factor k_0/k then tends to one, so near-equality forces G->0. Conversely
G->0 forces s->1 and B_alpha(k)/B->1.

For such k, alpha*k->infinity. The exact formula for S_k(q), divided by
F8, is

    S_k(q)/B_alpha(k)
       =[1+o(1)] e [t+alpha*k/Z_k]/(1+t/alpha)^alpha.                (R11)

Here alpha*k/Z_k->0. If t is bounded, its limit is e t exp(-t), whose
unique maximum one is at t=1. If t->0 the ratio tends to zero. If t->infinity,
use t/alpha<=k->0 and
(1+t/alpha)^alpha>=exp[t/(1+k)] to see that it again tends to zero.
Every subsequence is covered; hence S_k(q)/B_alpha(k)->1 exactly when t->1.

At t->1, q Z_k=t Z_k/(alpha*k)->infinity. The multiplier C_k in R8 then
tends to one exactly when loss->0. Because each of S_k(q)/B and C_k is
at most one, their product tends to one if and only if both do. Together
with R7 this proves the full R9 and both directions of d_b->0.

For the layer statement, H(x) is nondecreasing in x: the secant slope of
the convex function (1+kx)^alpha-1 from zero is nondecreasing. Once
alpha*k->infinity and k->0, for every fixed s>=0,

    H(1-s/(alpha*k)) ->exp(-s).                                     (R12)

Indeed the top power ratio is
[1-s/(alpha*(1+k))]^alpha, the subtracted ones are negligible, and
1-s/(alpha*k)->1. Define the size-biased probability of index i to be
x_i/sum_j x_j. If its layer distance alpha*k(1-x_i) is at least eps with
probability bounded below, monotonicity and R12 keep loss bounded away
from zero. Conversely layer distance tending to zero in probability gives
expectation H->1 by boundedness 0<=H<=1 and R12. This proves R4. It also
states the required upper-edge resolution directly in the actual spectrum,
since alpha*k(1-x_i)=alpha(A^+-y_i)/A.

## 4. The branch choice, including all oscillating paths

First suppose P/B stays bounded, so R7 holds. Apply the physical peak/width
coupling y_1<=A(3-eta_m(k)). For k>=eps*k_0, F10 and R7 give

    T_p=o(P)=o(B).                                                  (R13)

For k<=eps*k_0, the middle moment is o(B), by R7 and F9. Thus the two
actual contributions cannot both remain a positive proportion of B.
The other exceptional contribution is o(P)=o(B) by Section 2.

If P/B->r<1, the small-width branch cannot be sharp: its moment is at
most P+o(B), strictly below B. Sharpness is therefore exactly T_b/B->1,
which is R9. If 1<r<infinity, the large-width branch cannot be sharp:
its moment is at most B+o(P), strictly below P. On the small-width branch
the only leading term is T_p=P exp(-h), so sharpness is exactly h->0.
At r=1, the same split makes min{h,d_b}->0 necessary, and either condition
is sufficient by the actual lower contribution and the universal optimum.
Branch alternation is therefore allowed.

If P/B->infinity, the actual middle moment is o(P) on the whole path.
Indeed along every subsequence, either P/T has a bounded further subsequence,
where R7 bounds the middle by B[1+o(1)]=o(P), or P/T tends to infinity,
where the crude actual middle bound T=o(P) suffices. The other exceptional
values are o(P). Consequently

    M_alpha(rho)/P=exp(-h)+o(1),                                    (R14)

uniformly over actual states along such a path, without assuming alpha/D
small. The optimum is asymptotic to P; this proves the infinite-r case.

Finally an arbitrary P/B sequence has further subsequences tending to
some r in [0,infinity]. The finite and infinite cases just proved apply
to each. The weight version R3 encodes exactly their allowed branch
limits, including critical alternation. A bad subsequence on either side
would contradict its corresponding case. This proves R1 on every aspect
and every oscillating phase path.

## 5. The weaker entropy criterion excludes the rest of the spectrum

Write M_alpha=T_p+T_b+T_e, where T_e includes precisely the other exceptional
indices. There is a universal a>0 such that v_m/u_D<=exp(-2a) eventually.

If log P<=a alpha, then

    T_e<=m^2 P(v_m/u_D)^alpha<=m^2 exp(-a alpha)->0.                 (R15)

Jensen gives M_alpha>=1. Since M_alpha>=T_p+T_b, the logarithms of M_alpha
and 1+T_p+T_b differ by at most a bounded quantity plus o(1) in this case.
The value proof gives L_*>=log B>=C c eventually, and c->infinity, so
this difference is o(L_*).

If log P>a alpha, one instead uses the exact ordering T_e<=m^2 T_p.
Therefore the same logarithmic difference is at most O(1+log m). Now
L_*>=log P>a alpha and alpha=m c, so this is again o(L_*). No claim
that T_e itself vanishes is needed in this large-peak-log case.

Uniformly for all positive T_p,T_b,

    log(1+T_p+T_b)=max{0,log T_p,log T_b}+O(1).                      (R16)

The two cases and R16 prove the uniform R5. F2 gives log M*_alpha=L_*+o(1),
so R6 follows in both directions. The division is harmless because L_*
diverges. This is a complete value-normalized entropy near-optimality test,
not an assertion that sharp-moment rigidity persists at its weaker scale.

## 6. An actual APPT entropy optimizer that loses its whole sharp moment

Take alpha=m^2, so c=m. Let n be chosen so that D=mn is the nearest allowed
dimension to 3^alpha/B, with B computed at this m,alpha. Then D grows
exponentially, alpha/D->0 and P/B->1 (the exact u_D calibration changes
the ratio by 1+o(1)). Put eps=c^(-1/2) and k=(1-eps)k_0. Choose a
rank-rounded projection Q with fraction q_k from F1, and define the actual
APPT density proportional to I+kQ. Its all-unitary sufficiency follows
from k<=k_0 and the Schmidt pair bound in the value proof.

Its moment is asymptotic to B_alpha(k), because D is exponentially large
and rank rounding costs o(1) after multiplication by alpha. Equation R10
now gives

    log[B_alpha(k)/B]=-G+o(1), G~2 sqrt(c)->infinity.

Thus M_alpha(rho)/M*_alpha->0. But log B~2c, so G/log B->0 and
log M_alpha(rho)/log M*_alpha->1. The state satisfies R6 and fails R3.
This demonstrates the difference within the bulk competition window,
without using a nonphysical list or the already known balanced spike example.

The projection and pure-spike witnesses supply both sharp branches. R1
describes all sharp moment states, rather than only those witnesses. The
entropy criterion permits further spectra and larger losses as shown above.
Fixed-m limits, exact finite extrema, absolute separability and complete
formalization remain outside this manuscript. No new major-conjecture count,
historical priority, external peer review, Release, DOI or submission is claimed.
