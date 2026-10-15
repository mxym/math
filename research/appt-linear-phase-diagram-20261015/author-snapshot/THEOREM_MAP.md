# Complete scope and theorem map for four new APPT phase manuscripts

Status: complete author arguments, independent ordinary review pending.
This is new metadata. All earlier proof/code/certificate/manifest bytes are
unchanged. SOURCE_INPUTS.json binds their exact hashes and the credited inputs.

## Original matrix range and what is credited

Let rho be an original complex PSD trace-one density matrix on C^m tensor C^n,
APPT after every global unitary, 2<=m<=n, D=mn. Sort lambda_i decreasingly
and set y_i=D lambda_i. The present window has m->infinity, alpha>1,
alpha/m->c in (0,infinity), 3^alpha/D->r in [0,infinity). The alpha>1
domain is retained for max moment versus minimum entropy; eventual validity
also follows from alpha/m->c>0. There is no bounded-aspect restriction.

Credited L1/L2-L4 give the complete value:

    M*_alpha=max_APPT D^-1 sum_i y_i^alpha,
    E_alpha=log D-min_APPT S_alpha=log M*_alpha/(alpha-1),
    M*_alpha->F_*(c,r),       m E_alpha->log F_*(c,r)/c.

Their uniform compact positive alpha/m formulation and the all-order calibrated
value theorem V are existing inputs, not claimed as new work. The new problem
is the scalar argmax geometry, followed by the already established actual-spectrum
transfer S. All four new manuscript scopes lie in that one APPT direction.

## Scalar notation

    G(L)=2L^2/[3(2-L)]                  (L<2),
    B=exp(-cLh)[1+h(exp(cL)-1)],
    P_scalar=exp[-c(Lh+G(L))]           (L<2), P_scalar(2,h)=0,
    F=B+r P_scalar, F_*=max_[0,2]x[0,1] F,
    b(t)=(exp(t)-1)/t * exp[-1+t/(exp(t)-1)],
    r_0(c)=b(2c)-1,
    h_b(c)=1/(2c)-1/(exp(2c)-1).

Pole is {L=0} (all h redundant), value 1+r. Pure bulk is (2,h_b), value
b(2c). A mixed point has 0<L<2,0<h<1. P_scalar is distinct from the
actual spectral slack Pi_actual below.

## Manuscripts, exact results and logical ordering

| Scope | Complete result within that exact source | Dependencies |
|---|---|---|
| D1 support | For c>=1, F_*=max(b(2c),1+r), exact pure argmax and no hidden interior tie | L20 elimination/pure bulk and elementary calculus; L/S for matrix interpretation |
| LAST | Mixed-c set is open, contains (0,1/10], has last boundary strictly below one; every positive boundary has a compactly interior mixed tie at r_0 as well as both pure phases; all-r value there is pure envelope | Self-contained scalar argument, including repeated D1 proof; credited L/S for transfer |
| NO_ISLANDS | Mixed-c set exactly (0,c_star); one admissible initial K interval and one crossing for every fixed x=L/2; pure-only argmax for c>c_star, finitely many interior ties at the last boundary | LAST/D1 plus curvature inequality, elasticity ODE barrier and fixed-width monotonicity; L/S transfer |
| CRITICAL | 519/2000<c_star<13/50; exactly one nondegenerate interior mixed tie at c_star,r_0; exact local three-branch diagram, analytic coexistence curves and linear closing | LAST, NO_ISLANDS, exact 73-leaf certificate and integer engine; L/S transfer |
| GLOBAL | At all 0<c<c_star, at most one interior local maximum for every r, one unique global mixed state on one r interval, exactly two unique analytic coexistence curves, complete tie sets and nondegenerate interior Hessian | LAST, NO_ISLANDS, CRITICAL and the new exact 74-leaf whole-domain two-turn certificate; L/S transfer |

No row retroactively enlarges a prior ordinary review PASS. The independent
reviewer is asked to read LAST -> NO_ISLANDS -> CRITICAL -> GLOBAL in full,
including both interval engines, exact certificate data and full partitions.

## Complete scalar argmax table

For 0<c<c_star define 0<r_B(c)<r_0(c)<r_P(c). Both boundaries are real
analytic on (0,c_star); the inner maximizer is unique and nondegenerate.

| Parameter | Complete maximizing phase classes |
|---|---|
| 0<=r<r_B(c) | Bulk only |
| r=r_B(c) | Bulk and the unique interior point |
| r_B(c)<r<r_P(c) | Unique interior point only |
| r=r_P(c) | Unique interior point and pole |
| r>r_P(c) | Pole only |
| c=c_star, r<r_0(c_star) | Bulk only |
| c=c_star, r=r_0(c_star) | Bulk, pole, and exactly one interior point |
| c=c_star, r>r_0(c_star) | Pole only |
| c>c_star, r<r_0(c) | Bulk only |
| c>c_star, r=r_0(c) | Bulk and pole only |
| c>c_star, r>r_0(c) | Pole only |

Pole's redundant h coordinates are retained as a set but count as one phase.
At c_star the value is the pure envelope despite the additional interior tie.
Deleting that tie would give an incorrect rigidity conclusion.

## Actual-spectrum equivalence and all retained losses

Use the actual S indices R_m=m(m-1)/2,K_m=m(m+1)/2,j=D-K_m+1 and the
middle set {R_m,...,j} of N=D-m^2+2 entries. Put

    A=y_j>0, B_actual=y_(R_m), kappa=B_actual/A-1,
    mu=N^-1 sum_middle y_i,
    theta=(mu/A-1)/kappa if kappa>0, otherwise 0,
    L=(m-1)kappa in [0,2],
    z_i=(m-1)(y_i/A-1) in [0,L],
    J=N^-1 sum_middle z_i(L-z_i),
    eta_m(kappa)=2(m-2)kappa^2/[2-(m-3)kappa],
    Pi_actual=[A^alpha(3-eta_m(kappa))^alpha-y_1^alpha]/D >=0.

The credited S theorem says actual FIRST-NONZERO-scale nearoptimality

    (log D-S_alpha(rho))/E_alpha ->1

is equivalent to all three conditions:

    dist((L,theta), full scalar argmax)->0, J->0, Pi_actual->0.

The actual empirical measure of m(y_i-1) converges in 1-Wasserstein,
on any subsequence whose scalar parameters converge to (l,h), to

    (1-h)delta_(-lh)+h delta_(l(1-h)).

Every scalar maximizer is attained by actual APPT sequences. Thus the table
above describes all possible limiting body laws, with the pole law delta_0,
and permits alternation at ties. At surviving peaks r>0,l<2, S additionally
gives m(3-y_1)->3lh+2l^2/(2-l), and all other y_i tend uniformly to one.
At l=2 only the vanishing largest moment is asserted, not that interior
peak-height formula. Operator flatness or one outlier pattern is not inferred
from a bulk empirical law. For moving parameters nearing a tie, choosing one
phase requires control relative to its vanishing gap.

## Proof certificates versus discovery and review

CRITICAL uses 73 exact leaves (27+32+13+1); GLOBAL uses 74 exact leaves
(35+1+28+5+1+4), including seven explicit above-K-cap middle leaves. All
other leaves have strict outward integer sign bounds. The global K range
includes zero through removable E_p-series charts. The author replay verifies
each stored bound, complete rational partitions, analytic cap handling and
source hashes. These are author controls, not independent review or Lean.

Floating discovery files are preserved and excluded as proof dependencies.
The long decimal c_star in a discovery file is not a certified enclosure.
Only the strict rational interval above is currently certified by the source.
SOURCE_INPUTS.json states every input role, actual read scope and status.

The completed author scope is this one scalar linear-order finite-r APPT
classification and its credited S transfer. It does not establish exact finite
dimension extrema, every-order rigidity, external priority, human peer review,
absolute separability of the constructed APPT competitors, a submission, DOI,
Release, or any new Lean declaration. No major-problem count is increased.
