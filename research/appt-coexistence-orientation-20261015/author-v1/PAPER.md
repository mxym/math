# Orientation of the APPT coexistence curves and every fixed-r slice

Author: Yongxian Zhang (张永贤), South China University of Technology.
ORCID 0009-0000-3864-3536; mxymmxym1@gmail.com. 15 October 2026.
New author ordinary scope, pending independent ordinary review of this note.
No funding. OpenAI AI assistants assisted research/writing. Copyright2026
Yongxian Zhang; original material all rights reserved, third-party notices
retained. No new Lean scope, priority certificate, submission, release or
major-problem count. Previously frozen mathematical sources are unchanged.

## 1. Precise scalar and original quantum scopes

The frozen complete GLOBAL_MIXED_PHASE theorem is an ordinary input here,
together with its frozen NO_ISLANDS and CRITICAL_UNIQUENESS inputs. Their
internal AI mathematical independent full reads were reported PASS by the root; final
public metadata binding is handled separately by the root. Their frozen
opening author-status text is preserved verbatim rather than rewritten.
This note adds a new analytic orientation statement and requires its OWN
independent read. It does not rerun or enlarge the exact interval certificate,
reuse an old PASS for this new statement, or depend on pending S5/S6/S7.

For c>0,r>=0,0<=L<=2,0<=h<=1 define

    G(L)=2L^2/[3(2-L)],             L<2,
    B(c,L,h)=exp(-cLh)[1+h(exp(cL)-1)],
    P(c,L,h)=exp[-c(Lh+G(L))],      L<2,
    P(c,2,h)=0,
    F(c,r;L,h)=B+rP, V(c,r)=max_(L,h) F.

The pole class is {0}x[0,1] with value1+r; h is redundant there.
For t>0 put

    q(t)=t/(exp(t)-1), d(t)=1-q(t), w(t)=-log q(t),
    g(t)=w(t)-d(t), b(t)=exp g(t), s(t)=w'(t).

The unique bulk point is (2,h_b(c)), where
h_b(c)=1/(2c)-1/(exp(2c)-1), with value b(2c). Set
r_0(c)=b(2c)-1. The credited complete geometry theorem gives a unique
c_star in (519/2000,13/50), and r_star=r_0(c_star)>0, with:

- For0<c<c_star, analytic0<r_B(c)<r_0(c)<r_P(c). There is exactly one
  nondegenerate interior maximizer between r_B and r_P; the lower boundary
  ties that point with the bulk and the upper boundary ties it with the pole.
  Outside the closed strip only the relevant pure phase maximizes.
- Atc=c_star,r=r_star there are exactly three phase classes: pole, bulk,
  and one nondegenerate interior point. The two curves extend analytically
  to that point and their difference closes linearly.
- Forc>=c_star the complete value is max{b(2c),1+r}; atc>c_star its
  crossing has exactly the two pure classes. Atc=c_star the unique crossing
  has the one extra interior class just specified.

These are credited inputs, not new conclusions counted again. All uses of
an interior critical value below are local analytic continuations supplied
by nondegeneracy; no assumption of a global analytic branch outside its
proved domain is made.

The original quantum interpretation remains complex PSD trace-one densities
APPT after EVERY global unitary on C^m tensor C^n, integers2<=m<=n,m->infinity,
real alpha>1,alpha/m->c in(0,infinity),3^alpha/(mn)->r finite. The credited
L value and S actual-spectrum theorem transfer scalar argmax information
only in that window, with their actual loss conditions. Fixed-r scalar slices
are families of such limiting windows; they do not assert a new quantum
theorem for c tending to zero or infinity along the dimension sequence.

## 2. Complete orientation and slice theorem

**Theorem.** Both coexistence curves are strictly increasing:

    r_B'(c)>0, r_P'(c)>0,           0<c<c_star.               (2.1)

Their analytic continuations to c_star have strictly positive finite
derivatives there as well. Their endpoint values are

    r_B(0+)=r_P(0+)=0,
    r_B(c_star)=r_P(c_star)=r_star.                          (2.2)

At the triple point their derivatives satisfy the strict order

    0<r_P'(c_star)<r_0'(c_star)<r_B'(c_star).                (2.3)

For each fixed r in(0,r_star), let

    c_P(r)=r_P^-1(r), c_B(r)=r_B^-1(r),
    c_0(r)=r_0^-1(r).

They are unique and analytic, and

    0<c_P(r)<c_0(r)<c_B(r)<c_star.

As c increases over the ENTIRE positive axis the full scalar argmax is:

| c range | Complete phase classes |
| --- | --- |
| 0<c<c_P | Pole only |
| c=c_P | Pole and exactly one interior point |
| c_P<c<c_B | Exactly one interior point |
| c=c_B | Exactly that interior branch and the unique bulk point |
| c>c_B | Bulk only |

The interior point at the two different boundaries need not be the same
parameter pair; the wording refers to the uniquely continued mixed branch.
At r=r_star there is pole only for c<c_star, exactly the three classes at
c_star, and bulk only for c>c_star. At r>r_star there is one crossing
c_0(r)>c_star: pole below, exactly pole/bulk at the crossing, bulk above.
At r=0 the unique bulk point maximizes for every c>0. These are all ties.
Thus increasing c at fixed r never produces a repeated mixed interval.

For r increasing to r_star from below,

    c_B(r)-c_P(r)
     =[1/r_P'(c_star)-1/r_B'(c_star)](r_star-r)
            +O((r_star-r)^2),                              (2.4)

with a strictly positive coefficient. This is the horizontal closing
corresponding to the previously proved vertical closing at the triple point.

## 3. Elementary derivatives and strict convexity

The credited explicit formulas give0<q<1,s>0 and

    g'=s(1-q)>0, g''>0.                                   (3.1)

For example s=1/(1-exp(-t))-1/t>0 follows from1-exp(-t)<t.
The positive second derivative is also written explicitly in NO_ISLANDS.
An independent way to obtain the strict comparison actually needed here
is to write

    g(t)=max_(0<=h<=1) log[(1-h)exp(-th)+h exp(t(1-h))].

For t>0 its unique maximizing h lies strictly between0 and1. Each fixed
interior h gives a strictly convex log moment-generating function of t.
At any strict convex combination of two distinct positive t values,
use that middle point's maximizing h; its strict convexity, followed by
the two maximum inequalities, proves strict convexity of g. Since g is
analytic, this implies

    0<g'(k)<g'(K) whenever0<k<K.                           (3.2)

We do not infer a positive pointwise second derivative merely from a
generic strictly increasing function. The explicit formulas or the strict
convexity argument above supply exactly the derivative comparison used.
It follows that r_0 is strictly increasing, r_0(0+)=0, and r_0(c)->infinity:
indeed g(t)=t-log t-1+o(1) as t->infinity.

## 4. A local mixed critical value: which parameters are fixed

Let M(c,r)=F(c,r;L(c,r),h(c,r)) be ANY of the nondegenerate interior
critical branches used by the global geometry, including local continuations
across a coexistence curve and around the triple point. Set

    K=2c, k=cL=Kx, x=L/2 in(0,1),
    a(c,k)=2k^2/[3(2c-k)],
    T=r q(k)exp(-a),
    a_k=2x(2-x)/[3(1-x)^2]>0.

Here a_k is the partial derivative with c (equivalently K) FIXED.
The exact h elimination from GLOBAL gives, on its interior h domain,

    h=[d(k)-T]/k,
    f(c,k,r)=log max_h F=g(k)+T,
    f_k=g'(k)-T[s(k)+a_k].                               (4.1)

At the chosen interior critical branch, f_k=0, so

    T=g'(k)/[s(k)+a_k].                                   (4.2)

All identities concern actual derivatives of the analytic scalar function,
not derivatives of an approximate computed maximizer.

First compute a c partial with k AND r FIXED. Since

    partial_c a|_k=-4k^2/[3(2c-k)^2],

one has

    partial_c f|_(k,r)=4T x^2/[3(1-x)^2].                 (4.3)

Now take the c derivative of the local critical VALUE with r fixed. The
branch coordinates k(c,r),h(c,r) vary, but their terms vanish by stationarity.
Consequently

    M_c/M=4T x^2/[3(1-x)^2]>0,                            (4.4)

where M_c ALWAYS means the critical-value derivative with r fixed.
This use of the envelope identity is justified by the nondegenerate local
analytic branch; it is not a derivative along coexistence.

As an explicit coordinate check, if instead L (hence x) and r are held fixed,
then k_c=2x and a_c=G(L)=4x^2/[3(1-x)]. Formula(4.1) gives

    partial_c f|_(L,r)=2x g'(k)-T[2x s(k)+G(L)].

Using(4.2) reduces this to T[2x a_k-G(L)], which equals(4.3).
Away from stationarity the two partials differ by2x f_k; they must not be
identified before imposing f_k=0. Keeping K fixed while varying c=K/2
would be an inconsistent parameter prescription and is never used.

From(4.2),

    M_c/(2M)
      =g'(k) [a_k/(s(k)+a_k)] [x/(2-x)]
      <g'(k)<g'(K).                                      (4.5)

Both strict factors in brackets lie in(0,1). Thus

    0<M_c<2M g'(2c).                                     (4.6)

Finally the r derivative with c fixed is supplied by the original envelope:

    M_r=P(c,L,h) in(0,1).                                (4.7)

For a direct check, differentiating f gives M_r=M q(k)exp(-a).
At the optimizing h, M=exp(-kh)/q(k); hence this is exactly
exp(-kh-a)=P, not a different normalized peak weight. This preserves
which quantity appears in the coexistence derivatives.

## 5. Differentiate coexistence only after the fixed-r partials

On the lower boundary, M(c,r_B(c))=b(2c). Differentiating along this
curve NOW gives

    M_c+P r_B'=2b'(2c),
    r_B'=[2b'(2c)-M_c]/P>0.                              (5.1)

Here M=b(2c), so(4.6) implies M_c<2b(2c)g'(2c)=2b'(2c).
The denominator P is strictly positive because the tying critical point
is interior. On the upper boundary M(c,r_P(c))=1+r_P(c), so

    M_c+P r_P'=r_P',
    r_P'=M_c/(1-P)>0.                                    (5.2)

This proves(2.1). Each branch continues analytically through its boundary
by the credited negative definite Hessian. At c_star the tying point
stays strictly interior and nondegenerate; the credited analytic continuation
gives the same formulas with0<P<1 and finite M_c. Thus both endpoint
derivatives are finite and strictly positive as well. No limiting division
by a vanishing P or1-P is hidden.

For the derivative ordering, use exactly the frozen critical theorem's
notation p_star=P_star in(0,1),A_star>0. Its local formulas are

    r_B'(c_star)=r_0'(c_star)+2r_star A_star,
    r_P'(c_star)=r_0'(c_star)
                    -2p_star r_star A_star/(1-p_star).

Combining these credited strict separations with the newly proved positivity
of r_P'(c_star) yields(2.3). The certificate establishing A_star>0 is
unchanged; this note does not extend its coverage or claim a new interval run.

## 6. Endpoint values and the entire positive c axis

The c_star endpoint values and analytic continuation are part of the frozen
complete geometry theorem. For clarity establish the small-c endpoint
without using an unreviewed small-c expansion. Since0<r_B(c)<r_0(c)
and b(2c)->1, one has r_B(0+)=0. To bound r_P, for L>0 put

    Q_c(L,h)=[B(c,L,h)-1]/[1-P(c,L,h)].

The identity

    F-(1+r)=(1-P)(Q_c-r)

shows that the pole threshold is sup_(L>0,h)Q_c. At L=2 the denominator
is1. The L=0 class needs no division; it already is the pole.

B is the moment-generating function of a centered two-point random variable
with values-Lh,L(1-h), variance L^2h(1-h), and absolute value at most2.
Taylor's exact integral bound for0<c<=1 therefore gives

    0<=B-1<=C_0 c^2 L^2h, C_0=exp(2)/2.

For0<L<2 put H=Lh+G(L)>0. Since1-exp(-cH)>=cH/(1+cH),

    Q_c<=C_0[c L^2h/H+c^2L^2h]
         <=C_0(2c+4c^2)<=6C_0c.                          (6.1)

The estimate is also valid when h=0, where the numerator is zero, and at
L=2 by its direct numerator bound. Hence0<r_P(c)<=3exp(2)c for small c,
so r_P(0+)=0. This proves all endpoint values in(2.2) without substituting
a varying number of scales into a fixed-c theorem.

Together with the strictly positive derivatives, the endpoint values make
r_B and r_P analytic bijections from(0,c_star) onto(0,r_star). The inverse
function theorem applies at every interior point and at the endpoint via
the analytic continuations and their positive derivatives. Since
r_B<r_0<r_P, their inverses give c_P<c_0<c_B. Substituting the inequalities
into the complete r-ordered phase theorem proves every entry in Section2
for0<r<r_star. For c>=c_star the pure envelope and strict increase of r_0
continue the bulk class; no omitted extra high-c component is possible.

For r=r_star, monotonicity makes r>r_P(c) belowc_star and r<r_0(c) above,
so precisely the claimed triple transition occurs. For r>r_star, strict
increase and unboundedness of r_0 give a unique c_0(r)>c_star; the full pure
envelope proves the two-class crossing. For r=0, b(2c)>1 for everyc>0,
so only the unique bulk point remains. This explicitly handles every tie
and the entire c axis. Expanding the two analytic inverses at r_star gives
(2.4); its coefficient is positive by(2.3).

## 7. Actual APPT spectra and precise transfer restrictions

For any original density/order/dimension sequence in the finite(c,r) window
of Section1, use the ACTUAL middle quantities of S: R=m(m-1)/2,
K=m(m+1)/2,j=D-K+1,A=y_j,kappa=y_R/A-1,actual mean mu,

    L=(m-1)kappa,
    theta=(mu/A-1)/kappa ifkappa>0, else0,
    z_i=(m-1)(y_i/A-1), J=mean_mid z_i(L-z_i),
    eta_m=2(m-2)kappa^2/[2-(m-3)kappa],
    Pi=[A^alpha(3-eta_m)^alpha-y_1^alpha]/D>=0.

The original every-global-unitary S theorem states that relative entropy
nearoptimality is equivalent to

    dist((L,theta),FULL scalar argmax at(c,r))->0,
    J->0, Pi->0.                                          (7.1)

Insert the full one/two/three-class argmax from Section2; do not replace
(7.1) by the phase name or the body law alone. All tied classes can occur
on subsequences, and all are attained by actual APPT states by S. Along
a subsequence with(L,theta)->(l,h), the ACTUAL empirical law of m(y_i-1)
converges in W1 to(1-h)delta_-lh+h delta_l(1-h). In particular the pole
class gives delta0, the bulk class its h_b(c) law, and mixed its unique
interior law. At the triple point there are exactly the three corresponding
possible limiting body laws; alternation remains allowed.

When r>0 and l<2, S additionally gives the ACTUAL physical peak correction

    m(3-y_1)->3lh+2l^2/(2-l),

and uniform flattening of all nonlargest normalized eigenvalues. This formula
is NOT asserted at l=2, where the peak moment instead vanishes. Nor does
this new slice theorem extend S to r->infinity,c->0,c->infinity,finite m,
or exact finite-dimensional optimizers. It is one analytic consequence of
the fully classified scalar geometry within the original finite-window
quantifiers. No pending S5/S6/S7 scope is folded into a full-axis claim.
