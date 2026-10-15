# Unique critical anomalies and the entropy-order transition

Yongxian Zhang (张永贤), South China University of Technology.
15 October 2026, Asia/Shanghai. Complete author manuscript; independent
ordinary review pending. No new Lean theorem or old audit expansion.

## 1. Complete scalar and physical statements

For every finite alpha>0 define the convex kernel

    psi_alpha(y)=[y^alpha-1-alpha(y-1)]/(alpha-1),
    psi_1(y)=y log y-y+1,

and the FULL positive and negative critical ratios

    R_+(alpha,p)=(2-p)psi_alpha(1+p)/(2alpha p), 0<p<2,
    R_-(alpha,b)=(1-b)psi_alpha(1-b)/(alpha b), 0<b<1.
    D_+(alpha)=max_p R_+(alpha,p), D_-(alpha)=max_b R_-(alpha,b),
    d_alpha=max{D_+(alpha),D_-(alpha)}.                       (1)

Their endpoint limits are zero; both are positive inside. The all-profile
cubic APPT theorem C2 identifies this d_alpha with the actual limiting
bulk-onset coefficient. It also identifies every nonempty critical
profile as a single anomaly of a globally maximizing sign. Those are
credited physical input theorems, not inferred solely from the ratios.

**J0.** For every alpha>0, R_+ has a UNIQUE maximizer p_alpha in (0,2)
and R_- a UNIQUE maximizer b_alpha in (0,1). The second derivative with
respect to the anomaly parameter is strictly negative at each maximum.

**J1.** The four functions p_alpha,b_alpha,D_+(alpha),D_-(alpha) are
real analytic on (0,infinity), including through alpha=1. Moreover

    D'_+(alpha)>0, D'_-(alpha)<0.                            (2)

There is a UNIQUE alpha_x in (1/2,1) with D_+(alpha_x)=D_-(alpha_x).
The crossing is transverse. There is no claim of a simple algebraic
expression for alpha_x.

**J2.** The actual onset coefficient d_alpha is strictly decreasing on
(0,alpha_x), strictly increasing on (alpha_x,infinity), and has its
unique global minimum at alpha_x. Its two analytic branches meet with
different derivatives there. The H0-H4 theorem consequently has only the
negative nonbulk family in each fixed linear critical window below
alpha_x and only the positive family above it, eventually in m. At the
exact crossing both remain in the finite classification; no tie is lost.

**J3.** Let N_alpha(m) be the smallest integer N>=m for which every
integer n>=N has exact actual all-global-unitary APPT entropy maximum
equal to the integer-rank q_m projection bulk. For EACH fixed finite
positive alpha,

    N_alpha(m)=d_alpha m^2+a_alpha m+O_alpha(1),               (3)

where a_alpha is the explicit coefficient from I0-I3, maximizing over
every leading critical tie. This removes the nondegeneracy condition
from that earlier conditional O(1) statement. All finite integer effects
remain; a single exact ceiling is not inferred.

## 2. The positive maximum, with no restriction on alpha

In this section write f(p)=psi_alpha(1+p). For EVERY alpha>0, including
alpha=1, its derivatives satisfy

    f(0)=f'(0)=0, f''(p)=alpha(1+p)^(alpha-2)>0,
    f'''(p)=alpha(alpha-2)(1+p)^(alpha-3).

Direct differentiation of (1) gives

    partial_p R_+=F_+(p)/(2alpha p^2),
    F_+(p)=p(2-p)f'(p)-2f(p),
    F'_+(p)=p G_+(p), G_+(p)=(2-p)f''(p)-2f'(p),
    G'_+(p)=alpha(1+p)^(alpha-3)[2alpha-7-(alpha+1)p].        (4)

We have G_+(0)=2alpha>0 and G_+(2)=-2f'(2)<0. If alpha<=7/2,
G'_+ is strictly negative on (0,2). If alpha>7/2, its sign changes
exactly once, from positive to negative, at (2alpha-7)/(alpha+1) in
(0,2). Thus G_+ first possibly increases from an already positive
value, then strictly decreases to a negative value. It has EXACTLY
one zero g in (0,2), and is positive before it and negative after it.

Hence F_+ strictly increases on (0,g) and strictly decreases on (g,2).
Now F_+(0)=0 and F_+(2)=-2f(2)<0. There is exactly one zero
p_alpha in (g,2). Formula (4) makes R_+ strictly increase up to it
and strictly decrease afterwards. At this zero,

    partial_p^2 R_+(alpha,p_alpha)
                     =F'_+(p_alpha)/(2alpha p_alpha^2)<0.    (5)

This proves the positive half of J0 for arbitrarily small or large
fixed alpha; the intermediate 7/2 case is explicitly included.

## 3. The negative maximum, including its singular endpoint limits

Now put f(b)=psi_alpha(1-b). Its interior derivatives are

    f(0)=f'(0)=0, f''(b)=alpha(1-b)^(alpha-2)>0,
    f'''(b)=alpha(2-alpha)(1-b)^(alpha-3).

The full ratio derivative is

    partial_b R_-=F_-(b)/(alpha b^2),
    F_-(b)=b(1-b)f'(b)-f(b),
    F'_-(b)=b G_-(b), G_-(b)=(1-b)f''(b)-2f'(b),
    G'_-(b)=-alpha(alpha+1)(1-b)^(alpha-2)<0.                (6)

G_-(0)=alpha>0. At b->1 its limit is negative: it equals
-2alpha/(alpha-1) when alpha>1, tends to minus infinity at alpha=1,
and also tends to minus infinity when 0<alpha<1. To see the latter
directly with y=1-b, use

    G_-=-alpha(1+alpha)y^(alpha-1)/(1-alpha)
                                            +2alpha/(1-alpha).

At alpha=1 it is 1+2log(1-b). Thus G_- has exactly one zero g,
and F_- first increases, then decreases. Further, F_-(0)=0 and
F_-(b)->-1 as b->1. The latter holds since f(b)->psi_alpha(0)=1
and (1-b)f'(b)->0 for every positive alpha, also at alpha=1.
Therefore F_- has precisely one zero b_alpha after g, and at it

    partial_b^2 R_-(alpha,b_alpha)
                          =F'_-(b_alpha)/(alpha b_alpha^2)<0. (7)

No derivative at b=1 or a positive lower bound on alpha has been used.
The endpoint limits are handled for each fixed alpha. This completes J0.

## 4. Analyticity, strict order monotonicity, and the unique transition

The kernels are jointly real analytic for alpha>0,y>0. Their apparent
division by alpha-1 has a removable analytic singularity, for example
from Taylor's integral representation

    psi_alpha(1+h)/alpha
           =h^2 integral_0^1 (1-u)(1+u h)^(alpha-2) du,
    h>-1.                                                  (8)

At the unique critical points, (5) and (7) are nonzero. The analytic
implicit-function theorem applied to the ratio derivative consequently
provides locally analytic p_alpha and b_alpha. Uniqueness makes these
local functions agree on overlaps, giving global analyticity. Composition
gives analytic D_+,D_-. All hypotheses are interior ones; the singular
negative endpoint causes no difficulty for this local argument.

Dividing out alpha by (8), the ratios are

    R_+=p(2-p)/2 integral_0^1 (1-u)(1+u p)^(alpha-2) du,
    R_-=b(1-b) integral_0^1 (1-u)(1-u b)^(alpha-2) du.         (9)

For fixed p>0, differentiating with respect to alpha inserts the strictly
positive log(1+up) on 0<u<1. For fixed 0<b<1 it inserts the strictly
negative log(1-ub). All other factors there are positive. At an optimum
the anomaly derivative vanishes, so the chain rule gives exactly these
signed partial derivatives for D'_+,D'_-. This proves (2), not merely
weak monotonicity of the suprema.

H4 already proves D_-(1/2)=5sqrt(5)-11>D_+(1/2). A simple exact
opposite comparison holds at alpha=1. Indeed

    D_+(1)>=R_+(1,1)=log 2-1/2>31/162>3/16,
    D_-(1)<D_-(1/2)=5sqrt(5)-11<3/16.                       (10)

Here log 2=2atanh(1/3)>2(1/3+1/81)=56/81, giving the first bound.
For the last, sqrt(5)<179/80 since 179^2>5*80^2. The rational comparison
31/162>3/16 is strict. Thus the continuous difference D_+-D_- changes
sign between 1/2 and 1, and its derivative is strictly positive. It
has exactly one zero alpha_x there. This proves J1 and the scalar
claims in J2, including uniqueness of the global minimum of d_alpha.

For the actual critical-window claim, use H0-H4 and its l1 critical
localization on the original APPT set. Below alpha_x the positive
critical set is empty; a sequence of actual nonbulk optimizers with
positive retained anomaly would contradict that localization. Above
alpha_x the same argument excludes the negative sign. At alpha_x
there are exactly two nonempty critical profiles, one for each sign;
both are retained by the original finite formula. This does not assert
that both necessarily optimize at each finite dimension.

## 5. The unconditional bounded onset remainder

I0-I3 supplies the exact compact real crossing envelope nu_alpha,m^* and
its uniform scalar expansion

    nu_s,m(z)=d_s(z)m^2+a_s(z)m+O_alpha(1),
    a_alpha=max{a_s(z): d_s(z)=d_alpha},
    ceil(nu_alpha,m^*-C_alpha m^-3)<=N_alpha(m)
                             <=ceil(nu_alpha,m^*+C_alpha m^-3). (11)

The changes z=2p/(2-p) and z=b/(1-b) have nonzero derivatives at the
interior critical anomalies. Therefore (5),(7) imply strictly negative
second derivatives of d_s in z at its maximum as well. There are only
one or two globally critical points, by J0-J1. Around each, the leading
loss is bounded below by a positive constant times squared distance,
and a_s is Lipschitz. The leading compact gap outside these neighborhoods
is fixed and positive. Hence maximization of (11) increases the value
above d_alpha m^2+a_alpha m by at most

    max_(v>=0) [-c m^2 v^2+C m v]+O_alpha(1)=O_alpha(1).

Evaluation at a critical point attaining a_alpha gives the matching
lower. Thus nu_alpha,m^*=d_alpha m^2+a_alpha m+O_alpha(1).
The two ceilings in (11) each differ from their center by at most
1+C_alpha m^-3, proving (3) for every fixed positive order. This argument
also covers the exact sign transition: among its two leading ties, the
larger linear coefficient is used; if those coefficients tie, retain both.

## 6. Scope, inputs, and verification status

C0-C4 and E0-E4 are the unchanged independently ordinarily reviewed
14 October APPT packets. H0-H5 and I0-I3 have their separate source-bound
independent ordinary reads, which do not automatically certify the new
J0-J3 mathematics. This manuscript's independent read is pending.
No original quantum definition or old formal verification scope changes.

The resumed 15 October bounded primary screen used exact APPT/Renyi
critical/negative-entropy terms on primary indexes and returned no matching
examined item before this full manuscript. That does not establish
historical priority or exhaustive absence of prior work. These calculus
and onset refinements are in the same APPT research line, not an additional
major-conjecture solution.

No assertion is made for alpha changing with m, every finite dimension,
effective starting dimensions, unconditional single-ceiling formulas,
or absolute separability. Finite symbolic and numerical controls support
the all-domain proof above but do not replace its quantifiers or its
credited full physical inputs. No Lean execution, enlarged audit root,
external submission, email, Release or DOI is part of this work.

Personal independent research, no external funding; OpenAI AI assistants
assisted. Original material all rights reserved, with third-party inputs
retaining their attribution and licenses.
