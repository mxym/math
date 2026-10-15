# The sharp peak-or-bulk law for APPT orders faster than local dimension

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology. ORCID 0009-0000-3864-3536;
mxymmxym1@gmail.com. 14 October 2026, Asia/Shanghai.
No external funding. OpenAI AI assistants assisted research and writing.
Copyright 2026 Yongxian Zhang; all rights reserved for original material.

The previous all-positive-order value theorem uses a finite scalar maximum.
Here that maximum becomes an explicit competition between two existing
physical mechanisms. This supplies a simple first nonzero entropy equivalent
in a regime where an absolute-error law alone misses the bulk contribution.
It is one continuation of the APPT problem, not another independently counted
major conjecture. All new statements are ordinary proofs without new Lean.

## 1. Objects and results

Let 2<=m<=n, D=mn, and let rho be an actual density on C^m tensor C^n
whose partial transpose is positive after every global unitary. Put

    y_i=D lambda_i, with lambda_1>=...>=lambda_D,
    M_alpha(rho)=(1/D)sum_i y_i^alpha,
    M*_alpha=max_APPT M_alpha,
    E_alpha=log D-min_APPT S_alpha=log M*_alpha/(alpha-1),
    u_D=3D/(D+2), k_0=2/(m-1), p_m=1+k_0=(m+1)/(m-1),
    P=u_D^alpha/D.

All logarithms are natural. All limits below have m->infinity and
c=alpha/m->infinity. Thus alpha>1 and m>=3 eventually.

Define the exact scalar bulk quantities

    Z_k=(1+k)^alpha-1,
    q_k=(Z_k-alpha*k)/[k*Z_k*(alpha-1)]  for k>0,
    B_alpha(k)=Z_k/(alpha*k)
               [alpha/(alpha-1)*(1-k/Z_k)]^(1-alpha),
    B=B_alpha(k_0).                                                   (F1)

**Theorem F1.** For every L_m->infinity, uniformly over n>=m and
alpha>=m L_m,

    M*_alpha ~ max{P,B},
    log M*_alpha-log max{P,B} ->0.                                    (F2)

Moreover, uniformly in that same range,

    B ~ p_m^alpha/(e*alpha*k_0),
    log M*_alpha
      =max{alpha log u_D-log D,
            alpha log p_m-log(e*alpha*k_0)}+o(1).                     (F3)

The exact bases u_D and p_m are retained. Expanding them before multiplying
by an unrestricted alpha would not justify the additive o(1) statement.

**Theorem F2.** In the same fully unrestricted-aspect range,

    E_alpha ~ log max{P,B}/(alpha-1)
             ~ max{2/m, log u_D-(log D)/alpha}.                       (F4)

Both are first nonzero relative equivalents, including a bulk-dominated
deficit tending to zero. There is no upper bound on alpha or n; alpha can
grow arbitrarily faster than D.

Writing zeta=log(P/B), the critical moment window zeta->z in R has

    M*_alpha/B ->max{1,e^z}.                                         (F5)

This is a maximum transition. The sum P+B is not the correct leading law
when the two terms are comparable. The sublinear-order law in the earlier
paper instead retains the sum; the change is proved below by coupling.

## 2. Existing actual-state input and exact scalar optimization

Use Theorem V1 and its actual physical bridges in
[ALL_ORDER_VARIATIONAL.md](../appt-growing-renyi/ALL_ORDER_VARIATIONAL.md).
For every fixed epsilon>0, uniformly for alpha>=epsilon*m and n>=m,

    M*_alpha/V*_alpha ->1,                                           (F6)

where, with 0<=k<=k_0, 0<=q<=1,

    eta_m(k)=2(m-2)k^2/[2-(m-3)k],
    V_alpha(k,q)=[1+q((1+k)^alpha-1)
                   +P((3-eta_m(k))/3)^alpha]/(1+kq)^alpha,
    V*_alpha=max_(k,q) V_alpha(k,q).                                 (F7)

This is a theorem about the entire actual APPT set. Its upper coupling came
from all-unitary Schmidt witnesses; its lower comparison used finite
projection/spike APPT densities. Those existing constructions and the
earlier fixed-local projection calculation are credited inputs. F7 is an
approximant, not an assumed restriction to a family of spectra.

For fixed k>0, the scalar bulk S_k(q)=(1+q Z_k)/(1+kq)^alpha has derivative
whose sign is

    Z_k-alpha*k-k Z_k(alpha-1)q.

Strict Bernoulli gives Z_k>alpha*k, so its unique maximum is at q_k>0.
At q=1 the derivative is negative: the required inequality is the strict
convex tangent bound (1+k)^(1-alpha)>1+(1-alpha)k. Hence q_k<1.
Substitution gives exactly B_alpha(k) in F1.

For fixed 0<q<1, S_k(q) is strictly increasing in k: differentiating its
logarithm leaves a positive multiple of

    (1-q)[(1+k)^(alpha-1)-1].

The endpoint q=0 or q=1 gives one. Thus the largest possible scalar bulk
value throughout F7 is exactly B_alpha(k_0)=B.

Whenever alpha->infinity and alpha*k->infinity with 0<k<=k_0 and m grows,
the exact formula gives, uniformly,

    B_alpha(k) ~ (1+k)^alpha/(e*alpha*k).                              (F8)

Indeed Z_k/(1+k)^alpha->1, (alpha-1)log[alpha/(alpha-1)]->1, and
alpha*k/Z_k->0. Uniformity follows from k<=k_0->0 and
Z_k>=exp[alpha*k/(1+k)]-1. In particular F8 applies to k_0, proving the
bulk formula in F3. It also shows B->infinity uniformly in c->infinity.

## 3. Physical coupling makes simultaneous leading contributions impossible

Set eps=c^(-1/4). For the widths k<=eps*k_0, the scalar bulk is at most
(1+eps*k_0)^alpha. By F8 at k_0,

    (1+eps*k_0)^alpha/B
      <=O(c) exp[-alpha*k_0*(1-eps)/(1+k_0)] ->0.                    (F9)

The bound depends only on m and c, not on P or D.
For k>=eps*k_0, the exact protection satisfies

    eta_m(k)>= (m-2)k^2,
    ((3-eta_m(k))/3)^alpha
       <=exp[-alpha*(m-2)*eps^2*k_0^2/3]
       <=exp[-C sqrt(c)] ->0                                        (F10)

for a universal C>0 and all sufficiently large m. The factor
(1+kq)^(-alpha) only decreases this head term.

Consequently every point in F7 has one of the two bounds

    V_alpha(k,q)<=P+o(B)                       if k<=eps*k_0,
    V_alpha(k,q)<=B+o(P)                       if k>=eps*k_0.        (F11)

The errors are uniform in P>=0. Conversely k=0 gives 1+P, and maximizing
the bulk at k=k_0 gives at least B. Therefore

    V*_alpha ~max{P,B}                                              (F12)

uniformly over every n>=m and alpha>=m L_m. Combining F6 and F12 proves
the multiplicative F2. Taking logarithms turns both uniform relative errors
into additive o(1), proving the remaining F2 and F3. No trace expansion at
alpha much larger than D has been made.

The finite lower physical mechanisms are the exact pure spike
(I+2vv*)/(D+2), and the projection-only density proportional to I+k_0 Q
with rank(Q) chosen near q_(k_0) D. The latter is APPT because every unit
Schmidt vector satisfies sum_(i<j)s_i s_j<=(m-1)/2. In comparable peak/bulk
mass, the prior dimension dichotomy makes D exponentially large in alpha,
so integer rank rounding and trace errors vanish. In peak dominance, the
pure-spike bound retains u_D exactly. These are existing actual states.

## 4. Relative entropy and the simple equivalent

By F8,

    log B/(alpha-1)
       =[alpha log p_m-log(e*alpha*k_0)+o(1)]/(alpha-1)
       ~2/m,                                                       (F13)

uniformly for c>=L_m. Indeed log p_m~2/m, while
log(alpha*k_0)/(alpha/m)=O(log c/c)->0 uniformly c>=L_m.
Also log B->infinity uniformly, so the additive logarithmic o(1) in F2
is negligible relatively to log max{P,B}. This proves the first F4.

The peak logarithm divided by alpha-1 is
alpha/(alpha-1)[log u_D-log D/alpha]. If it is negative, the positive bulk
branch wins. If it is positive, multiplication by alpha/(alpha-1)->1 is
a uniform relative change. Combining this with F13 proves the second F4,
including windows where the branch values are comparable and both of order
1/m. The positive bulk floor is necessary at that scale.

For zeta->z, F2 divided by B proves F5. At z=0 the moment is asymptotic to
B, rather than 2B. The upcoming spectral criterion identifies the two
possible sharp branches and permits alternation; it does not infer a
simultaneously sharp mixed state from equality of the two benchmark values.

## 5. Scope

All assertions have m->infinity and alpha/m->infinity, uniformly in every
n>=m. They sharpen the value theorem within the same APPT direction.
Fixed-m growing-order optimization, exact finite optima, absolute
separability and complete Lean formalization are not claimed. No historical
first solution, external human peer review, new Release, DOI or submission
is asserted. Current primary literature and the inherited notes were
checked for the actual range; a missing search hit is not priority evidence.
