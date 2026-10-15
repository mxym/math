# The first coexistence threshold of the linear-order APPT entropy profile

Yongxian Zhang (张永贤), South China University of Technology.
15 October 2026, Asia/Shanghai. Author proof, independent read pending.
No external funding; OpenAI AI assistants assisted. Original rights reserved.

## 1. Original quantum setting and credited value theorem

Use actual complex PSD trace-one APPT densities on C^m tensor C^n, meaning
PPT after EVERY global unitary. Let m<=n, D=mn and y_i=D lambda_i, with
the eigenvalues decreasing. For alpha>1 put

    M*_alpha=max_APPT D^-1 sum_i y_i^alpha,
    E_alpha=max_APPT(log D-S_alpha)=log M*_alpha/(alpha-1).

The already completed linear-order theorem L1 identifies the sharp scalar
profile uniformly over all n>=m and alpha/m in fixed positive compact
intervals as m->infinity. Its scalar definitions are

    G(L)=2L^2/[3(2-L)], 0<=L<2,
    B(c,L,h)=exp(-cLh)[1+h(exp(cL)-1)],
    P(c,L,h)=exp[-c(Lh+G(L))], P(c,2,h)=0,
    F(c,r;L,h)=B(c,L,h)+r P(c,L,h),
    F_*(c,r)=max_([0,2]x[0,1]) F(c,r;L,h).

Here c>0,r>=0. One has M*_alpha/F_*(alpha/m,3^alpha/D)->1 in that
uniform range. Put

    b(k)=(exp(k)-1)/k * exp[-1+k/(exp(k)-1)],
    g(k)=log b(k), b(0)=1, g(0)=0,
    h_bulk(c)=1/(2c)-1/(exp(2c)-1).

The credited calculation gives max B=b(2c)>1, with the unique maximizing
pair (2,h_bulk(c)); the pole L=0 gives 1+r. The complete all-order VALUE
theorem is older work and is not re-claimed. This note determines when
the pure-bulk scalar value first ceases to be globally optimal, including
the small-c threshold, every tie, and the relevant actual spectra.

## 2. A positive attained threshold and exact mixing optimization

For 0<=L<2 define

    U(c,L,h)=[b(2c)-B(c,L,h)]/P(c,L,h),
    r_bulk(c)=min_(0<=L<2,0<=h<=1) U(c,L,h).          (B1)

At L=0, U=b(2c)-1 independently of h. The function U is positive,
and it tends to infinity as L->2 uniformly in h and locally uniformly
in c>0. To see this, B(c,L,h)<=b(cL) and P<=exp[-cG(L)]. For c in
a fixed positive compact interval and L near 2,

    b(2c)-b(cL)>=C(2-L),
    exp[cG(L)]>=exp[C'/(2-L)],

with positive constants C,C'. The first inequality follows by integrating
b'(k)>0 on a positive compact interval, and the second follows directly
from G. Their product diverges. Thus the minimum in B1 is attained
away from L=2, is positive, and depends continuously on c. The same
uniform divergence reduces continuity to the maximum/minimum theorem
on one fixed compact set near every fixed c. In particular

    0<r_bulk(c)<=b(2c)-1.                            (B2)

The exact identity

    F(c,r;L,h)-b(2c)=P(c,L,h)[r-U(c,L,h)]             (B3)

for L<2 proves the complete bulk-onset criterion:

* For r<r_bulk, F_*=b(2c) and the unique scalar maximizer is the
  pure-bulk pair (2,h_bulk(c)).
* At r=r_bulk, the full scalar argmax set is that bulk pair together
  with EVERY minimizer of U.
* For r>r_bulk, F_*>b(2c), so no L=2 point is a scalar maximizer.

This retains possible zero-width and multiple-width ties at the threshold.
It does not assume that the intermediate-c phase boundary is unique.

There is an exact one-dimensional formula for B1. Fix K=2c and
0<k=cL<K, and write

    a=2k^2/[3(K-k)], q(k)=k/(exp(k)-1), A(k)=1/q(k).

Then

    U=exp(a)[b(K)exp(kh)-1-h(exp(k)-1)].              (B4)

The bracket is strictly convex in h. Its derivative is
b(K)k exp(kh)-(exp(k)-1), and the unconstrained minimizer is

    h_U(k,K)=[log A(k)-g(K)]/k.                      (B5)

It is always less than 1: A(k)<exp(k) and g(K)>0. Consequently the
unique constrained minimizer is max(0,h_U). If h_U<=0, its value is
exp(a)[b(K)-1], which is at least the zero-width value. If h_U>0,
direct substitution and g(k)=log A(k)-1+q(k) give the simpler identity

    min_h U=exp(a)[g(K)-g(k)]/q(k).                  (B6)

The min in B1 may therefore be computed from the zero-width competitor
and the widths with h_U>0, using B6. No numerical maximization is being
used to establish this formula.

## 3. Small-c global compactness before expansion

**Theorem B (first coexistence at small positive c).** For every sufficiently
small c>0, U has a unique minimizing pair (L_B(c),h_B(c)), with 0<L_B<2
and 0<h_B<1. The rescaled width t_B(c)=[2-L_B(c)]/c and h_B(c)
extend real analytically to c=0. They satisfy

    t_B(c)=8/3+(16/9)c+O(c^2),
    L_B(c)=2-(8/3)c-(16/9)c^2+O(c^3),
    h_B(c)=1/2-c/6-(4/9)c^2+O(c^3),
    r_bulk(c)=(4e/3)c^3-(28e/9)c^4+O(c^5).           (B7)

The unique rescaled maximum/minimum assertion in this theorem is GLOBAL.
Here is the required endpoint localization, before applying a local series.
The analytic even extension of g near zero has expansion

    g(k)=k^2/8-k^4/576+O(k^6).                        (B8)

For example this follows by adding the convergent series of
log[(exp(k)-1)/k]-1+k/(exp(k)-1). It follows that b'(k)>=k/8 for all
sufficiently small k>=0. Hence for 0<=L<2 and small c>0,

    b(2c)-B(c,L,h)
      >=b(2c)-b(cL)>=c^2(4-L^2)/16
      >=c^2(2-L)/8.                                (B9)

The trial width L=2-(8/3)c, with the unique B5 mixing, is interior
for small c and B6 gives U=O(c^3). Thus every GLOBAL minimizing pair
satisfies U<=C c^3. Since P<=1, B9 forces 2-L<=8C c.
In particular L->2, k/(2c)->1, and B5 is positive and tends to 1/2;
every global minimizing h must equal that unique interior mixing.

Put t=(2-L)/c. We have t bounded above. Since L>=1 for these minimizers,
the stronger combination of B9 with P<=exp[-cG(L)] gives

    U/c^3 >=(t/8)exp[2/(3t)].                        (B10)

If t->0 the right side tends to infinity. Therefore every global
minimizer has t in ONE fixed compact subinterval of (0,infinity),
independent of small c. This excludes both moving width endpoints and
all exponentially thin boundary layers.

On that compact interval, set k=2c-c^2 t. B6 becomes

    U/c^3=Phi(c,t)
      =[g(2c)-g(2c-c^2t)]/c^3
         *exp[2(2-ct)^2/(3t)]/q(2c-c^2t).            (B11)

The function extends real analytically through c=0 locally uniformly in
t>0; the numerator has a factor c^3 because g'(0)=0 and its arguments
differ by c^2t. B8 gives the limiting function

    Phi(0,t)=psi(t)=(t/2)exp[8/(3t)].                 (B12)

This has its unique global minimum at t0=8/3, with value 4e/3 and
psi''(t0)=3e/16>0. Uniform convergence on the fixed compact interval
from B10 proves that every global minimizer tends to t0. The analytic
implicit function theorem, with positive second derivative there, now
gives a unique analytic minimizing branch. Global localization proves
that it is the unique GLOBAL branch for every sufficiently small c.
This proves the existence and uniqueness parts of the theorem.

## 4. Coefficients, active phases and the first derivative jump

For the coefficients, the locally uniform analytic expansion of B11 is

    Phi(c,t)=exp[8/(3t)]
      [t/2+c(-t^2/8-5t/6)+O(c^2)].                  (B13)

At t0 the coefficient of c is -28e/9, and its t derivative is -e/3.
The derivative of the optimal t is therefore
(-(-e/3))/(3e/16)=16/9. Substitution gives r_bulk and L_B in B7.
Using B5 and B8 gives

    h_U(2c-c^2t,2c)=1/2-c/6-(t/6)c^2+O(c^3),        (B14)

which gives h_B in B7. These series and their needed derivatives hold
uniformly near t0 by analyticity. They are not based on a stationary
calculation before proving global localization.

For small c, r_bulk=O(c^3)<b(2c)-1~c^2/2, so the zero-width pole is
strictly below the optimum at this first coexistence. B3 and the unique
global minimizer show that at r=r_bulk there are exactly TWO scalar
maximizing pairs: the pure bulk pair and (L_B,h_B). Their body laws have
different support widths for each such fixed c, although their small-c
limits agree. No extra scalar convex combination is inserted.

The Hessian of U at its minimum is positive definite: its h curvature
is strictly positive by B4, and the Schur complement is the positive
width curvature supplied by B11 and the implicit function theorem.
Differentiating B3 twice at the mixed minimizer gives

    Hess F=-P Hess U.

Thus for r just above r_bulk the global nonbulk maximizer is a unique
analytic branch. The usual compact sublevel argument using U<=r places
all competing maximizers near the unique minimizer; the divergent
L=2 endpoint and the higher L=0 value cause no escape. On this branch
the objective is strictly greater than the bulk value.

At the threshold the one-sided derivatives are exactly

    (d/dr)_- F_*=0,
    (d/dr)_+ F_*=P_B(c):=P(c,L_B(c),h_B(c)).          (B15)

This follows either from the branch or from the slopes of the two active
affine competitors. The log-profile derivatives are divided by b(2c).
Since c[L_B h_B+G(L_B)]->1, we have

    P_B(c)->exp(-1),
    derivative jump of log F_* ->exp(-1) as c->0+.    (B16)

## 5. Connection to the upper threshold and actual spectra

The companion scalar pole-onset analysis defines

    r_crit(c)=max_(L,h) (B-1)/(1-P),

with the continuous zero convention at L=0. It already supplies the exact
criterion F_*>1+r iff r<r_crit. Combining the two exact criteria yields
an elementary structural conclusion: for a fixed c either

    r_bulk=b(2c)-1=r_crit,

or

    r_bulk<b(2c)-1<r_crit.                           (B17)

In the latter case the values strictly exceed BOTH pure values for every
r in the single open interval (r_bulk,r_crit), and for no other r.
There are no separated mixed intervals in r. To verify B17 directly for
one interior competitor, write A=(b(2c)-B)/P and Q=(B-1)/(1-P).
Then b(2c)-1=P A+(1-P)Q. Hence A<b(2c)-1 iff Q>b(2c)-1.
Taking the infimum or maximum proves both strict inequalities at once.
Endpoint competitors do not create a strict inequality. This does not
prove that the set of c having a mixed interval is connected or has a
unique endpoint. That intermediate-c question remains separate.

The actual quantum consequences use the existing L1 and complete spectral
criterion S. Fix one small c>0 and let m->infinity, n>=m, alpha/m->c,
3^alpha/D->r_bulk(c). Actual first-nonzero-scale entropy near-optimality
is equivalent to distance of the S width/mixing parameters to the TWO
pairs above tending to zero, AND both the S chord/spread loss and actual
peak loss tending to zero. These losses are not removed. Every scalar
pair has an actual integer-rank all-global-unitary APPT realization by S.

The possible full empirical body laws of m(D lambda_i-1) are exactly

    (1-h_bulk(c))delta_(-2h_bulk(c))
          +h_bulk(c)delta_(2(1-h_bulk(c))),
    (1-h_B(c))delta_(-L_B(c)h_B(c))
          +h_B(c)delta_(L_B(c)(1-h_B(c))).            (B18)

These are 1-Wasserstein subsequential limits; alternating phases are
allowed. At the pure-bulk branch the actual peak moment tends to zero.
At the interior mixed branch it tends to r_bulk(c)P_B(c)>0 and

    m(3-D lambda_max)->3[L_B h_B+G(L_B)].             (B19)

Thus, after FIRST taking the fixed-c physical limit, the right side of
B19 multiplied by c tends to 3 as c->0. Likewise the mixed peak moment
is asymptotic to (4/3)c^3 in this iterated limit. Both body laws in B18
tend to (delta_(-1)+delta_1)/2 as c->0, despite these different peak
patterns. No interior peak expansion is applied at the bulk width 2.

These are iterated fixed-c then c->0 conclusions. This note does not
assert a new uniform physical theorem on paths alpha/m->0; L1 and S have
their original fixed positive compact/fixed-c hypotheses. There is no
exact finite-dimensional cutoff, full intermediate-c phase diagram,
complete all-order spectral rigidity, Lean audit expansion, submission,
external human peer review, priority certificate or new major count.
