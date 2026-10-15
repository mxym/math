# A single mixed-c interval for the APPT linear-order scalar problem

Author: Yongxian Zhang (张永贤), South China University of Technology.
Contact: mxymmxym1@gmail.com. ORCID: 0009-0000-3864-3536.
Date: 2026-10-15. Author manuscript, pending independent ordinary review.
No Lean claim, submission, or new-major claim. No funding. OpenAI assisted the
mathematical investigation and writing. Original text: all rights reserved;
third-party results retain their attribution and rights.

## Scope, inputs and limits

The scalar definitions F=B+rP, V=max F, b, r_0 and the actual complex APPT
interpretation are those of LAST_MIXED_BOUNDARY.md. The exact frozen inputs are:

* PURE_ENVELOPE_GE_ONE.md, SHA-256
  ad1a5aabca9d3fcf2e960cbf43bcf7cfbdfd232cc58b86bbaf355229656016a9;
* LAST_MIXED_BOUNDARY.md, SHA-256
  6e4f77e2bbecbc5e71f426925d444e8e1a9b69d2ffebcbef88badc1f4e87f0a0.

Both are complete author arguments still awaiting ordinary independent review.
We use their explicit small-c witness, c>=1 pure estimate, and endpoint compactness
to locate the threshold strictly between 1/10 and 1 and transfer boundary ties.
The new no-islands argument itself is proved in full below. No root collaborator's
unreviewed scalar or small-c lower-onset draft is a dependency. The exact h
elimination is independently derived here; its antecedent fixed-width elimination
is credited to theorem L20 of LINEAR_ORDER_VARIATIONAL.md, whose source bytes are
recorded in CREDITED_SOURCES.json.

The credited main results L and S establish the value and actual-spectrum
nearoptimizer correspondence for complex density matrices APPT under every global
unitary, with m<=n, m tending to infinity, alpha>1, alpha/m tending to c>0 and
3^alpha/(mn) tending to finite r. The present note adds scalar structure to those
results. It does not replace the full APPT problem by a restricted matrix ansatz.

The threshold parameter below is unique. This does NOT assert uniqueness of the
interior scalar maximizer at that threshold, or uniqueness of every strict mixed
branch at arbitrary r. Those are separate questions left open here.

## Theorem

There is exactly one number c_star such that strict mixed value occurs for some
r>=0 precisely when 0<c<c_star. Moreover 1/10<c_star<1.

For c>c_star the complete scalar value and argmax are the two pure branches:

    V(c,r)=max{b(2c),1+r},

with only the unique pure bulk maximizer for r<r_0(c), only the pole class for
r>r_0(c), and exactly those two classes at r=r_0(c).

At c=c_star the same all-r value holds, but its crossing r=r_0(c_star) has a
nonempty finite set of additional interior maximizers. They tie the bulk and pole.
The theorem of LAST_MIXED_BOUNDARY transfers these ties to distinct attainable
body laws for actual complex-density APPT nearoptimizers, with the loss conditions
of S retained.

More explicitly, each fixed width fraction x=L/2 in (0,1) has one analytic
crossing curve K_x>0, with K=2c, such that this width gives a strict improvement
over the pure crossing exactly for 0<K<K_x. Then

    2 c_star = max_(0<x<1) K_x.

The maximum is attained at finitely many interior x. At the last boundary,
each maximizing x gives one and only one interior h at this particular width.
No numerical estimate for c_star is used to prove this theorem.

## 1. Elementary functions and derivatives

For t>0 define

    q(t)=t/(exp(t)-1),         d(t)=1-q(t),
    w(t)=-log q(t),           g(t)=w(t)-d(t)=log b(t),
    s(t)=w'(t)=exp(t)/(exp(t)-1)-1/t=1-d(t)/t,
    e(t)=t d'(t)/d(t).

Here 0<q<1, 0<d<1, s>0 and d'=s q>0. In fact s>1/2, as proved by
H(t)=(t-2)exp(t)+t+2>0 with H(0)=H'(0)=0,H''(t)=t exp(t)>0.
One has

    g'=s d>0,
    w''=1/t^2-exp(t)/(exp(t)-1)^2>0,
    q''=exp(t)H(t)/(exp(t)-1)^3>0,
    g''=w''+q''>0.

The inequality for w'' follows from 2sinh(t/2)>t. Thus g is strictly convex.

The proof will use two quantitative derivative inequalities. The constants
are sufficient constants; no assertion of sharpness is needed.

## 2. A curvature bound for g

For every t>0,

    t g''(t)/g'(t) > 1-g(t)/2.                    (2.1)

To prove it, put z=(t-d)/d>0. Since d'=q(t-d)/t,

    t g''/g' = t d'/d + t s'/s
              = qz-q+1/z.

By the arithmetic-geometric mean inequality,

    qz+1/z >= 2 sqrt(q),
    t g''/g' >= 1-(1-sqrt(q))^2.

For y=sqrt(q) in (0,1),

    g/2-(1-sqrt(q))^2 = -log y-3/2+2y-y^2/2 > 0.

Indeed the expression is zero at y=1 and its derivative is
-(1-y)^2/y<0 for y<1. This proves (2.1) strictly.

## 3. An elasticity barrier

For every t>0 such that e(t)>1/2,

    e(t)<1-w(t)/4.                               (3.1)

This implication, rather than an unrestricted linear bound for e, is the
claim needed below. In particular it is never applied at large w with a
negative right-hand side.

Since w is strictly increasing from zero to infinity, use w as variable and
write q=exp(-w), d=1-q. Direct differentiation of e=q(t-d)/d gives the ODE

    de/dw = -e + q(e+q)(1-e)/[(1-q)e].            (3.2)

All denominators are positive for the present solution. At w=0 the removable
expansions from exp(t) give

    w=t/2+O(t^2),       e=1-t/6+O(t^2),
    e(w)=1-w/3+O(w^2).

Thus e(w)<E(w)=1-w/4 initially. We show that E is a strict upper barrier
throughout 0<w<=2. At any contact with E, put E=1-w/4 in [1/2,1). The
right side of (3.2) is strictly less than E'=-1/4 exactly when

    E+q < 4[(exp(w)-1)/w] E(E-1/4).              (3.3)

Use the elementary bounds q<=1/(1+w)=1/(5-4E) and
(exp(w)-1)/w>=1+w/2=3-2E. A sufficient condition for (3.3), after
multiplying by the positive 5-4E, is

    R(E)=32E^4-96E^3+86E^2-20E-1 > 0.

This condition holds on the entire interval [1/2,1]:

    R(1/2)=1/2, R(1)=1,
    R''(E)=384E^2-576E+172 <= -20.

For the last bound note that this quadratic is convex and has value -20
at both endpoints, so it lies below their constant chord. R is concave
and lies above its positive endpoint chord. This is a whole-interval
polynomial proof, not sampling.

Consequently a first upward contact of e with E before or at w=2 is
impossible, since at such a contact (3.2) gives e'<E'. Hence e(2)<1/2.
For w>=2, at a contact with the constant barrier e=1/2, (3.2) becomes

    de/dw = -1/2+q(1/2+q)/(1-q) < 0.

Here q<=exp(-2)<1/5, and the positive fraction is at most 7/40<1/2.
A first upward crossing of this constant barrier is also impossible.
Therefore e>1/2 can occur only for w<2, where the first strict barrier
already proves (3.1).

## 4. Fixed-width reduction of the mixed-value test

Put K=2c, k=cL, x=k/K=L/2 in (0,1) and u=K-k. For L<2 set

    a=2k^2/[3(K-k)]=cG(L),
    U(K,k,h)=[b(K)-B]/P
      =exp(a)[b(K)exp(kh)-1-h(exp(k)-1)].

At the pure crossing r_0=b(K)-1, a strict mixed value exists at this
width precisely when min_h U<r_0. This follows simply by multiplying
F-b(K)>0 by the positive 1/P. The strict convexity

    U_hh=exp(a)b(K)k^2 exp(kh)>0

gives the unique optimal h. Define

    v=w(k)-g(K),     Delta=g(K)-g(k)>0.

If v<=0 the constrained minimum is h=0, and U_min=exp(a)r_0>r_0.
If v>0, the unique minimum is h=v/k. It lies in (0,1), since
w(k)<k and g(K)>0. Exact substitution gives

    U_min = exp(a) Delta/q(k).                   (4.1)

Indeed exp[g(K)+kh]=exp[w(k)]=1/q(k), and
Delta=d(k)-v. Thus strict mixed value at this width is equivalent to

    v>0 and W(K,x)<0,
    W=2Kx^2/[3(1-x)]+log H(K,x),
    H=Delta/[q(k)(exp(g(K))-1)].                 (4.2)

The restriction v>0 is essential. No inequality for W outside that
admissible domain is used.

## 5. The admissible domain is a unique initial interval

Fix x in (0,1), and regard all functions in (4.2) as functions of K.
The function v(K)=w(xK)-g(K) is strictly concave. To see this, write

    t^2 w''(t)=1-[t/(2sinh(t/2))]^2.

It is strictly increasing in t>0, since sinh(z)/z is strictly increasing.
Consequently

    x^2 w''(xK)<w''(K)<g''(K),
    v''(K)<0.

One has v(0)=0 by removable continuation and v'(0)=x/2>0. On the other
hand, the large-K expansions w(t)=t-log t+o(1) and
g(t)=t-log t-1+o(1) show

    v(K)=-(1-x)K-log x+1+o(1) -> -infinity.

Strict concavity now implies that exactly one finite T_x>0 satisfies
v(T_x)=0, and v>0 exactly on (0,T_x). This step excludes the possibility
that a fixed width becomes admissible again at a later K.

## 6. A monotone normalized g increment

On 0<K<T_x, with k=xK and Delta=g(K)-g(k), one has

    d/dK [Delta/d(k)^2] > 0.                     (6.1)

Fix K in this interval and abbreviate E=e(k), treated as a constant in
the following auxiliary function of t:

    chi_E(t)=t g'(t)-2E g(t).

For k<=t<=K,

    chi_E'(t)=g'(t)[t g''(t)/g'(t)+1-2E] > 0.

If E<=1/2 this follows from g',g''>0. If E>1/2, admissibility says
g(K)<w(k), so for all such t, using (2.1) and (3.1),

    t g''/g' > 1-g(t)/2 > 1-w(k)/2 > 2E-1.

Thus chi_E(K)>chi_E(k), or

    K[g'(K)-x g'(k)]-2e(k)Delta > 0.

Since K d(d(k))/dK /d(k)=e(k), this is exactly the strict derivative
statement (6.1). In particular the proof has used the admissibility
restriction g(K)<w(k) at the decisive point.

## 7. Monotonicity of H on the entire admissible domain

Still for fixed x and 0<K<T_x, Delta'>0 because g' is strictly positive
and strictly increasing. By (6.1), d(k)/sqrt(Delta) strictly decreases;
sqrt(Delta) strictly increases. Since v=d(k)-Delta>0,

    v/sqrt(Delta)=d(k)/sqrt(Delta)-sqrt(Delta)

strictly decreases. Equivalently,

    2v'/v < Delta'/Delta.                        (7.1)

Set phi(v)=exp(-v)-1+v>0. The denominator of H is

    q(k)(exp(g(K))-1)=exp(-v)-q(k)=Delta+phi(v),
    H=Delta/[Delta+phi(v)].                      (7.2)

Here phi'>0, and phi(v)/v^2 is strictly decreasing: the integral identity

    phi(v)/v^2=integral_0^1 (1-t)exp(-tv) dt

shows that its derivative is strictly negative. Thus phi'/phi<2/v.
If v'>0, (7.1) implies

    (phi'/phi)v' < 2v'/v < Delta'/Delta.

If v'<=0, the first expression is nonpositive, whereas Delta'/Delta>0.
In both cases phi(v)/Delta strictly decreases. Formula (7.2) proves

    partial_K H(K,x)>0                           (7.3)

throughout the admissible domain. Therefore W in (4.2) has strictly
positive K derivative there: its first summand has the positive constant
derivative 2x^2/[3(1-x)], and log H also strictly increases.

## 8. One crossing for each width; no islands in c

For fixed x in (0,1), the small-K expansions g(t)=t^2/8+O(t^3) and
q(t)=1+O(t) give

    lim_(K->0+) H(K,x)=1-x^2,
    lim_(K->0+) W(K,x)=log(1-x^2)<0.

As K tends to T_x from below, v tends to zero, H tends to one by (7.2),
and therefore W tends to 2T_x x^2/[3(1-x)]>0. The strict monotonicity
from Section 7 proves that there is exactly one K_x in (0,T_x) for which
W(K_x,x)=0. For admissible K the strict mixed test is exactly K<K_x;
outside admissibility the minimum already strictly exceeds r_0.

All functions are real analytic for 0<K<T_x,0<x<1, and W_K>0.
The analytic implicit-function theorem shows that x -> K_x is analytic
on (0,1). Define K_star=sup_(0<x<1) K_x. The complete strict mixed set
is consequently

    {c>0:some strict mixed value at some r}=(0,K_star/2).

This is just the union over x of the nested initial intervals (0,K_x),
followed by K=2c and the crossing test proved in LAST_MIXED_BOUNDARY.
In particular there are no additional mixed-c components.

The small-c witness and c>=1 bound in the frozen input note show
0<K_star<=2 and 1/10<c_star=K_star/2<=1. The last-boundary compactness
theorem there improves the latter inequality to c_star<1, and supplies
at least one interior crossing tie. At such a tie the strict convexity
in h of U forces h=v/k, and hence W(K_star,x)=0. Thus K_x=K_star:
the supremum over x is attained.

## 9. Full pure argmax above the threshold; finitely many boundary ties

If K>K_star, every positive interior width has either v<=0, giving
U_min=exp(a)r_0>r_0, or v>0, giving K>K_x and W(K,x)>0. In either
case its value at the pure crossing is strictly below b(K). The h faces
also have strict inequality. Only the pole and the unique bulk maximizer
remain at the crossing. The affine interpolation argument in the frozen
input gives the asserted all-r pure envelope and complete argmax.

At K=K_star, all additional crossing ties have 0<L<2,0<h<1 and lie in
a common compact subset of that rectangle by the same endpoint estimates.
For this fixed K the admissible x domain is one interval (x_a,1):
w(Kx) is strictly increasing and crosses g(K) once between 0 and K,
because 0<g(K)<w(K). On it W(K,x) is real analytic. It is not identically
zero. In fact as x tends to one,

    Delta = g'(K)K(1-x)+o(1-x),
    log H = log(1-x)+O(1),
    W = 2Kx^2/[3(1-x)]+log(1-x)+O(1) -> +infinity.

The zeros corresponding to ties lie in a compact subset of the analytic
interval by the endpoint compactness. A nonconstant real analytic function
has only finitely many zeros on such a compact subset. Hence there are
finitely many boundary x and, by strict convexity of U in h, exactly one
boundary h for each such x. These x are precisely the global maximizers
of the analytic curve K_x. Their number, possible equality of branches,
and nondegeneracy are not established here.

## 10. Actual APPT consequences and remaining work

The no-islands theorem identifies one transition in the parameter c for
the existence of any strict mixed value. Combined with L and S, it gives
the complete pure-region actual-spectrum criteria above c_star and the
finite collection of additional attainable mixed body laws at the crossing
when c=c_star. Distances must always be taken to the full scalar argmax,
and the spread J and actual peak loss must still tend to zero, as required
by S. At the threshold the interior laws are additional global maximizers;
they cannot be discarded merely because the numerical value is the pure
envelope.

For c<c_star, the present proof establishes existence of strict mixed
value and an analytic fixed-width crossing description. It does not yet
give a unique interior maximizing width for every r, an exact elementary
formula for c_star, or a certified enclosure for its value. Those are
genuine remaining tasks. Floating-point discovery roots are not used by
any proof above. This manuscript and its dependencies remain author-only
until independent ordinary review binds the exact final bytes.
