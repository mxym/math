# Binary Brenier stability: sharp mass crossover and a different boundary phase transition

Research continuation, 8 October 2026. Complete candidate analytic proof, pending the user's later unified review. No publication or independent audit is claimed. This argument does NOT use the centered-potential estimate (P), or the preceding top-N candidate.

## 1. Fixed source, target classes, and exact statements

Fix d>=2, p>2, and s=p/(p-2)>1. Independently fix a boundary exponent

    alpha=beta+1>1.

Let L>0 be C^2 near zero, with ell=log L satisfying

    x ell'(x)->0,       x^2 ell''(x)->0.                  (SV)

Use one fixed first marginal f which near zero equals

    f(x)=c x^(alpha-1)L(x) exp(-x^2/2),   x>0,

and has a C^2, 1-strongly convex negative logarithm and a quadratic far tail. Such an extension exists because its prescribed second derivative is 1+beta/x^2-ell''(x)>=1+beta/(2x^2) near zero; extend this derivative continuously above one, make it equal to one far away, and integrate twice. Normalize. The fixed source is

    r(x)=f(x_1) product_(j=2)^d g(x_j),
    g(z)=c_g exp[-1/(1-z^2)] 1_{|z|<1},
    rho(dx)=r(x)dx.

It is absolutely continuous, 1-strongly log-concave on its extended convex support, and has moments of every positive order. It stays fixed as all other parameters vary. Its distribution function and half-mass quantile are

    F(t)=integral_0^t f(x)dx,     q(m)=F^(-1)(m), 0<m<=1/2,
    T=q(1/2).

The statement below depends on the entire fixed f through constants and through q. The boundary asymptotics used later are

    F(t)~(c/alpha)t^alpha L(t),      t f(t)/F(t)->alpha.  (1.1)

Both follow by dominated convergence after rescaling the integral, using |x ell'(x)| arbitrarily small.

For every target with finite second moment, T_mu is its Brenier map from rho. All target classes impose integral |y|^p dmu<=1. Atom locations are not separately bounded. Distinct positive-mass locations are the actual support; repeated labels are merged and zero-mass labels discarded.

Define three moduli:

1. Omega_2(w): both targets have at most two actual atoms and W_2(mu,nu)<=w.
2. Omega_(2,eta)(w), 0<eta<=1/2: the same, and every positive atom of each target has mass at least eta. A Dirac mass is allowed.
3. Omega_[m](w), 0<m<=1/2: each target has the form (1-m)delta_a+m delta_b, a,b arbitrary, with the moment bound. Allowing a=b simply includes Dirac masses and does not change any result. The TWO targets have the same prescribed mass vector (1-m,m).

Each modulus is the supremum of ||T_mu-T_nu||_(L^2(rho)) over the indicated pairs.

Put

    B(t)=t F(t)^(1/(2s)),   0<t<=T,
    g_*(t)=F(t)^(1/(2s))/t.

B is continuous strictly increasing. For 0<w<B(T), let h_w be the unique solution

    w=h_w F(h_w)^(1/(2s)).                              (1.2)

For 0<r<=T define the running maximum

    G(r)=max_(r<=t<=T) g_*(t).                           (1.3)

### Theorem A: fixed mass and minimum-mass crossover

There exist c,C,w_0>0, depending only on the one fixed source, p, and d, such that the following hold simultaneously for EVERY 0<w<=w_0 and the stated entire mass ranges:

    Omega_[m](w)
       ~ w + min{m^(1/(2s)),
                  [w m^(1/(2s))/q(m)]^(1/2)},    0<m<=1/2;      (1.4)

    Omega_(2,eta)(w)
       ~ [w G(max{h_w,q(eta)})]^(1/2),           0<eta<=1/2;    (1.5)

    Omega_2(w) ~ [w G(h_w)]^(1/2).                           (1.6)

Here and below '~' between positive expressions denotes two-sided comparison up to positive constants, not a leading-coefficient asymptotic. The SAME constants work for all m or eta in the displayed intervals. In (1.5), w_0<B(T), so the interval in (1.3) is never empty.

There is no reliance on the preceding candidate top-N envelope. In particular the upper bounds are direct binary transport estimates, not consequences of (P).

### Corollary B: the binary boundary threshold is alpha=2s

For L=1, uniformly for small w,

    Omega_2(w) ~
       w^(alpha/(2s+alpha)),    1<alpha<2s;
       w^(1/2),                alpha>=2s.                (1.7)

Thus binary targets have a different phase boundary from the already established unrestricted / N>=3 power-law result, whose critical CDF exponent is alpha=s and whose interior obstruction is one third. A third atom can change the optimal power even though both budgets are fixed.

For a general (SV) factor:

- If 1<alpha<2s, Omega_2(w)~F(h_w)^(1/(2s))=w/h_w.
- If alpha>2s, Omega_2(w)~w^(1/2).
- If alpha=2s, choose a small fixed a<T in the source's prescribed region. Then

      Omega_2(w) ~ w^(1/2)
           [1+sup_(h_w<=t<=a) L(t)]^(1/(4s)).           (1.8)

  The added one absorbs the fixed interior range; any other fixed positive constant gives an equivalent expression. No monotonicity of L is assumed.

For L(t)=[log(e/t)]^gamma these become

    Omega_2(w) ~
       w^(alpha/(2s+alpha)) [log(e/w)]^(gamma/(2s+alpha)),
                                                    1<alpha<2s;
       w^(1/2) [log(e/w)]^(max(gamma,0)/(4s)),       alpha=2s;
       w^(1/2),                                    alpha>2s.   (1.9)

At the old critical source alpha=s, formula (1.9) gives

    Omega_2(w) ~ w^(1/3)[log(e/w)]^(gamma/(3s))        for ALL real gamma.

In particular negative gamma genuinely separates two atoms from three: the binary ratio to w^(1/3) tends to zero, while the inherited three-atom interior construction has a positive one-third lower ratio.

## 2. A weighted score controls every halfspace, in every orientation

We first prove the uniform geometric estimate needed for arbitrary binary target locations. This prevents the lower construction's preferred direction from being silently imposed on the upper bound.

### 2.1 Source regularity and score tail

The zero-extended density r is continuous, belongs to W^(1,1)(R^d), and satisfies

    r(x)<=C exp(-c|x|^2),
    |x|r(x) in W^(1,1)(R^d).

Near x_1=0, continuity follows from beta>0 and slow variation. The derivative is bounded by C x_1^(beta-1)L(x_1), which is integrable since beta>0. There is no boundary jump. Transverse boundary derivatives are integrable because g vanishes faster than every power, and far-tail integrability follows from the quadratic extension.

On the source interior define the nonnegative weighted score

    A(x)=1+|x| |grad log r(x)|.

Set it arbitrarily, say zero, on the rho-null complement. There is C such that its decreasing rearrangement satisfies

    A^*(u)<=C/q(u),                  0<u<=1/2,             (2.1)
    integral_0^m A^*(u)du <= C m/q(m), 0<m<=1/2.          (2.2)

Proof. Write X=x_1, Z_j=x_j, and D_j=(1-|Z_j|)^(-2). The source formula and its extension give

    A <= C[1+X^2+X^(-1)+(1+X)sum_(j>=2) D_j].            (2.3)

The X^(-1) term has tail F(1/t). The other first-coordinate terms have Gaussian or exponential tails, and P(D_j>t)<=C exp(-c sqrt(t)). For the product, the union bound

    P((1+X)D_j>t)
       <= P(1+X>t^(1/3))+P(D_j>t^(2/3))
       <= C exp(-c t^(1/3))

holds for large t. The polynomial lower bounds on F(1/t) from slow variation absorb all these faster tails. Fixed-ratio comparison of F then yields P(A>t)<=C F(1/t). Absorbing the outside constant by a fixed change in t, again using regular variation of F, proves (2.1) for small u; enlarge C for the compact remaining interval.

Because alpha>1, choose r_0 with 1/alpha<r_0<1. Integration of the inverse logarithmic derivative F(x)/(x f(x))->1/alpha gives

    q(v)>=C^(-1)q(m)(v/m)^(r_0),   0<v<=m<=1/2.

Its integral proves (2.2). QED.

### 2.2 Weighted halfspace trace bound

For every halfspace H={x:u dot x>c}, |u|=1, with rho(H)=m<=1/2,

    integral_(boundary H) |x|r(x) dH^(d-1)(x)
       <= integral_H A d rho
       <= C m/q(m).                                      (2.4)

To see the first inequality, apply the divergence theorem for the W^(1,1) vector field u|x|r(x) on H, with a large-radius cutoff and then let the cutoff tend to infinity. The outward normal on the finite boundary is -u, so

    integral_(boundary H) |x|r
       = -integral_H u dot grad(|x|r)
       <= integral_H [r+|x||grad r|].

The right side is exactly the indicated bound. The identity initially holds for almost every c by Sobolev slicing. It holds for all c by continuity of the hyperplane integrals: r is continuous with a Gaussian envelope, and local orthogonal parametrizations of hyperplanes permit dominated convergence. The cutoff tails tend to zero by the same envelope. The second inequality is the elementary rearrangement bound on an m-mass set followed by (2.2).

No alignment of H with a coordinate axis was assumed.

### 2.3 Moving a fixed-mass halfspace

For each unit u and 0<m<1, let H_(m,u) be the unique upper halfspace normal to u with rho-mass m. All projected laws are atomless. The projection of the open convex source interior is an interval, and its density is positive at any quantile of mass strictly between zero and one. Thus the threshold is unique.

For 0<m<=1/2 and any unit u,v,

    rho(H_(m,u) triangle H_(m,v))
       <= C min{m, angle(u,v) m/q(m)}.                    (2.5)

Proof. Along a shortest spherical path u(t), let c(t) be the threshold preserving mass m. The function giving halfspace mass is C^1 in normal and threshold: locally write the boundary as a graph over a fixed hyperplane, then differentiate the integral; continuity and the Gaussian envelope justify differentiation. Its threshold derivative is minus the strictly positive hyperplane density. The implicit function theorem gives a C^1 threshold along the path, locally and hence over the compact path.

Differentiating the mass constraint gives

    c'(t)= [integral_(u(t) dot x=c(t)) u'(t) dot x r(x)dH]
              /[integral_(u(t) dot x=c(t)) r(x)dH].

The normal velocity is u'(t) dot x-c'(t). Its weighted absolute integral is at most

    2|u'(t)| integral_(u(t) dot x=c(t)) |x|r(x)dH
       <= C |u'(t)| m/q(m),                              (2.6)

by (2.4). Integrating the boundary-crossing estimate along the path proves the angular bound. One can justify this estimate by smoothing the indicator of a halfspace, applying the fundamental theorem of calculus, and passing to the limit using the displayed continuous hyperplane integrals. The path length is angle(u,v). The trivial symmetric-difference bound is 2m. Combining them proves (2.5), after changing C. QED.

This estimate is what allows arbitrary binary directions and arbitrary cell shapes, including directions almost parallel to the source boundary.

## 3. Exact binary target coupling after centering

Every non-Dirac binary target can be written

    mu=(1-m)delta_a+m delta_b,    0<m<=1/2,
    v=b-a,    R=|v|>0,
    bar_mu=a+m v.

Its Brenier map is

    T_mu=bar_mu+v(1_(H_(m,u))-m),   u=v/R.                (3.1)

Indeed the maximum of two affine functions has those two gradients and selects an upper halfspace normal to v. Adjust its intercept to give the prescribed mass; uniqueness of Brenier maps supplies (3.1).

The moment bound gives

    |bar_mu|<=1,        |v|<=C m^(-1/p).                  (3.2)

The second estimate follows directly from |a|<=(1-m)^(-1/p) and |b|<=m^(-1/p). No centered pth-moment assertion is needed.

For a second binary target nu, write its rare mass n<=1/2, gap vector z, length S, and barycenter bar_nu. Both target and map squared distances split off their barycenters:

    W_2(mu,nu)^2=|bar_mu-bar_nu|^2+W_c^2,
    ||T_mu-T_nu||_2^2=|bar_mu-bar_nu|^2+D_c^2.            (3.3)

A coupling of the centered binary targets is determined by tau=P(I=1,J=1), where I,J are Bernoulli of means m,n. Its centered cost is

    m(1-m)R^2+n(1-n)S^2-2(tau-mn) v dot z.              (3.4)

The feasible interval is max(0,m+n-1)<=tau<=min(m,n). This exactly solves the 2x2 transport problem: choose the upper endpoint when v dot z>=0, and the lower endpoint otherwise.

Assume first v dot z>=0 and relabel the TWO targets so m<=n. Then

    W_c^2=m(1-n)|v-z|^2
             +(n-m)[mR^2+(1-n)S^2].                    (3.5)

In particular, because n<=1/2,

    m|v-z|^2 <=2 W_c^2,
    (n-m)S^2<=2 W_c^2.                                  (3.6)

Let A=H_(m,v/R), B=H_(n,z/S). A halfspace with fixed normal is nested in its mass, so

    rho(A triangle B)
       <= n-m + rho(H_(m,v/R) triangle H_(m,z/S)).        (3.7)

Writing the centered map difference as

    (v-z)(1_A-m)+z[(1_A-1_B)-(m-n)]

and taking the square norm gives

    D_c^2<=2m|v-z|^2+2S^2 rho(A triangle B).             (3.8)

For the angle theta between the two vectors, with 0<=theta<=pi/2,

    theta <= C |v-z|/max(R,S).                            (3.9)

This follows because |v-z|>=max(R,S)sin(theta), by minimizing the other vector's length, and theta<=pi sin(theta)/2 on this range.

Combine (2.5), (3.2), and (3.6)-(3.9). If W_2<=w, then

    S^2 rho(H_(m,v/R) triangle H_(m,z/S))
       <= C min{m S^2, S|v-z| m/q(m)}
       <= C min{m^(1/s), w m^(1/(2s))/q(m)}.             (3.10)

Therefore all acute pairs satisfy

    ||T_mu-T_nu||_2^2 <= C[w^2+Psi(w,m)],
    Psi(w,m)=min{m^(1/s), w m^(1/(2s))/q(m)},            (3.11)

where m is their smaller rare mass. In particular, m is at least eta if a minimum weight eta is imposed.

### Obtuse directions are not omitted

Suppose v dot z<0. If m+n<=3/4, the lower feasible coupling endpoint is zero, and (3.4) gives

    W_c^2 >= (1-m-n)(mR^2+nS^2)
           >= (mR^2+nS^2)/4.                             (3.12)

Here use 2RS<=R^2+S^2 to bound the negative cross term. The map variance is at most 2(mR^2+nS^2), so the map distance is at most Cw.

If m+n>3/4, both m,n exceed 1/4. Reverse the two labels of nu: its gap becomes -z, its distinguished mass becomes n'=1-n in [1/2,3/4), and its centered map is unchanged. Now v dot (-z)>0 and m<=n', while 1-n'>1/4. Formula (3.5) remains valid, with n', and controls |v+z|<=Cw and (n'-m)S^2<=Cw^2. Both gap lengths are bounded by a fixed constant from their original moment bounds. The comparison in (3.7) uses only the angular lemma at mass m, which is in (1/4,1/2]. Its q(m) is bounded below. Thus the same calculation gives

    ||T_mu-T_nu||_2^2 <= C(w^2+w).                        (3.13)

The estimate remains valid when the vectors are tiny: use S^2 theta<=C S|v+z|, never divide by a fixed positive lower bound on a gap.

For two targets with the SAME prescribed rare mass m, the last case requires m>3/8. Choose w_0<=q(3/8)(3/8)^(1/(2s)). Then Psi(w,m)=w m^(1/(2s))/q(m)>=c w throughout m>=3/8, so (3.13) is absorbed by (3.11). For a minimum-mass or unrestricted class, its supremum of Psi includes m=1/2, which likewise absorbs Cw. Finally, if either target is a Dirac mass, the map distance equals W_2 exactly, since there is only one coupling to a Dirac mass. All degeneracies are therefore covered.

## 4. Genuine two-atom lower examples with exactly prescribed masses

Fix ANY 0<m<=1/2 and write t=q(m). The two atoms will have masses exactly 1-m and m throughout the construction, even as w varies.

There is one sufficiently small epsilon>0, depending only on the fixed source, such that for every t in (0,T] and 0<b<=epsilon t the following holds. Define

    H_b(y)=E F(y+bZ),       ell_b=H_b^(-1)(F(t)),
    A={X<t},              C={X<ell_b+bZ},

where Z has the symmetric transverse density g. Both cells have mass m exactly. The inverse exists, and bracketing gives |ell_b-t|<=b. On [t-2b,t+2b], density comparability and |f'|<=C f(t)/t hold uniformly. These follow near zero from (SV), and on the remaining compact range from f>0 and C^2 regularity. Symmetry E Z=0 and Taylor expansion improve the intercept to

    ell_b=t+O(b^2/t).                                    (4.1)

The cell disagreement has the exact representation

    rho(A triangle C)=E|F(ell_b+bZ)-F(t)|
                    =b f(t) E|Z|+O(b^2 f(t)/t).

One fixed choice of epsilon gives

    c b f(t)<=rho(A triangle C)<=C b f(t).                (4.2)

Also f(t) is uniformly comparable to F(t)/t over 0<t<=T: use (1.1) near zero and positivity/continuity on the compact remainder.

Let R=m^(-1/p), and define

    mu=(1-m)delta_0+m delta_(-R e_1),
    nu=(1-m)delta_0+m delta_(R(-e_1+b e_2)/sqrt(1+b^2)).   (4.3)

Each target has precisely two distinct positive-mass atoms and pth moment exactly one. The maps are gradients of the global hinge potentials

    U(x)=R(t-x_1)_+,
    V(x)=R/sqrt(1+b^2) (ell_b-x_1+b x_2)_+.              (4.4)

Thus they are genuine Brenier maps, not assigned step functions. The same-label target coupling gives

    W_2(mu,nu)<=m^(1/(2s)) b.                             (4.5)

Indeed the difference between (-1,0) and (-1,b)/sqrt(1+b^2) has length at most b. On the mismatch A triangle C, one source map is zero and the other has length R. Consequently,

    ||T_mu-T_nu||_2^2>=R^2 rho(A triangle C)
                     >=c b m^(1/s)/t.                   (4.6)

Choose

    b=epsilon min{t, w/m^(1/(2s))},

also taking epsilon<=1. Then W_2<=w and

    ||T_mu-T_nu||_2^2>=c Psi(w,m).                        (4.7)

All constants are uniform in m,w. The locations may tend to infinity as m decreases, precisely as permitted by the moment class. There is no hidden lower mass condition.

To obtain the remaining w term in (1.4), use the same mass vector with two short, distinct atoms, for example (1-m)delta_0+m delta_(e_1/4), and translate the whole target by w e_2, for w<=1/4. Both pth moments remain below one. Translation adds the same vector to the Brenier map, and its Wasserstein distance is exactly w by the barycenter lower bound and the translating coupling. Thus the map distance is w. Taking the better of this example and (4.7), and using max(A,B)>=(A+B)/2, proves the lower half of (1.4).

The preceding upper argument proves its upper half after taking square roots. This completes the fixed-mass formula, without any use of (P).

## 5. Optimize the mass, with or without a minimum weight

From Sections 3-4, uniformly for 0<eta<=1/2,

    Omega_(2,eta)(w)^2 ~ sup_(eta<=m<=1/2) Psi(w,m).       (5.1)

The possible w^2 terms are absorbed: at m=1/2 and small w, Psi(w,1/2)=c_0 w>=c_0 w^2. The same reasoning gives the unrestricted binary formula with 0<m<=1/2.

Make the exact change m=F(t). The two arguments of the minimum in Psi are equal if and only if

    w=t F(t)^(1/(2s))=B(t).

B is strictly increasing, so the change occurs uniquely at t=h_w. For t<=h_w, the smaller argument is F(t)^(1/s), increasing in t. For t>=h_w, the smaller argument is w g_*(t). If the admissible interval includes h_w, its entire lower portion has maximum at h_w, and that value is already w g_*(h_w). If its lower endpoint exceeds h_w, only the second regime is present. Therefore, EXACTLY,

    sup_(eta<=m<=1/2) Psi(w,m)
       =w max_(max{h_w,q(eta)}<=t<=T) g_*(t).             (5.2)

For no minimum weight replace max{h_w,q(eta)} by h_w. Equations (5.1)-(5.2) prove (1.5)-(1.6).

The maximum in (5.2) is over a compact interval and is attained. The lower example in Section 4, at that maximizing mass, has both its masses at least eta. This closes the actual target-position, mass, coupling and convex-gradient optimization; it is not merely a one-sided mass-profile envelope.

## 6. Evaluate the phase diagram

By (1.1),

    g_*(t) ~ t^(alpha/(2s)-1)L(t)^(1/(2s)),
    d log g_*(t)/d log t = t f(t)/(2s F(t))-1
                         -> alpha/(2s)-1.               (6.1)

### Subcritical binary boundary: alpha<2s

The derivative in (6.1) is strictly negative for all sufficiently small t, and g_*(t) tends to infinity. Hence for all small h, the running maximum on [h,T] is exactly g_*(h): the finite maximum on the remaining compact range is eventually dominated. Thus

    Omega_2(w) ~ [w g_*(h_w)]^(1/2)
               =F(h_w)^(1/(2s))=w/h_w.                  (6.2)

The identity uses (1.2), not a substitution h=w raised to a power. It remains valid for nonmonotone (SV) factors because the nonzero power in (6.1) dominates their logarithmic derivative.

### Supercritical binary boundary: alpha>2s

Now g_*(t) tends to zero at the boundary and has a finite positive maximum on (0,T]. Its running maximum therefore approaches a finite positive limit. Equation (1.6) gives Omega_2(w)~w^(1/2).

### Critical binary boundary: alpha=2s

The power vanishes and g_*(t) is comparable to L(t)^(1/(2s)) near zero. The fixed compact remainder contributes a finite positive constant. Hence (1.6) gives (1.8), with the ACTUAL h_w from (1.2). A local endpoint value L(h_w) need not control the running maximum for oscillatory L.

For L=1 this proves (1.7). For logarithmic powers, solve

    w ~ h^(1+alpha/(2s)) [log(e/h)]^(gamma/(2s)).

Its logarithm shows log(e/h)~log(e/w), and standard substitution with fixed multiplicative comparison gives

    h ~ w^(2s/(2s+alpha)) [log(e/w)]^(-gamma/(2s+alpha)).

For alpha<2s, substitute into w/h to obtain (1.9). For alpha=2s the running maximum of the logarithmic factor grows as [log(e/h)]^gamma when gamma>0 and is bounded when gamma<=0. For alpha>2s use the preceding supercritical argument. Every statement is for all sufficiently small w, not merely a subsequence.

## 7. The explicit minimum-weight crossover in the old critical family

Take alpha=s, corresponding to beta=s-1 in the completed critical-atom result. Choose eta_0>0 small enough that g_*(t) is decreasing on (0,q(eta_0)] and exceeds its later compact maximum there. For 0<eta<=eta_0 and small w, Theorem A simplifies to

    Omega_(2,eta)(w) ~
       [w eta^(1/(2s))/q(eta)]^(1/2),
                           w<=q(eta)eta^(1/(2s));
       F(h_w)^(1/(2s)),    w>=q(eta)eta^(1/(2s)).         (7.1)

The constants are simultaneous in eta,w. The threshold is the actual mass-quantile scale, not an unspecified eta-dependent constant.

For L=1, q(eta)~eta^(1/s), and (7.1) becomes

    Omega_(2,eta)(w) ~ min{w^(1/3), w^(1/2)eta^(-1/(4s))} (7.2)

for all 0<eta<=eta_0 and sufficiently small w. The crossover is w~eta^(3/(2s)). Thus fixing a positive minimum atom weight improves the exponent from one third to one half, with the exact divergence of the one-half constant as the mass floor disappears.

For the EXACT mass vector (1-m,m), the extra large-w saturation is different and is not replaced by the minimum-weight formula:

    Omega_[m](w) ~ w+min{m^(1/(2s)), w^(1/2)m^(-1/(4s))}  (7.3)

for L=1 and small m,w, uniformly. The w term matters when the whole rare component is much smaller than the allowed translation distance.

For a general slow factor at alpha=s, keep q(eta) in (7.1) and q(m) in (1.4). Since q(eta)^s L(q(eta)) is comparable to eta, the half-power coefficient is also comparable to

    eta^(-1/(4s)) L(q(eta))^(1/(2s)).                    (7.4)

The exact quantile formulas are safer than replacing q(eta) by a bare power for arbitrary (SV) factors.

## 8. New versus inherited statements and scope boundaries

The three main increments are:

1. A direct upper-and-lower optimal law for ALL binary targets, permitting both positions and masses to vary, and not assuming a preferred direction or shared zero atom in the upper bound.
2. Uniform sharp formulas for a fixed binary mass vector and for a disappearing lower bound on positive atom masses.
3. The binary boundary threshold alpha=2s and its critical running-maximum correction, distinct from the already completed alpha=s threshold for unrestricted targets and N>=3.

The original two-atom rare-cell mechanism belongs to entry 008. Here its rotation is made independently tunable at an exactly prescribed mass, and a new all-directions binary upper bound is matched to it. Neither Brenier uniqueness, two-affine-plane convexity, nor elementary 2x2 coupling optimization is claimed as a new general mechanism.

The top-N slowly-varying candidate in the preceding folder is NOT an input. Comparisons to its proposed sharper N>=3 envelope remain conditional on that candidate's later review. The assertion that three atoms have an interior one-third obstruction is already in the completed entry 008 and suffices for the negative-gamma binary-versus-three-atom separation stated above.

No theorem here claims arbitrary source classification or a fixed-mass N>=3 result. The general (SV) theorem assumes beta>0, so the zero-extended density has no first-boundary jump and its weighted score is integrable. The hard-boundary beta=0 power source can be handled separately by a bounded hyperplane-trace argument, but it is not silently included in the proof above. Dimension one remains isometric and is excluded.

## 9. Literature and dependency notes

Primary sources checked in the current research pass:

- Bansil and Kitagawa, Quantitative stability in the geometry of semi-discrete optimal transport, arXiv:2002.02022v2: https://arxiv.org/html/2002.02022 . Their fixed-support Laguerre-cell stability is a relevant comparison, including weight dependence. The present problem allows arbitrary changing binary support and measures target distance in W_2.
- Delalande and Merigot, Quantitative stability of optimal transport maps under variations of the target measure: https://arxiv.org/html/2103.05934 . Background for quantitative map stability.
- Cyril Letrouit, Unstable optimal transport maps, arXiv:2510.13265 (2025): https://arxiv.org/abs/2510.13265 . Its full text, https://arxiv.org/html/2510.13265v1 , explicitly uses rotating equal-weight two-atom targets to exhibit strong instability for a source with boundary density blow-up. Thus rotation of binary targets and fixed-weight counterexamples are established mechanisms, not claimed new here. Our source family instead has a vanishing boundary density and an integrable weighted score; the new candidate statements are the matching mass-dependent modulus and the alpha=2s classification. This short screening does not settle historical priority.
- The completed predecessor source-phase construction: https://github.com/mxym/math/blob/c2281bc871c9bf60994985d6665ae45f4711d080/preprints/008-density-overlap-phase/v1/main.tex .

The proof above is self-contained apart from standard existence/uniqueness of quadratic Brenier maps for an absolutely continuous source and elementary Sobolev divergence/slicing, change of variables, dominated convergence, and the implicit function theorem. In particular, no centered-potential stability theorem is imported.

The prior 459-line candidate was left unchanged. Its SHA-256 at the start of this continuation was c3cf5061de5ac9298f3fb88e07800c9d88257b01a1cd80f82fdc5e1a083055c1.
