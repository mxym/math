# Exact finite Haar-vs-independent transcript distance without quantum memory

## 1. Model and results

Let d>=1 be the complex Hilbert-space dimension and t>=0 the round count. In law P a single Haar pure state is drawn and t copies are supplied. In law Q, t independent Haar pure states are drawn. An observer sequentially measures each copy once. Arbitrary classical adaptation is allowed, including a common classical random tape independent of the states. Arbitrary fresh auxiliary systems and one-copy quantum channels with classical output are allowed; the ancillary input of each step may be prepared using the classical past, but no quantum memory or shared entanglement across rounds is retained and copies are not measured jointly. Fresh ancillas and classical-output operations induce POVMs on the corresponding input copy. Increments quoted below are not about the more general purity-testing task with an arbitrary alternative state.

Write V(d,t) for the supremum over these strategies of total variation between the full classical transcript laws, with TV(P,Q)=sup_A |P(A)-Q(A)| (equivalently half the L1 distance). For equal prior probabilities, the optimal decision probability based on a transcript is (1+TV)/2. We permit finite or countable measurement outcomes (in particular classical strings); the same upper bounds extend to standard Borel outcomes as described below. The lower bounds use finite measurements.

With alpha_t=product_{j=0}^{t-1}(1+j/d), if alpha_t-1<=1/64, then

    V(d,t) = (1-1/alpha_t) product_{j=0}^{t-1}(1-j/d).            (1)

The empty product is 1, and d=1 gives zero actual distance for every t. In the nontrivial range t>=2 of (1) one necessarily has t<=d. In particular d>=64 t^2 suffices. Repeated measurement in any fixed orthonormal basis attains (1), by the distinct-outcome event.

For all d, V(d,0)=V(d,1)=0 and V(d,2)=(d-1)/(d(d+1)). At t=3 the exact values are

    d=1: 0;
    d=2: 1/4;
    d=3: 1/15 + sqrt(3)/10;
    d=4: 13/60;
    d=5: 8(21-sqrt(66))/525;
    d>=6: (3d+2)(d-1)(d-2)/(d^2(d+1)(d+2)).                 (2)

A fixed repeated basis attains (2) for d=2 and d>=6. Feed-forward attains the listed larger values for d=3,4,5. We make no claim of complete optimality outside (1) and the cases t<=3.

## 2. Rank-one learning trees and the permanent

Conditional on the classical past, a measurement is a POVM. We can refine each positive effect into rank-one effects and keep the refined label in the classical transcript, using only the original coarsened label to choose future POVMs when simulating the original protocol. Taking a marginal can only decrease TV, so a rank-one-strategy upper bound is sufficient. Zero effects are omitted. For standard Borel outcomes, take the scalar reference measure tr(M(dz))/d for a POVM M and use the positive matrix-valued Radon-Nikodym density of M. Refine its density into outer products of the columns of its positive square root, then retain the column index. This gives the same argument by integration. An independent random tape may be conditioned on, or retained as part of the transcript; fixed upper bounds apply uniformly to it.

In law Q, conditional on any past the next copy has density I/d. If a selected rank-one effect is a |v><v| for a unit vector v and a>=0, its conditional Q probability is a/d. In particular the conditional expectation of |v><v| equals I/d. This identity uses the POVM sum, not any assumption that successive chosen directions are uniform on the sphere.

For a fixed path of unit directions v_1,...,v_t, let G_t=(<v_i|v_j>)_{i,j<=t} and P_t=per(G_t), with P_0=1. The conditional weights a used by an adaptive strategy on this particular path are the same in the two path probabilities. The averaged density of t copies in law P is Pi_sym / binom(d+t-1,t). Expanding the symmetric projector as an average over permutations gives

    dP/dQ = P_t / alpha_t.                                     (3)

In particular paths with zero Q have zero P. This is valid for adaptive protocols, because for each fixed path its POVM effects and their order are fixed before evaluating the path probability. The symmetric state identity can also be proved using complex Gaussian coordinates: a standard circular complex Gaussian vector has independent Haar direction and squared radius with moment d(d+1)...(d+t-1). The coordinate monomials have zero unequal phase moments and paired moments given by the factorials of the coincident indices, yielding the permutation sum after division by this radial moment.

Their total variation can be written as E_Q[(1-dP/dQ)_+], since their total masses agree. Hence the optimization is of E_Q[(alpha_t-P_t)_+]/alpha_t. These likelihood ratios are for the *full measured records*, not for a hypothetical joint quantum measurement.

## 3. Occupation-space increment

On the r-particle symmetric space, define the unnormalized product

    Phi(v_1,...,v_r) = sqrt(r!) Pi_sym (v_1 tensor ... tensor v_r).

It has norm squared P_r. Let a^dagger(w) map xi in this space to sqrt(r+1) Pi_sym(w tensor xi), and let a(w) denote its adjoint on the next particle sector (using the same notation at every sector). On the r-particle sector a(w) is sqrt(r) times contraction with <w| in the first slot when r>0. Thus a^dagger(w) appends w to Phi, and

    a(w) Phi(v_1,...,v_r) =
       sum_i <w|v_i> Phi(v_1,...,omit v_i,...,v_r).             (4)

The relation a(w)a^dagger(w)-a^dagger(w)a(w)=||w||^2 I follows either by symmetrizing that first-slot contraction or by the normalized occupation basis: creation in coordinate i raises its occupation k_i with factor sqrt(k_i+1), annihilation lowers it with factor sqrt(k_i), and operators in distinct coordinates commute in this commutator.

Put V_r=[v_1 ... v_r] and let H_r be the Gram matrix in the order of the r missing-one vectors on the right of (4). These symbols concern a fixed transcript prefix. For unit w the relation gives

    P_(r+1) = P_r + <w|B_r|w>,
    B_r = V_r conjugate(H_r) V_r^dagger >= 0.                  (5)

Indeed the vector of coefficients in (4) is conjugate(V_r^dagger w); expanding its norm gives the entrywise conjugate of H_r in (5), with our convention that the inner product is linear in the second variable. Equivalently, under the Haar hypothesis the posterior mean after this path is (I+B_r/P_r)/(d+r): compare the conditional probability of the next projector in (3) and use alpha_(r+1)/alpha_r=(d+r)/d. Thus B_r/P_r is the operator part in the known posterior formula. For r=0 take B_0=0. This proves monotonicity under appending any unit directions. The basic permanent likelihood and this positive marginal operator have precedents (see SOURCES.md); the main step below is a uniform lower bound on the nonzero spectrum at low likelihood, then its use in an exact adaptive optimization.

## 4. A uniform spectral bound in a small-deficit prefix

Define S_r=sum_{i<j} |(G_r)_(i,j)|^2. We first prove: if S_r<=1/32, then

    H_r >= (45/64) I_r,
    B_r has rank r and its nonzero eigenvalues are >= 135/256.     (6)

For r=1 the bound follows directly from H_1=(1) and B_1=|v_1><v_1|. In general the Frobenius error satisfies ||G_r-I||_F^2=2 S_r. Hence the operator norm error is at most 1/4, so G_r is positive definite with minimum eigenvalue at least 3/4. Put L=ln G_r (natural logarithm). The scalar bounds ln(1+z)>=z-z^2 for |z|<=1/4 and sum of eigenvalue deviations z equal to zero give tr L>=-2S_r>=-1/16. The scalar bound follows by integrating the derivative -z/(1+z) of ln(1+z)-z. Also lambda_min(L)>=ln(3/4). Each diagonal entry of L is nonpositive: apply concavity of the scalar logarithm to the eigenvalue distribution in the corresponding coordinate vector, whose G_r expectation is 1.

On the (r-1)-particle symmetric space over C^r, let e_(hole i) be the normalized state with one particle in each coordinate except i. These are orthonormal, and applying the symmetric tensor power of V_r sends them to the missing-one Phi vectors. Consequently H_r is the compression of the symmetric tensor power of G_r to their span. This tensor power is exp(dGamma(L)), where dGamma(L) is the sum of L acting in each individual tensor position. On occupation states it acts as sum_{a,b} L_(a,b) a_a^dagger a_b; this follows by applying the one-particle map to each of the particles and counting identical terms. Its compression to the hole subspace is exactly

    (tr L) I_r + L^T - 2 diag(L).                              (7)

To see this, for a diagonal hole i sum L_(j,j) over j!=i; for distinct target hole i and input hole j, the only way to move the hole is to remove the particle at i and place it at j, with coefficient L_(j,i) and both occupation factors 1. The matrix L^T is Hermitian and has the same eigenvalues as L. Since diag(L)<=0, (7) is at least (ln(3/4)-1/16) I. For any normalized vector in the hole subspace, the spectral theorem and scalar Jensen applied to exp give an expectation of exp(dGamma(L)) at least exp(ln(3/4)-1/16). This argument uses convexity of the scalar exponential in a one-vector spectral measure, not operator convexity of exp. Since e^(-1/16)>=15/16, the result is at least 45/64. This proves the H_r assertion. The columns of V_r are independent; B_r>= (45/64) V_r V_r^dagger, with support exactly their span. On that span the smallest eigenvalue of V_r V_r^dagger is the smallest eigenvalue of G_r, at least 3/4. This proves (6).

Let 0<delta<=1/64. For every prefix with P_r<=1+delta, we now show S_r<= (3/2)(P_r-1)<=3/128. The base r=1 has zero both sides. By monotonicity all ancestors stay under the same threshold. At an inductive step the preceding S_(r-1)<=3/128<1/32 makes (6) applicable. Using (4) before the last vector is appended gives

    P_r-P_(r-1) >= (2/3) sum_{i<r} |<v_i|v_r>|^2,

because 45/64>2/3. Add this to the inductive inequality. This bootstrap shows that at every prefix with positive deficit relative to 1+delta, the rank and spectral lower bound (6) hold. It does not assume that arbitrary Gram matrices satisfy a lower bound on H_r.

## 5. Conditional Jensen and exact birthday-scale optimization

Fix the comparison threshold A=alpha_t with 0<A-1<=1/64, and write f(P)=(A-P)_+. At a prefix with P_r>=A, (5) makes all future deficits zero. Otherwise let u=A-P_r in (0,1/64]. By (6), B_r has r nonzero eigenvalues, each greater than u. For any next unit vector w the spectral probabilities |<e_j|w>|^2 in an eigenbasis of B_r give

    (u-<w|B_r|w>)_+ <= <w|(u I-B_r)_+|w>.

This is scalar convexity of the positive part. Conditioned on the prefix in law Q, the expectation on the right is tr((u I-B_r)_+)/d=(1-r/d)u by the POVM normalization. This holds for every allowable conditional POVM, and an eigenbasis attains the bound at that step. At r=0 the deficit is fixed. Hence iteration of conditional expectations yields

    E_Q f(P_t) <= (A-1) product_{r=0}^{t-1}(1-r/d).           (8)

The product is used for t<=d. In (1), t>=2 and A-1>= (t-1)/d, so t<=d. If A=1 the actual t is 0 or 1 and no estimate is needed. For d>=64t^2, ln A<=t(t-1)/(2d)<=1/128, and e^h-1<=2h on [0,1/128], giving the stated sufficient range.

A fixed repeated orthonormal basis gives independent uniform outcomes under Q. Distinct outcomes have G_t=I and hence P_t=1. If any two repeat, reorder that pair first: its two-vector permanent is 2, and (5) makes P_t>=2>A. Thus equality in (8) holds by counting the distinct Q outcomes. Divide by alpha_t to obtain (1). This is simultaneously an optimum over classical adaptive choices and over the subclass which repeats a fixed measurement. Taking d=2^n and polynomial t(n) covers the asymptotic setting of c/0104 with a sharper *finite* value once d>=64t^2. The usual O(t^2/d) upper bound itself was already known: (5) gives P_t>=1 in the older pointwise likelihood argument.

## 6. Exact three-round calculation

For two rounds, the first rank-one direction is u and the continuation may have any finite or countable POVM. The value x=|<u|v>|^2 for the second direction has Q conditional mean 1/d. The Haar likelihood-ratio numerator is P_2=1+x. By the chord upper bound for the convex function (1/d-x)_+ on [0,1], its expectation is at most (1-1/d)/d, achieved by the same-basis measurement where x is 0 or 1. Division by alpha_2 gives the stated V(d,2).

For three rounds take d>=2 and condition on the first two directions u,v, with overlap squared x. Their phases may be chosen so that <u|v>=sqrt(x). From (5) the two candidate eigenvalues of B_2 are (1+sqrt(x))^2 and (1-sqrt(x))^2, since the two-by-two Gram G_2 and the missing-one Gram agree under this phase choice. More explicitly they are the eigenvalues of G_2^(1/2) conjugate(H_2) G_2^(1/2)=G_2^2, and the rest are zero. If x=1, include the zero eigenvalue among the two candidates; the support then has rank one. Set A=alpha_3=(d+1)(d+2)/d^2. The largest conditional Q expected third-round deficit equals h_d(x)/d, where

    h_d(x) = (d-2)(A-1-x)_+
           + (A-2-2x-2 sqrt(x))_+
           + (A-2-2x+2 sqrt(x))_+.                           (9)

Spectral Jensen proves the upper bound, and an eigenbasis realizes it. It remains to optimize the expectation over x with conditional mean 1/d. Every finitely supported law for x with that mean can be realized as a conditional POVM on the second copy. Given the first u, let e_1,...,e_(d-1) be an orthonormal basis of its orthogonal complement. For each desired atom x, use the unit directions sqrt(x)u +- sqrt(1-x)e_j over j with equal weights. Their average projector is x|u><u|+(1-x)(I-|u><u|)/(d-1). Mix the directions with the desired atom probabilities, and multiply the resulting weights by d to make the effects. The mean condition makes their sum I (hence all effects valid, even at duplicated directions). Under Q this realizes the desired law; a first fixed basis suffices, and the third choice is conditional on both directions. In all cases below an affine upper bound to h_d is saturated by a finite such law. The final optimum is its expectation divided by d A.

* d=2: A=3, and (9) is the maximum of 2-4x and 1-2x+2 sqrt(x). Both are at most 2-x using 2 sqrt(x)<=1+x; equality at the respective endpoints 0,1. The endpoint law with mean 1/2 gives 1/4 after dividing by d A.
* d=3: A=20/9. The first term A-1-x is positive and A-2-2x+2 sqrt(x) is positive throughout. Thus (9) is the maximum of 5/3-5x and M(x)=13/9-3x+2 sqrt(x). The tangent to the concave M at x=1/3 has intercept 13/9+1/sqrt(3)>5/3 and slope -3+sqrt(3)>-5. It dominates both terms over [0,1]. Constancy at x=1/3 gives the optimum (2).
* d=4,5,6: set s=2-A and a=A-1=1-s. The positive branch of -s-2x+2 sqrt(x) vanishes for x>=a, since a>1/4 and its value at a is -(1-sqrt(a))^2<=0. Hence (9) is the maximum of C(x)=(d-2)(a-x)_+ and M(x)=(d-2)a-s-dx+2 sqrt(x). For d=4 the tangent to M at x=1/4 is 17/8-2x, which dominates C(x) as well. Constancy at x=1/4 gives 13/60.
* For d=5 specifically, put c=(41-4 sqrt(66))/25, the smaller positive solution of c+1/c=2+4s=82/25. It satisfies 0<c<2/5, since z+1/z decreases on (0,1) and 82/25>2/5+5/2. The tangent to M at x=c^2 is the line (5-1/c)(1-x): differentiate M and use the equation for c. It also dominates C(x), because at 1 both vanish and at 0 the inequality is 1/c<74/25, equivalent to 4 sqrt(66)<33. The convexity of C gives the interior inequality. The law supported on c^2 and 1 with mean 1/5 realizes the optimum in (2).
* For d=6, the chord L(x)=(d-2)a(1-x) bounds C(x), by convexity. The difference M-L=-s-beta x+2 sqrt(x) is at most -s+1/beta with beta=2+(d-2)s. For s=4/9, s beta=136/81>1. Thus the chord also bounds M, and the endpoint law is optimal. For d>=7, A<=3/2 and the last two terms in (9) vanish (2 sqrt(x)-2x<=1/2), so the same endpoint chord again attains the optimum. In these cases the endpoint law is precisely the same-basis measurement and yields (2).

A repeated basis gives 17/90, 7/40, and 34/175 for d=3,4,5 respectively: under Q, distinct triples have permanent 1, those with exactly two equal have permanent 2, and all equal have permanent 6. Substitute in the deficit. These values are strictly smaller than the corresponding values in (2). The comparison is to repeating the same basis only. All of the results concern sample-state idealizations, with no assertion about applications or cryptographic implementations.
