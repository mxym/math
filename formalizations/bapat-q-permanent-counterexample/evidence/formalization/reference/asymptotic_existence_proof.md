# An independent existence proof of failure of q-permanent monotonicity

Date: 2026-10-08. This companion proof does not depend on the order-200 integer certificate. No historical priority or proof-assistant certification is claimed. The construction uses complex Hermitian Gram matrices and does not settle the real-symmetric restriction.

For any square matrix A, let P_q(A)=sum_{sigma} q^{inv(sigma)} product_i A_{i,sigma(i)}. The claim addressed is monotonicity for non-diagonal Hermitian positive definite A and -1<=q<=1. We construct a finite-dimensional counterexample in that domain, by first finding a rank-two positive-semidefinite endpoint witness.

## A. Endpoint identity: full proof with complex conventions

Let v_i=(a_i,b_i) be nonzero rows in C^2, and set

A_ij = a_i conjugate(a_j) + b_i conjugate(b_j).

Thus A=VV* is Hermitian PSD. Define

F(x,y)=product_{i=1}^n (a_i x+b_i y),
S(x,y)=sum_{1<=i<j<=n}(a_i b_j-b_i a_j) product_{k notin {i,j}}(a_k x+b_k y).

For p=sum_{k=0}^d p_k x^{d-k}y^k, use the squared Bargmann norm

||p||_B^2=sum_{k=0}^d (d-k)! k! |p_k|^2.

The inner product is linear in its first argument. If ell_i=a_i x+b_i y, then <ell_i,ell_j>_B=A_ij. The complex Gaussian moment identity, or direct monomial expansion, gives

< product_{i in I}ell_i, product_{j in J}ell_j >_B = per A[I,J]

whenever the two lists have equal length. In particular ||F||_B^2=per A. Also

(a_i b_j-b_i a_j) conjugate(a_k b_l-b_k a_l)
= A_ik A_jl-A_il A_jk.

It follows directly that

||S||_B^2=sum_{i<j,k<l}(A_ik A_jl-A_il A_jk) per A[{i,j}^c,{k,l}^c].  (A1)

There are no signs on the complementary permanent: both complements are listed in increasing order, and a permanent is invariant under independent reordering.

On the other hand, differentiate the defining q-permanent at q=1. For every permutation, count its inversions by pairs i<j. If its values on that pair are l>k, its contribution is A_il A_jk times the ordinary permanent of the complementary submatrix. Therefore

P'_1(A)=sum_{i<j,k<l} A_il A_jk per A[{i,j}^c,{k,l}^c].             (A2)

No inversion count on the complementary permutation appears, because q=1 after differentiation and one is counting a single marked inversion.

For each fixed row pair i<j, the two-row permanent expansion is

per A=sum_{k<l}(A_ik A_jl+A_il A_jk) per A[{i,j}^c,{k,l}^c].

Sum over the N=binom(n,2) row pairs, and subtract (A1). Comparing with (A2) proves the exact identity

2P'_1(A)=N||F||_B^2-||S||_B^2.                                  (A3)

Thus ||S||_B^2>N||F||_B^2 is a rigorous finite endpoint witness. Since P'_q is a polynomial, P'_1<0 implies P'_q<0 on some interval (1-delta,1], yielding a counterexample strictly inside (-1,1). Since every row is nonzero, A has positive diagonal. If desired, A+epsilon I is positive definite and retains the strict negative derivative for sufficiently small epsilon>0 by continuity.

## B. Repetition identity and sphere integral

Suppose each original row v_i is repeated L times contiguously, preserving the original order of the n groups. Let A_L be the resulting nL by nL Gram matrix. Then

F_L=F^L,  S_L=L^2 F^{L-1}S.                                     (B1)

Indeed pairs within a group have zero determinant, and each ordered pair of distinct original groups contributes exactly L^2 equal terms.

Let mu be normalized Haar measure on CP^1, represented by unit vectors (x,y) in C^2. For any homogeneous binary form p of degree d,

||p||_B^2=(d+1)! integral |p|^2 dmu.                             (B2)

This follows from integral |x|^{2a}|y|^{2b}dmu=a!b!/(a+b+1)! and the vanishing of mixed phase moments.

Writing g=|S/F|^2 where F is nonzero, (B1)-(B2) yield

R_L := ||S_L||_B^2/[binom(nL,2)||F_L||_B^2]
= [2L^2/(n^2(L^2 n^2-1))] [integral |F|^{2L}g dmu / integral |F|^{2L}dmu].   (B3)

The product |F|^{2L}g is understood as |F|^{2L-2}|S|^2, so there is no singularity issue at zeros of F for L>=1.

If |F| has a unique projective global maximum u, then

lim_{L->infinity} R_L=2g(u)/n^4.                                (B4)

Here is a direct justification that handles the possible poles of g. It is continuous near u since |F(u)|>0. Outside any neighborhood of u, |F|<=a<|F(u)|. Choose a smaller neighborhood of u of positive measure on which |F|>=b>a. Its contribution bounds the denominator below by a positive constant times b^{2L}. Since S is bounded on the compact sphere, the numerator outside the original neighborhood is bounded by a constant times a^{2L-2}; its normalized contribution vanishes exponentially. Concentration near u proves (B4).

Consequently a base configuration satisfying g(u)>n^4/2 at a unique global maximum generates a finite endpoint counterexample for all sufficiently large L.

## C. Ordering converts the peak score into a Gini pair sum

Choose a unitary Q with Qe_1=u, using a unit column representative of u, and make the variable substitution zeta=Qw. Coefficient rows transform as v_i -> v_i Q. Thus the Gram matrix is unchanged, F_new(w)=F_old(Qw), and S_new(w)=det(Q) S_old(Qw). Since |det(Q)|=1 and Haar measure is unitary invariant, all relevant norms and modulus ratios are unchanged. The chosen maximum is now at e_1=(1,0). At the maximum every a_i is nonzero, because F(u) is nonzero. Put z_i=b_i/a_i, and x_i=Re z_i. At u=(1,0),

S(u)/F(u)=sum_{i<j}(z_j-z_i)=sum_i (2i-n-1)z_i.                  (C1)

Order the rows so that x_1<=...<=x_n. This does not change F or its maximum. It gives

Re[S(u)/F(u)]=sum_{i<j}|x_i-x_j|.                              (C2)

In particular, if the pair sum exceeds n^2/sqrt(2), then g(u)>n^4/2 and (B4) produces a counterexample.

More generally the best ordering magnitude is exactly max_theta sum_{i<j}|Re(e^{-i theta}(z_i-z_j))|, by the rearrangement inequality. The single real projection in (C2) is sufficient for the asymptotic argument.

## D. Equidistributed rows force the required pair sum

Choose finite collections of unit rows v_1,...,v_m whose empirical projective measures tend weakly to uniform Haar measure on CP^1 as m tends to infinity along a sequence. For an explicit deterministic choice, take m=r^2 and rows v_{k,l}=(sqrt(p_k),sqrt(1-p_k) exp(2 pi i(l+1/2)/r)), where p_k=(k+1/2)/r and 0<=k,l<r. Since Haar measure has independent uniform p and relative phase, these empirical measures converge by ordinary Riemann sums. A sequence of dimensions is sufficient; a configuration for every integer m is unnecessary.

Let u_m be any projective global maximum of |F_m|, where F_m is their product. Choose a unitary variable change sending u_m to (1,0). The empirical projective measures of the transformed rows still tend weakly to Haar measure, even though this unitary depends on m. To see this, use compactness of U(2): every subsequence of the chosen unitaries has a convergent subsubsequence, and the limit pushforward of Haar measure is Haar measure. Equivalently, uniformity follows by a finite-net argument for the compact family of rotated continuous test functions.

The ratio z=b/a is continuous away from the single projective point a=0, which has Haar measure zero. Therefore the empirical distributions of x=Re(b/a) converge weakly to the real marginal of the complex Cauchy law

p_C(z)=1/[pi(1+|z|^2)^2].

Its real density and distribution function are

p_X(x)=1/[2(1+x^2)^{3/2}],
G(x)=(1+x/sqrt(1+x^2))/2.

If X,Y are independent with this law, then

E|X-Y|=2 integral_{-infinity}^{infinity} G(x)(1-G(x)) dx
      =(1/2) integral_{-infinity}^{infinity} dx/(1+x^2)
      =pi/2.                                                    (D1)

No convergence of unbounded moments is being assumed. For each T, apply weak convergence of product empirical measures to the bounded continuous function min(|x-y|,T), and then let T tend to infinity by monotone convergence. This gives

liminf_{m->infinity} m^{-2} sum_{i<j}|x_i-x_j| >= pi/4.           (D2)

## E. Make the peak unique without disturbing the limit

The original product can have several equal global maxima. To remove this issue, before making the unitary coordinate change append the additional unit linear factor

ell_{u_m}(z)=u_m* z.

Its coefficient row is conjugate(u_m), not u_m unless the chosen coordinates make it real. It has modulus at most 1 on the unit sphere, with equality only at the projective point u_m. Hence the new product

F_tilde=F_m ell_{u_m}

has a unique projective global maximum at u_m: at u_m it retains the original maximum modulus, while every other projective point has a strictly smaller product.

In the peak coordinates this new row is (1,0), so it appends x=0. It does not alter the limiting empirical distribution, and (D2) holds with n=m+1 for the augmented collection. Order these n rows by x as in Section C. Then

liminf_{n->infinity} |S(u_m)/F_tilde(u_m)|^2/n^4 >= pi^2/16 > 1/2. (E1)

Choose any fixed eta with 1/sqrt(2)<eta<pi/4. The liminf pair-score bound implies that every sufficiently late configuration in the chosen sequence has g(u)/n^4>eta^2>1/2. Select one such finite augmented and ordered base configuration and hold its n, F, S, and unique peak fixed. Only after making that choice, let L grow sufficiently large. No interchange of the two limits or estimate uniform in n is needed. Equation (B4) gives R_L>1, and (A3) gives P'_1(A_L)<0. By continuity there is a real q strictly between -1 and 1 with P'_q(A_L)<0.

## Conclusion

The argument above disproves the full Bapat q-permanent monotonicity conjecture already for rank-two Hermitian PSD matrices with positive diagonal, and by a small diagonal perturbation also for positive definite matrices. It is a non-explicit existence proof. The companion finite construction supplies an explicit order-200 Gaussian-integer Gram witness with a separately verified strict negative endpoint derivative. The construction supplies pi^2/8 as a strict lower asymptotic benchmark, not as a claimed universal exact limit. For each fixed base configuration the exact repetition limit is 2g(u)/n^4, which can be larger.

Every delicate step is isolated above: (A2) marks actual inversions; (A1) fixes conjugations; (B2) carries the factorial normalization; (B4) handles zeros; (D2) uses truncation rather than an unjustified moment limit; and Section E guarantees a unique peak with one explicitly described extra factor.
