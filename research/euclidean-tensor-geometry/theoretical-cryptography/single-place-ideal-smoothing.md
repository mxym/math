# Single-place smoothing on ideal tori: critical phase and arithmetic recurrence

**Scope.** [Peikert–Regev–Stephens-Davidowitz (PRS), Lemma 6.9](https://web.eecs.umich.edu/~cpeikert/pubs/rlwe-anyring.pdf) gives a uniform product-of-widths sufficient smoothing bound for an ideal lattice. Their §6.1 uses it when broadening only one real embedding or one conjugate complex pair. In a fixed field, we identify the exact transition scale of this path for wrapped noise, including the absence of a single critical error profile in general. This concerns standalone canonical Gaussian noise on an ideal torus, not the success probability of a solver, an alteration of PRS's hardness theorem, or a concrete scheme. The compact log-unit torus is standard; see [McMullen, §3](https://people.math.harvard.edu/~ctm/papers/home/text/papers/mink/mink.pdf) for the diagonal-orbit viewpoint. The focus here is its effect on the one-place smoothing path, together with an effective recurrence bound in unit rank two.

## 1. Width product and phase

Let K be a fixed number field of degree n, with archimedean places v of real dimension d_v in {1,2}. Use the canonical real Euclidean space, with each complex place counted twice in the squared norm. Let L be the canonical lattice of a fixed nonzero fractional ideal I. Let U be probability Haar on the additive torus K_R/L. Define the centered spherical-at-each-place continuous Gaussian with widths r_v: in orthonormal real coordinates in place v its covariance is r_v^2/(2 pi) times the identity. Write P_r for its reduction modulo L.

Put

    H = {s: sum_v d_v s_v=0},
    Lambda = { (log |sigma_v(u)|)_v : u in O_K^times },
    T = H/Lambda.

By the unit theorem T is compact. For common geometric mean g>0 and shape s in H, let

    V_g(s) = TV(P_(g exp(s)), U).                            (1)

It is a continuous function on T. Indeed, a unit multiplies the fraction ideal bijectively, induces a Haar-preserving automorphism of the torus, and shifts s by its log vector: its signs and complex rotations do not affect isotropic place blocks. Also a small change in shape changes the Gaussian in TV by O(||s-s'||), uniformly in g, by the closed formula for Gaussian KL and Pinsker. For example, KL in one direction is

    (1/2) sum_v d_v (exp(2(s_v-s'_v))-1-2(s_v-s'_v)).

This gives a global Lipschitz bound on the unit quotient for its flat metric. The same reasoning gives continuity in log g, uniformly in s.

Now fix positive relative widths w_v, and broaden a single place i by exp(t):

    r_v= b(t) w_v exp(t 1_(v=i)).
    omega=(prod_v w_v^(d_v))^(1/n),
    g(t)=b(t) omega exp(d_i t/n),
    s_0=(log(w_v/omega))_v,
    v_i=e_i-(d_i/n) 1.

Then the exact comparison is

    TV(P_r,U)=V_(g(t))(s_0 + t v_i).                         (2)

The logarithmically growing direction v_i lies in H, with the same factor d_i/n for the two real coordinates of a complex place. This formula remains asymptotically valid if only the broadened width is replaced by b(t) w_i sqrt(exp(2t)+B) with fixed B>=0, because the log-width change is O(exp(-2t)). That includes the shape of a broadened width plus a fixed Gaussian variance floor, for positive leading scale.

## 2. Exact critical scale, with an interval of limits

Let T_i be the closure in T of the continuous one-parameter subgroup t v_i. It is a connected subtorus (a point in unit rank zero). As t tends to infinity:

1. If g(t) tends to infinity, the distance in (2) tends to zero uniformly over all shapes. If g(t) tends to zero, it tends to one uniformly over all shapes.
2. If g(t) tends to g_0 in (0,infinity), the set of subsequential limits is exactly the closed interval

       [ min_(s in s_0+T_i) V_(g_0)(s),
         max_(s in s_0+T_i) V_(g_0)(s) ].                   (3)

   Both endpoints lie strictly between zero and one. Moreover, the limiting continuous-time empirical distribution is the pushforward of probability Haar on s_0+T_i by V_(g_0).
3. If T_i=T and the unit rank is nonzero, interval (3) is nondegenerate for every sufficiently large fixed g_0. In particular the error does not converge to any shape-independent profile at those critical offsets.

Thus the transition for a small baseline b is at t=(n/d_i) log(1/b)+O(1) (with fixed w_v), but the critical logarithmic offset alone does not determine the limiting error. This is a fixed-field result; no bound is claimed uniform over growing degrees or changing ideals.

**Proof of 1 and 2.** For u in the Euclidean dual lattice L*, the Fourier coefficient of the wrapped Gaussian at u is exp(-pi g^2 E_s(u)), where E_s(u) is the sum over places of exp(2s_v) times the squared orthonormal-coordinate length of u in that place. Take a compact set of representatives for T. Uniform comparability to the ordinary Euclidean length bounds the absolute sum of the nontrivial Fourier modes by a quantity tending to zero as g tends to infinity. For small g, uniformly on the same representatives the unwrapped Gaussian puts probability tending to one in a ball of radius sqrt(g); its image has Haar mass tending to zero. This proves 1. For fixed g>0, all the nontrivial Fourier coefficients are positive, so V_g>0. The wrapped Gaussian density is positive everywhere, giving V_g<1; compactness turns these into strict bounds over T.

For every torus character, the continuous-time mean along the linear trajectory vanishes in the limit unless the character is identically one on T_i, as seen by integrating exp(i a t). Trigonometric approximation yields Haar time averages on the orbit closure, for all starting phases. In particular every neighborhood of every point in the closure is visited at arbitrarily late times. Joint continuity in s and log g now gives the limit set and empirical law, and connectedness makes the image an interval.

**Proof of 3.** For any shape define

    ell(s)=min_(0 != u in L*) E_s(u).

Fourier comparison yields the following uniform first exponent on the entire unit torus:

    -log V_g(s)/(pi g^2) -> ell(s)    as g -> infinity.       (4)

The lower bound V_g(s)>=(1/2)exp(-pi g^2 ell(s)) uses one Fourier test of supremum norm one. For the upper bound, factor exp(-pi(g^2-1)ell(s)) out of the sum of squared-width Fourier terms and use the uniform absolute summability at g=1 on compact representatives. This gives (4).

The Euclidean dual differs from the trace-dual ideal J by coordinatewise conjugation, which does not affect E_s. For nonzero x in J,

    E_s(x) = sum_v d_v exp(2s_v)|sigma_v(x)|^2
         >= n |N_(K/Q)(x)|^(2/n)

by weighted arithmetic–geometric mean. The algebraic norms of nonzero x in a fixed fractional ideal have a positive attained minimum N_0: after clearing one denominator their positive absolute norms lie in a discrete subset of the positive integers. Equality for a minimizing x happens at the unique balanced shape s_v=(log N_0)/n-log |sigma_v(x)|. On a compact fundamental representative set there are only finitely many such balancing shapes, because at equality the length of x is bounded uniformly. Hence ell(s) achieves n N_0^(2/n) at finitely many shapes modulo units, and is strictly larger elsewhere if the torus has positive dimension. Since T_i=T, the uniform exponent (4) proves 3.

## 3. When a single place winds densely in unit rank two

Suppose K has exactly three archimedean places, so dim H=2. Let j,k be the two places other than i. Then its one-place flow is either periodic or dense in the whole T, with the exact criterion

    periodic iff there is a nontorsion unit u with
                       |sigma_j(u)|=|sigma_k(u)|.           (5)

Indeed, the kernel of s_j-s_k in H is the line spanned by v_i. A nonzero continuous line on a two-torus has proper closed subgroup closure exactly when it contains a nonzero lattice vector. The following cases resolve (5) in terms of the field or of the singled place.

- Every direction is dense in each totally real cubic field and in each quintic field with one real and two complex places.
- In a quartic field with two real and one complex place, the flow for either real place is dense. The complex-place flow is periodic exactly when there is a real quadratic subfield.
- In a CM sextic field (a totally imaginary quadratic extension of a totally real cubic field), all three flows are dense.

For the prime-degree claim, any nontorsion unit in a prime-degree field generates that field, since a rational unit is +1 or -1. Equality between moduli at distinct places gives a nonzero integer monomial relation of total exponent zero on its distinct conjugates: at a real place use the square and at a complex place use the product of the conjugate pair. The Galois group of the splitting field acts transitively in prime degree p, hence contains a p-cycle (its order is divisible by p). The rational span of cyclic shifts of any nonzero zero-sum vector on p indices is the entire zero-sum subspace, by irreducibility of the p-th cyclotomic polynomial. Applying the p-cycle powers to the monomial relation and taking absolute logarithms forces all conjugate moduli equal. Their norm is one in absolute value, so all are one, contrary to nontorsion.

In the mixed quartic, when singling out the complex place, equality at both real embeddings forces u^2 to lie in a proper subfield (those embeddings agree on u^2), necessarily a real quadratic if u is nontorsion. Conversely, of the two real embeddings of a real quadratic subfield, one has two real extensions to K and the other has a complex pair. Its nontorsion units have equal values at the two real places of K. For a singled real place, write a,b,c,d for the four conjugates of a generating unit, with a,b real and d the complex conjugate of c, and equality of the remaining moduli giving b^2=cd. Then its norm gives a=+b^(-3) or -b^(-3). A splitting-field automorphism g sends b to a. Iterating a relation g(b)=+b^(-3) or -b^(-3) until g has finite order forces b to be a root of unity. If a unit does not generate K, it lies in a real quadratic subfield (an imaginary quadratic subfield cannot embed in this real-embeddable K) or is rational. For real quadratic nontorsion units the two distinct real modulus values are reciprocal but unequal, and the two real places of K and the complex place lie over different values as above. This excludes equality also for non-generators.

For a CM sextic, u times its CM conjugate is a totally positive unit in the real cubic subfield. Its images are the squares of the three original moduli. Equality at two places would make this unit rational, and hence one, by the prime degree of the subfield. Again the original unit would be torsion.

## 4. Effective rank-two recurrence

In any of the dense rank-two cases, time averaging a Lipschitz function on the entire T has a power-saving rate, uniform in starting phase. Namely for a field and chosen place there are constants C,B>0 such that for every Lipschitz F:T -> R and R>=2,

    | (1/R) int_0^R F(s_0+t v_i) dt - int_T F |
       <= C (||F||_infty + Lip(F)) R^(-1/(B+3)).            (6)

In particular, it holds for F=phi o V_g for any Lipschitz real function phi on [0,1], with constants uniform in every fixed g>0. This is a rate for continuous time and a fixed field. Its constants need not be small.

To prove (6), take log-unit generators l_1,l_2 and use them as a coordinate basis so T=R^2/Z^2. Put A_h=(l_h)_j-(l_h)_k. The two numbers are logs of positive algebraic numbers. The velocity of the line v_i in these coordinates is a nonzero scalar multiple of (A_2,-A_1). By density no nonzero integer covector m annihilates it. The lower bound for nonzero linear forms in logarithms [Matveev](https://doi.org/10.1070/IM2000v064n06ABEH000314) gives |m_1 A_2-m_2 A_1|>=c(1+||m||)^(-B), for some B and c>0 depending on the fixed units. Consequently the time average of the nonconstant character indexed by m is bounded by C(1+||m||)^B/R. Convolve F first with a wrapped Gaussian of coordinate standard deviation h. The uniform error is at most C h Lip(F), and the Fourier coefficients of the smoothed function are bounded by ||F||_infty exp(-c' h^2 ||m||^2). Summing the character estimates gives C ||F||_infty h^(-B-2)/R. Set h=R^(-1/(B+3)), proving (6).

For example, the logarithms in K=Q(2^(1/4)) at the two real places have equal absolute value on the quadratic-subfield unit 1+sqrt(2). Its logarithm vector is (a,a,-a) with a=log(1+sqrt(2)), giving a nonzero period for the complex-place flow. For a totally real cubic the same type of direction never has a period; it instead obeys (6) and explores the whole critical interval. For a concrete strict comparison, take any totally real cubic and an ideal whose trace dual is O_K. At shape (0,0,0) the first exponent ell is 3 by the unit 1. At widths proportional to (2,1,1/2) it is strictly larger than 3: equality would require the second embedding of an algebraic integer to be +1 or -1, forcing that integer to be +1 or -1 in all embeddings, incompatible with balancing. Both shapes are approached by the same one-place flow, so for large fixed g their differing errors are genuinely in one trajectory's limit set.

## Reproduction

    node verify-single-place-ideal-smoothing.js

The verifier tests weighted width identities, exact prime-cyclic rational-span examples, example field unit identities, and the character time-average estimate on toy logarithmic tori. The field classification and uniform limits follow from the analytic argument, not from parsing approximate unit logarithms.
