# A one-surplus-column Gaussian module generation bound in prime-power cyclotomics

**Scope.** This is a probability bound for generating a free module from independent prescribed Gaussian ring entries. The motivation is the surjectivity requirement in §3 of [Albrecht–Felderhoff–Lai–Lapiha–Woo, A Gaussian Leftover Hash Lemma for Modules over Number Fields](https://perso.jfelderhoff.fr/work/papers/AFLLW25.pdf), referred to below as AFLLW. Their Corollary 3.9 covers general full-rank modules and more general distributions, assuming GRH and using a column count starting at twice the module rank. We treat the narrower case of the standard free module with independent spherical entries, remove GRH, and identify the leading probability even with one surplus column. This only establishes the generation ingredient, not the subsequent kernel-smoothing hypotheses or any cryptosystem claim.

Related earlier generation results include [Micheli–Weger](https://arxiv.org/abs/1803.08785) for densities of rectangular matrices over algebraic integers, and [Stehle–Steinfeld, Lemma 4.4](https://doi.org/10.1007/978-3-642-20465-4_4) for two Gaussian generators of an ideal in a dyadic cyclotomic setting. The statement here is a uniform growing-degree, near-square result for all polynomially growing free module ranks, not a new local characterization of surjectivity or a new lattice sampler.

## 1. Model and bounds

Let L be the ring of integers of K=Q(zeta_f), with f=p_0^a a prime power and degree n=phi(f) tending to infinity. Use the canonical Euclidean norm with conjugate complex places counted twice in the squared norm. Let g=|Delta_K|^(1/n) and D_(L,s) be the centered discrete Gaussian with mass proportional to exp(-pi ||x||^2/s^2). Let X have size r by r+u, with all entries independent D_(L,s), and let Gen mean that its columns generate L^r as an L-module. This is stronger than spanning over K.

For fixed C>1 and D>0, suppose s>=C g, r>=1, u>=1, and r+u<=n^D. Then uniformly in these choices,

    Pr(Gen) = product_(j=u+1 to u+r) (1-p_0^(-j))
                   + O(n f^(-u-1) + poly(n) exp(-c n)),      (1)

where c>0 depends only on C and the polynomial bounds are for fixed D. In the dyadic tower f=2n and g=n, so the main term is precisely the probability that a uniform r by r+u matrix over F_2 has full row rank. The error is O(n^(-u)+poly(n) exp(-c n)). In particular the difference in probability between generation over L and generation after reduction at the unique ramified prime is small despite the infinitely many other ideals. If u is fixed and r grows in the dyadic case, the limit is product_(j>=u+1)(1-2^(-j)), strictly positive and strictly less than one.

A finite version of the argument is useful. Write

    epsilon=exp(-n),   H=(s/g)^n,   beta=(1+epsilon)/H,
    B_j = j log(s sqrt(jn))/log(s/g).

If s>g and H>=p_0, the absolute error in (1) is bounded by

    2 r(r+u) epsilon
      + 2 (1+epsilon)^(r+u) n f^(-u-1) zeta(u+1)
      + sum_(j=1 to r) [j^2 exp(-n) + H^(-1) + beta B_j].    (2)

No numerical parameters for any application are intended.

## 2. Capped Gaussian atoms and the small primes

For every nonzero integral ideal P in L, its covolume in the canonical space is N(P) sqrt(|Delta_K|). Its Euclidean dual is isometric, by coordinate conjugation, to its trace-dual ideal, of norm 1/(N(P)|Delta_K|). Multiplication by any element of an ideal gives a contained principal ideal; comparison of norms and arithmetic–geometric mean over the embeddings therefore give

    lambda_1(P*) >= sqrt(n)/(g N(P)^(1/n)).

By the Banaszczyk bound in [Peikert–Regev–Stephens-Davidowitz, Lemma 2.6](https://web.eecs.umich.edu/~cpeikert/pubs/rlwe-anyring.pdf), the dual Gaussian tail at width s_0=g N(P)^(1/n) is at most epsilon. If s>=s_0, Poisson summation bounds the Gaussian mass of every coset P+x between (1-epsilon)s^n/det(P) and (1+epsilon)s^n/det(P). The denominator rho_s(L) is at least s^n/det(L). If s<s_0, the centered coset has maximal mass, and it increases with width, so

    rho_s(P+x) <= rho_(s_0)(P)
                 <= (1+epsilon) g^n/det(L).

Thus for a single entry Y the maximum point probability modulo P obeys the capped bound

    max_x Pr(Y mod P=x) <= (1+epsilon) max(N(P)^(-1), H^(-1)).      (3)

This resembles the capped atom bound of AFLLW Lemma 3.3; the short derivation above is for the present centered model. Also the maximum *exact* point probability of Y in L is at most det(L)/s^n=(sqrt(g)/s)^n <= H^(-1), since g>=1.

For a prime ideal P of norm Q<=H, every nonzero left row over the residue field defines a linear relation among entries of a column. Condition on all but one coordinate with a nonzero coefficient: by independence its probability is at most (1+epsilon)/Q. Projective left rows suffice, so with r+u independent columns the rank-deficiency probability is at most

    (Q^r-1)/(Q-1) * ((1+epsilon)/Q)^(r+u)
       <= 2 (1+epsilon)^(r+u) Q^(-u-1).                    (4)

There is a unique ramified prime P_0, above p_0, with residue field F_(p_0). All other prime-ideal norms Q are 1 modulo f: for a rational prime different from p_0, the residue degree is the order of its class modulo f. At most n such prime ideals have any one norm, because a norm is a prime power and determines the underlying rational prime, over which there are at most n ideals. Consequently no prime distribution theorem is needed for the union bound:

    sum_(P!=P_0) N(P)^(-u-1)
       <= n sum_(h>=1) (1+f h)^(-u-1)
       <= n f^(-u-1) zeta(u+1).                            (5)

This gives the middle term in (2) for the small unramified primes. At P_0, H>=p_0 ensures that the coset Poisson bounds apply. The distribution of each residue differs from uniform in TV by at most 2 epsilon, allowing for the Gaussian normalizer (which itself is within relative epsilon of its Poisson main term since L* is contained in P_0*). Tensorization and data processing give a total error of at most the first term in (2) for the ramified rank probability. The uniform full-rank probability is the finite-field count obtained by requiring row j to escape the span of its predecessor rows.

## 3. Large primes: one new coordinate at a time

Consider only the leading r+1 columns; the remaining u-1 cannot decrease any rank. Let E_j mean that the first j rows of the first j+1 columns are surjective over the residue fields of *every* prime ideal with norm greater than H, with E_0 certain. We bound transitions by exposing a fresh bottom coordinate rather than retaining a large block of extra columns.

On E_(j-1), the first j-1 rows of the first j columns have full row rank at each such prime, and hence rank j-1 over K (rank could not increase from K under reduction). Condition on these top rows. To bound the chance of a zero determinant of the leading j by j matrix A_j, expose all but one bottom entry with nonzero cofactor. The remaining entry has at most one exact field value that makes the determinant zero, of probability at most H^(-1) by the exact point bound. The probability of a long entry among the j^2 entries of A_j is at most j^2 exp(-n): for D_(L,s),

    Pr(||Y||>s sqrt(n))
       <= exp(-pi n/2) rho_(sqrt(2)s)(L)/rho_s(L)
       <= (sqrt(2) exp(-pi/2))^n <= exp(-n),

where the second inequality follows from Poisson summation and monotonicity of the dual Gaussian mass as the primal width grows. These bad events are charged before conditioning on the actual old square; the fresh bottom coordinate is not involved in them.

Now fix the old square A_j when its determinant is nonzero and its entries have norm at most s sqrt(n). In each embedding, Hadamard's inequality bounds the absolute determinant by (s sqrt(jn))^j, so

    |N_(K/Q)(det A_j)| <= (s sqrt(jn))^(jn).

The only candidate large primes are those dividing det A_j. The number of distinct ones of norm greater than H is at most B_j: their product divides the principal ideal of the determinant, and each norm exceeds H. This is just a cardinality bound; no procedure for identifying these primes is needed.

At each candidate prime, rank A_j=j-1 because the top rows are already independent. A nonzero left null vector has nonzero bottom coordinate: otherwise it would give a relation among the top rows. Condition additionally on the top j-1 coordinates of column j+1. The bottom entry of that column is fresh, and failure to increase rank imposes exactly one residue on it. Formula (3) bounds its probability by beta. A union bound over the candidates now gives

    Pr(E_j^c) <= Pr(E_(j-1)^c) + H^(-1)
                    + j^2 exp(-n) + beta B_j.

This bound did not require independence of the reductions at different primes. Summing it over j proves the final term in (2). Under the asymptotic hypotheses, B_j is O(j log(nr)) uniformly in s>=C g: write log s=log(s/g)+log g, use log(s/g)>=log C and g<=f<=2n. Thus the total large-prime error is polynomial times exp(-c n).

Finally, a morphism between these finite free L-modules is surjective if and only if it is surjective after reduction at every maximal ideal. Indeed a nonzero finitely generated cokernel has a nonzero localization at a maximal ideal in its support, and Nakayama then detects it after reduction. Therefore the actual generation probability is at most the ramified full-rank probability and at least that probability minus the two unramified error terms. This completes both (1) and (2).

## Reproduction

    node verify-cyclotomic-gaussian-module-generation.js

This verifies finite-field rank products, the one-coordinate repair property on generated finite fields, and the elementary prime-power residue-norm and sum bounds. It does not sample or test any real scheme or manipulate unknown factorization inputs.
