# Exact additive factors of an unwrapped lattice Gaussian

Continuous covariance addition has no direct exact discrete analogue. For independent discrete noise, [Genise–Micciancio–Peikert–Walter](https://web.eecs.umich.edu/~cpeikert/pubs/gaussians.pdf) prove statistical convolution theorems with smoothing hypotheses, and the [LPR toolkit](https://web.eecs.umich.edu/~cpeikert/pubs/toolkit.pdf) uses such distribution-changing steps in lattice models. This note asks an exact, unwrapped question: when is a lattice-valued probability law a convolution factor of a full-support discrete Gaussian on the same lattice? We give a complete factor classification for arbitrary positive definite real quadratic forms, not just product Gaussians or Gaussian addends. The conclusion concerns addition of independent noise before any quotient; it does not restrict all randomized resampling, approximate transformations with parameters changing, or distributions after reduction modulo a lattice.

[Agostini–Améndola](https://arxiv.org/abs/1801.02373) develop the connection between multivariate discrete Gaussians and theta functions, including the relation of independence to block parameters. Here we use the zero **divisor** and its irreducibility on the universal covering space to settle additive factorization. This does not change any computational hardness claim.

## Classification

Fix an integral basis of the lattice, identifying it with Z^d. In these coordinates write D_{B,t} for the discrete Gaussian law proportional to exp(-xᵀ B x+tᵀx), with B real symmetric positive definite and t real. A one-dimensional factor has center t/(2B). Decompose the target precision B into integer-orthogonal blocks: use an integral unimodular basis change so that B is block diagonal and each block cannot be further orthogonally split by such a change. Then:

1. If independent lattice vectors X and V sum in law to D_{B,t}, both X and V have independent restrictions to these same blocks.
2. On each indecomposable block of dimension at least two, one summand must be deterministic and the other the target block shifted by the opposite lattice vector. In particular a higher-dimensional indecomposable target itself is convolution-indecomposable up to translation, even among arbitrary probability addends.
3. In each rank-one block, take the Jacobi product in §4, a countable sum of independent signed Bernoulli variables whose nonzero probabilities are summable. Partition the factors arbitrarily between the summands, and add a deterministic integer to one and its negative to the other. This describes all factorizations on that block and always gives a valid factorization.

Consequently if the source is itself D_{A,s}, it must split along the target blocks. Its higher-dimensional block precisions must equal the target's, and its centers there can only be translated by lattice vectors. For a one-dimensional block use source parameters (a,β) and target parameters (b,γ). The exact condition for existence of an independent additive correction is

    L=a/b is a positive integer,   L+(γ-β)/b is an odd integer.

In particular, for both centered, L must be an odd integer. These conditions are sufficient simultaneously: just take the independent blockwise corrections. No assumption is made that the arbitrary corrections are themselves discrete Gaussians.

### §1. Analytic preliminaries

For any lattice law P with Gaussian tails, let F_P(w)=E exp(wᵀX), regarded as an entire function of w∈C^d. Its restriction to each complex line through zero has order at most two, by completing the square in the Gaussian bound. The functions are 2πi-periodic in each coordinate and have F_P(0)=1. If X+V has lattice Gaussian law, the two summands automatically have Gaussian pointwise tails: choose any atom v0 of V with probability a0>0, so P_X(x)≤P_target(x+v0)/a0, and similarly for V. Thus F_target=F_X F_V holds as an entire identity. Orders and multiplicities in a zero divisor add under this product.

A useful cancellation lemma is the following. If F and G are normalized lattice-law transforms with Gaussian tails, with the same analytic zero divisor, then F/G=exp(kᵀw) for some k∈Z^d. The ratio is a globally holomorphic nonvanishing function (cancel local irreducible factors of the divisors). As C^d is simply connected it has a holomorphic logarithm H with H(0)=0. For each complex line w=z v, the restrictions of F and G have the same zeros with multiplicities and order ≤2. One-variable Hadamard factorization cancels their common canonical product and gives that H on this line is a polynomial of degree at most two. Hence the Taylor series of H has no homogeneous part above degree two. Periodicity makes each H(w+2πi e_j)-H(w) a constant in 2πi Z and forces the quadratic part to vanish. The linear part must then have integer coefficients. In particular a zero-free such probability transform is the transform of a single lattice atom.

We also need that any independent blocks of the sum are inherited by both summands. If F_target=prod_j F_j(w_j), its analytic divisor is a sum of cylinders over the divisors of the F_j. The divisor of F_X consists of a subcollection of these cylinders, with multiplicities bounded by the corresponding target multiplicities. For each j, restrict F_X to w_k=0 for k≠j; the resulting function is the marginal F_{X,j}. No cylinder from another block meets this slice, since every F_k(0)=1. Restricting a cylinder from block j gives exactly its underlying divisor with the same multiplicity (check on the smooth dense part and extend the divisor); local units remain nonzero everywhere. Thus F_X and prod_j F_{X,j} have the same divisor. The product is itself a lattice-law transform with Gaussian tails. The cancellation lemma makes their ratio a lattice monomial; on the block slices the ratio is 1 by construction, so that monomial is 1. The blocks are therefore independent. Apply the same proof to V.

### §2. Integer decompositions and principal theta divisors

Up to constant normalization the target transform is

    F_{B,t}(w) = sum_{x∈Z^d} exp(-xᵀ B x+(t+w)ᵀx).

For an integral vector n its shift by 2Bn multiplies it by exp(nᵀBn+(t+w)ᵀn); shifts by 2πi m are periods. These are the standard theta automorphy factors for the principal polarization of the complex torus

    T_B = C^d / ( 2B Z^d + 2πi Z^d ).

Equivalently the usual period matrix is iB/π, after dividing the coordinates by 2πi and using an equivalent sign for the real-period lattice. The tilt t translates the zero divisor and does not affect the polarization. The canonical alternating integral form pairs 2Bn and 2πi m by nᵀm up to the common convention for sign. We use two classical facts: a principal theta divisor is irreducible if and only if the polarized torus is indecomposable, and the product decomposition into indecomposable polarized subtori is unique as a collection of embedded factors. See [Debarre, *Polarisations sur les variétés abéliennes produits*](https://perso.imj-prg.fr/wp-content/uploads/debarre-pub/33.pdf) and [Debarre–Hacon](https://www.math.ens.psl.eu/~debarre/47.pdf). An irreducible principal theta divisor is reduced, since a multiplicity k>1 would force its principal self-intersection degree to be divisible by k^d.

Here the polarized product decomposition is exactly an integer-orthogonal decomposition of B. One direction is immediate from a block basis. For the other, complex conjugation preserves the period lattice and negates the alternating form. Thus it permutes the unique polarized factors (conjugating the complex structure and the sign of the form preserves positivity together). On the entire period lattice conjugation splits **integrally** into its + real and - imaginary parts. A pair of exchanged nontrivial factor lattices would violate this: on their direct sum the + and - sublattices are the diagonal and antidiagonal relative to the exchange, and their sum has index 2 to the power of the rank of one factor. Invariant orbits of factors give direct summands of the lattice, so such an index cannot be canceled elsewhere. Hence every factor is conjugation-stable and its own lattice splits integrally into the two eigenspaces.

Choose a basis of the imaginary periods from the stable factors, written as the columns of 2πi U with U∈GL_d(Z). Their dual real periods for the pairing are the columns of 2B U^(-T), and the real periods belonging to a factor are in the real span of that factor's imaginary basis divided by i. This is exactly that U^(-1) B U^(-T) is block diagonal. Integral coordinates of lattice vectors change by x=U^(-T)x', giving precisely the claimed precision congruence. Thus the rank and irreducibility of every block used in the classification is a statement about the given integral lattice, not an arbitrary real reparameterization.

### §3. The universal lift of an irreducible theta divisor

An irreducible principal theta divisor Θ on a complex abelian variety T of dimension d≥2 remains irreducible when lifted to C^d. Here is an argument that does not require Θ smooth.

Let Θ_reg be the connected smooth locus of the irreducible divisor. If the image of π₁(Θ_reg) in the torus lattice π₁(T)=Z^{2d} were a proper subgroup, its finitely generated quotient would have a cyclic prime-order quotient. Let f:T'→T be the associated connected torus cover of degree ℓ. This is an étale isogeny, and T' is also an abelian variety by pulling back the polarization. Above Θ_reg this cover is trivial. Thus the divisor f^*Θ consists of ℓ distinct reduced irreducible components, permuted transitively by the translations in the deck group. These are exactly the closures of the components over Θ_reg, since étaleness preserves dimension and the inverse image of the singular locus is smaller-dimensional. All ℓ components have the same numerical divisor class [D], since they are translates. Numerical intersection and Riemann–Roch on the abelian variety give

    ℓ = (f^*Θ)^d/d! = ℓ^d · (D^d/d!),      D^d/d! is an integer.

This is impossible for d≥2. Therefore the smooth locus surjects onto the torus lattice and its inverse image in the universal cover is connected. That inverse image is a smooth connected complex hypersurface, hence irreducible. Its closure is the full lifted divisor; the preimage of the singular locus cannot supply any component. This proves the lifting assertion.

In an indecomposable block of dimension at least two, the transform divisor of the target is therefore one reduced irreducible hypersurface on C^d. Since the independent factors' divisors add, one factor must have no zeros. The cancellation lemma makes it a mere shift. This proves the rigidity there without assuming either factor Gaussian.

### §4. One-dimensional blocks and positivity

For the scalar precision b and tilt γ, the [Jacobi triple product](https://dlmf.nist.gov/20.5) gives

    F_{b,γ}(w) = prod_{r≥1}
         (1+exp(γ-b(2r-1)) exp(w))/(1+exp(γ-b(2r-1)))
       · (1+exp(-γ-b(2r-1)) exp(-w))/(1+exp(-γ-b(2r-1))).

Each factor is a normalized transform of a variable supported on {0,1} or {0,-1}. Nonzero probabilities have a summable bound, so any subproduct defines the law of an almost surely finite signed sum. The products converge locally uniformly, and each factor has a distinct simple zero class modulo 2πi Z. The complete list of zeros in log coordinates is

    b(2j+1)-γ + (2k+1)π i,     j,k∈Z.

A factor's divisor must choose a subset of these zero classes, because the factor itself is 2πi-periodic. Choose the corresponding Jacobi-subproduct probability law. It has those same zeros with multiplicity, and Gaussian tails follow from its being a genuine convolution factor with the complementary product. By the cancellation lemma the original factor differs from this law only by an integer shift. The two shifts in the complementary pair must cancel. Thus all possible choices give positive probability laws, not just formal deconvolutions.

For scalar Gaussian source D_{a,β}, inclusion of its zeros in the target set requires the spacing relation a/b=L∈Z_{>0}, and matching the zero at a-β requires L+(γ-β)/b odd. Conversely these two relations match every source zero to a target zero. The corresponding target subproduct has Gaussian tails, and the source is its integer translate by cancellation. Hence existence follows, with the independent correction the translated complementary Bernoulli sum. This proves the stated criterion.

## Cyclotomic example

For an odd prime p, the usual unscaled canonical integer lattice of Q(ζ_{p^a}) is a scalar multiple of an orthogonal sum of p^{a-1} copies of A*_{p-1}; its Euclidean dual uses A_{p-1}. This follows by splitting the Gram of the power basis into blocks of powers ζ_{p^a}^j ζ_p^k, or from the [powerful-basis Gram calculation in the toolkit](https://web.eecs.umich.edu/~cpeikert/pubs/toolkit.pdf). Both root lattices are integrally orthogonally indecomposable. For A* the shortest projected unit vectors span and have pairwise nonzero inner products up to sign. For A the shortest differences e_i-e_j span and their nonorthogonality graph is connected. In an orthogonal lattice decomposition a shortest vector has to lie in one factor, so these spanning and connectivity facts exclude any nontrivial split.

Thus different centered spherical widths on either the ring lattice or the codifferent of an odd prime-power cyclotomic cannot be matched exactly by an arbitrary independent lattice-valued additive correction. In the dyadic case the canonical lattice instead splits into orthogonal rank-one factors, so the exact centered conversion exists precisely when the ratio of target to source Gaussian **width-squares** is an odd positive integer. The statements do not concern the actual covariance ratio (which need not equal the width parameter ratio for a discrete Gaussian), or an error law after quotienting.

## Statistical boundary

For any fixed source and target lattice probability laws, the set of probability laws obtainable by convolution of the source with any probability law is closed under total variation. Indeed if P*ν_j→Q, choose an atom x of P of mass a>0. For every finite K, a ν_j((K-x)^c)≤(P*ν_j)(K^c); the right-hand laws are uniformly tight, so the ν_j are tight. On a countable lattice this gives a subsequence converging in total variation, and convolution is a contraction. Thus non-feasible fixed Gaussian parameters have a strictly positive best approximation error within the independent-addition class. This is not a uniform quantitative gap for varying precisions, and is consistent with the standard smoothing-based approximation lemmas.

For two Gaussian laws P and Q one can also give a finite positive lower-bound certificate if independent addition is impossible. All their theta divisors are reduced: decompose their principal polarizations into indecomposable factors, and use reducedness on each. The necessity proof for block factorization uses only inclusion of divisors of P in Q, and each block's argument above then produces the positive correction. Therefore failure of exact conversion implies there is a complex w with F_P(w)=0 but F_Q(w)≠0. Let b=||Re w||, a=P(0)>0, and write W_S(r)=sum_{||x||>r} S(x) exp(b||x||). For every radius r and every independent additive law ν we have

    (2+1/a) d_TV(P*ν,Q) ≥ exp(-2br)|F_Q(w)| -
        Q(||Y||>r)/a - exp(-2br)W_Q(2r) - exp(-br)W_P(r).

To see this, truncate ν to ||v||≤r without renormalizing. The discarded mass is at most [Q(||Y||>r)+d_TV(P*ν,Q)]/a by using the atom at zero in P. The truncated convolution has transform zero at w. On ||y||≤2r, the weighted comparison costs at most exp(2br) times twice TV plus the discarded mass. Outside, the target costs W_Q(2r). In the truncated convolution, ||x+v||>2r implies ||x||>r, costing at most exp(br)W_P(r). This proves the bound; for sufficiently large finite r its right side is positive by Gaussian tails. This certificate is about fixed parameters, and may become very small as parameters change.

The adjacent toy checker verifies arithmetic zero-spacing and factor orientation identities, stylized block-coordinate transformations, and finite theta-series evaluations (150,463 exact checks and 1,080 floating comparisons). It does not attempt to verify the global analytic statements by finite sampling.
