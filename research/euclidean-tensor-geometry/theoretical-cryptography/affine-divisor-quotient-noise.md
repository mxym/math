# An exact noise barrier for affine divisor-quotient maps

This note tests a narrow but explicit model assumption: when can a same-ring divisor quotient keep exactly a prescribed wrapped Gaussian error after an affine transformation of the response coordinate? It characterizes the noise condition and gives a sharp optimum that holds even when the linear map and additive dither are randomized. It is **not** a lower bound for arbitrary modulus switching, a search reduction, or a statement about any deployed parameters.

We use the dual continuous sample format from [Lyubashevsky–Peikert–Regev, Definition 3.1](https://web.eecs.umich.edu/~cpeikert/pubs/ideal-lwe.pdf) and [Peikert–Regev–Stephens-Davidowitz, Definition 2.14](https://web.eecs.umich.edu/~cpeikert/pubs/rlwe-anyring.pdf). The latter's hardness theorem for any ring and modulus does not say that arbitrary affine projections preserve a specified noise law. [Langlois–Stehlé](https://perso.ens-lyon.fr/damien.stehle/MSIS.html) and [Brakerski et al., §3](https://arxiv.org/abs/1306.0281) prove broader, approximate modulus-switching statements with randomized rounding of the public coordinate and hypotheses on secret/noise. Those maps lie outside our pointwise affine model. [Gentry et al., Ring Switching in BGV-Style Homomorphic Encryption](https://web.eecs.umich.edu/~cpeikert/pubs/ring-switching.pdf) uses a separate mechanism for changing fields, also not analyzed here.

## Exact signal and noise conditions

Let R=Z[Y]/(Y^d+1), d a power of two, and L the codifferent. Since the derivative of the cyclotomic polynomial at Y is d times a unit, L=(1/d)R; use its coefficient basis to identify the response torus with (ℝ/Z)^d. All matrices below are in those lattice coordinates. Write C_c for the integer matrix of multiplication by a chosen ring lift of c.

The formal input has uniform a∈R/qR and response b=as/q+e mod L, for fixed s∈L/qL. The independent noise e is a centered real Gaussian N(0,Γ) reduced modulo L. Here Γ is positive definite in lattice coordinates. Choose integers 2≤p≤q and retain the public coordinate by the natural residue map to R/pR. Such a map is well-defined exactly when p divides q; hence assume q=mp. Fix in advance the desired transported secret c(s mod pL), for a unit c∈(R/pR)^×. We require affine maps to transport the signal **pointwise**, for every input residue a and s, before convolution with independent error. The map may depend on external randomness and on the public a only in the noise estimates below; every linear map allowed there must satisfy the stated congruence (so pointwise compatibility is required at all a for each allowed matrix). We are not asserting this restriction follows for a map that only matches the joint distribution averaged over discarded lifts of a.

For a fixed continuous linear torus map T (an integer matrix in the chosen basis) the exact signal condition is
```
T = m U,     U ≡ C_c mod p.
```
Indeed evaluation at a=1 for arbitrary s says T s/q−C_c s/p is integral, so T−m C_c≡0 mod q, which is precisely the displayed condition. Conversely applying this congruence to as proves all signal identities. Since c is a unit modulo p, U is invertible modulo p and has nonzero real determinant. Thus every allowed T on the torus is surjective. The public residue projection sends uniform a to uniform a mod p, and applying T to an independent uniform response preserves Haar probability, including after addition of independent dither. If choosing T and the dither conditionally on a, the same statement holds conditional on each a, provided they are independent of the original response noise or original independent Haar response respectively.

After the signal constraint, allow any additive torus-valued dither D independent of e (it need not be Gaussian). For fixed T, the output noise can be exactly the centered wrapped Gaussian of covariance Γ' if and only if
```
Γ' − T Γ Tᵀ is positive semidefinite.
```
A degenerate independent Gaussian dither with that difference as covariance suffices. For necessity let k run over the integer dual characters of the coordinate torus. Its output Fourier coefficient must satisfy
```
exp(−2π² kᵀΓ'k) = exp(−2π² kᵀTΓTᵀk) E[exp(2πi kᵀD)] .
```
If the quadratic difference is negative at some real vector, it is also negative at a rational vector by continuity and hence at an integer vector by clearing denominators. The required dither Fourier coefficient would have modulus larger than one, which is impossible. This proof does not assume Gaussianity of the dither or approximate equality of unwrapped densities. The covariance guarantee is for the wrapped law itself.

## Sharp spherical bound, including randomized maps

Let Γ=σ²I, Γ'=γ²I, σ>0. The power basis of a power-of-two cyclotomic is orthogonal up to a common factor in the full canonical metric, so both laws are also canonical spherical after this conversion of widths. For the standard target secret transport c=1, the exact optimal bound is γ≥mσ. More generally, with c fixed, let ℓ² be the sum of squares of the least-absolute representatives of its d coefficients modulo p (ties do not change ℓ²). Then every exact spherical target satisfies
```
γ ≥ m σ ℓ.
```
This remains necessary when (T,D) is arbitrarily jointly randomized, independent of e, with T ranging over allowed matrices. The rows of C_c consist of the same coefficients in different orders, with possible sign changes, since multiplication is negacyclic. Each row of U in its congruence class must therefore have squared norm at least ℓ². At a character k equal to a coordinate unit vector, the conditional Gaussian Fourier coefficient given T is at most exp(−2π² m²σ²ℓ²); adding dither and averaging cannot increase this modulus. A smaller γ would have strictly larger coefficient, a contradiction. In fact the TV distance to any proposed smaller spherical target is at least
```
[exp(−2π²γ²) − exp(−2π²m²σ²ℓ²)]/2
```
by testing a bounded character. This is a lower bound for the noise law; it is not a conclusion about distinguishability after hiding a signal, and it can itself be very small at wide error widths.

Equality at γ=mσℓ is fully characterized. At each coordinate character, attaining the modulus bound with the prescribed positive real phase forces the corresponding row squared norm to be minimal for almost every T and the dither phase in that coordinate to vanish almost surely. Thus D is zero on the torus. At a general integer k let X=exp(−2π²σ²‖Tᵀk‖²). Matching the target coefficients at k and 2k says E X⁴=(E X)⁴. Strict convexity forces X to be constant for each k. Testing coordinate vectors and pairwise sums forces U Uᵀ=ℓ²I for almost every allowed T. Conversely any matrix U with this property and the required congruence attains equality with zero dither. Thus randomization does not improve the equality case.

For odd p each least-absolute representative is unique; equality then holds exactly if C_ĉ C_ĉᵀ=ℓ²I, where ĉ is the coefficientwise centered lift. Equivalently multiplication by the centered lift has zero off-zero negacyclic autocorrelation. For c=1 this holds and U=I is the unique minimizing linear map for p>2. At p=2 and c=1 the minimizing linear maps are m times diagonal sign matrices (each diagonal entry of U may be either +1 or −1); randomizing among them has the same spherical law.

A useful strict test for nontrivial c at odd p is the following: every U different from C_ĉ has some row squared norm at least ℓ²+p. Indeed changing any centered integer entry x by a nonzero multiple of p increases its square by at least p²−2p|x|≥p. In the fixed-map class, the optimum depends on the operator norm of U; in particular if ‖C_ĉ‖²_op≤ℓ²+p, the centered lift is optimal, including a possible tie. The simpler randomized Fourier lower bound above does not in general compute the optimal constant beyond the equality case.

## Volume versus directional widths

For any fixed allowed U and positive definite Γ, exact target covariance satisfies det Γ'≥m^(2d) det Γ. In fact the Loewner criterion above gives det Γ'≥det(TΓTᵀ)=m^(2d)(det U)² det Γ, and det U is a nonzero integer. Equality requires |det U|=1 and zero covariance increase. This does not force equal widths in all directions: for c=1 the two-by-two shear U=[[1,p],[0,1]] satisfies the congruence and is unimodular; its Gram matrix minus I has determinant −p². With spherical source it makes one principal axis narrower and another wider, so the spherical optimum must not be rephrased as a common Loewner lower bound m²σ²I for every permitted output.

In integer-noise units this is also consistent with the identity-transport map b↦mb: defining the integer-scaled torus error as q times the original lift e, the corresponding target lift multiplied by p is pme=qe. The obstruction is to maintaining the same spherical width in the fixed *torus* unit, not a contradiction to holding the unwrapped integer-scaled noise fixed.

[Toy verifier](verify-affine-quotient-noise.js): exact arithmetic checks of signal compatibility on small negacyclic rings, row-norm minima, the shear, and centered lift examples `1+Y²` and `1+Y` in dimension four. No cryptographic instances, private data, attack routines, or implementations are used.
