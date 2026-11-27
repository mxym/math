# Theoretical cryptography research notes

These are two complementary strands of finite algebra and probability, with proofs and exact small examples. None supplies a polynomial-time factoring, discrete-logarithm, Ring-LWE or SIS solver. The elliptic curves below are algebraic geometry objects, not a claim about elliptic-curve discrete logarithms. The random-module results use independent uniformly distributed ring rows and a specified sparse limit; they are not results about recovering a secret in a noisy cryptosystem.

## Finite-field elliptic geometry

- [Fixed double-cover incidence](FixedDoubleCoverIncidence.md): a fixed pair of degree-two maps realizes the complete quartic Riemann–Roch system, and each irreducible cubic picks out one projective section.
- [Residual fibers and pencils](EllipticResidualPencils.md): exact cubic-fiber counts over rational residual points; simply branched pencils have an asymptotic one-third density, but some other pencils have no cubic fibers at all.
- [Monodromy beyond simple branching](EllipticQuarticMonodromy.md): classifies when cubic fibers can occur and gives exact resolvent-based counts and explicit examples.
- Exact small example: `node verify-elliptic-residual-pencil-toy.js`. Success is silent.

## Random finite modules

- [Scalar precursor](finite-module-scalar-energy.md): projective second moment and integer energy counting.
- [Sparse signed-monomial shell](finite-module-sparse-poisson.md): factorial moment bound and Poisson limit.
- [Unrestricted coefficient critical window](finite-module-unrestricted-critical-window.md): inactive residue-field components require a weighted bound; they cannot be treated as fully active samples.
- [The modulus-square crossover](finite-module-q-square-crossover.md): in the stated sparse regime, the random two-point minimum law is clipped by the deterministic energy floor (q^2); includes the exact universal ideal calculation.
- [Arbitrary odd prime moduli](finite-module-nonuniversal-all-moduli.md): remove deterministic universal relations and the same sparse probability law holds, including for fixed moduli.
- Small, generated examples: run each `verify-finite-module-*.js` here with Node.js. The examples check finite identities, not the asymptotic theorems by experiment.
