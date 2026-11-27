# Theoretical cryptography research notes

These are two complementary strands of finite algebra and probability, with proofs and exact small examples. None supplies a polynomial-time factoring, discrete-logarithm, Ring-LWE or SIS solver. The elliptic curves below are algebraic geometry objects, not a claim about elliptic-curve discrete logarithms. The random-module results use independent uniformly distributed ring rows and a specified sparse limit; they are not results about recovering a secret in a noisy cryptosystem.

## Defensive competition security reviews

- [NIST fourth-round KEM proof scope](PublicPQCCompetitionSecurityScopeAudit.md): historical BIKE correctness threshold, later HQC analysis, and version-specific limits. This audits published results; it is not a new attack.

## Integer factorization theory

- [Low-degree CRT observation bounds](FactorCRTPolynomialObservationBounds.md): sharp transcript bounds in a restricted polynomial-query model, not a lower bound for ordinary factoring.

## Earlier finite-field elliptic geometry

- [Fixed double-cover incidence](FixedDoubleCoverIncidence.md): a fixed pair of degree-two maps realizes the complete quartic Riemann–Roch system, and each irreducible cubic picks out one projective section.
- [Residual fibers and pencils](EllipticResidualPencils.md): exact cubic-fiber counts over rational residual points; simply branched pencils have an asymptotic one-third density, but some other pencils have no cubic fibers at all.
- [Monodromy beyond simple branching](EllipticQuarticMonodromy.md): classifies when cubic fibers can occur and gives exact resolvent-based counts and explicit examples.
- [Tame tetrahedral quartics above a fixed cubic quotient](EllipticQuarticTameCubicQuotient.md): geometric counts 3, 4, and 5; finite-field descent and an elliptic halving test.
- Exact small example: `node verify-elliptic-residual-pencil-toy.js`. Success is silent.

## Ring-LWE noise and random finite modules

- [Information loss in sparse signed-monomial folds](folded-error-information-limit.md): exact Fourier damping and a statistical bound for observing the entire sparse folded transcript, not the full noisy input.

- [Scalar precursor](finite-module-scalar-energy.md): projective second moment and integer energy counting.
- [Sparse signed-monomial shell](finite-module-sparse-poisson.md): factorial moment bound and Poisson limit.
- [Unrestricted coefficient critical window](finite-module-unrestricted-critical-window.md): inactive residue-field components require a weighted bound; they cannot be treated as fully active samples.
- [The modulus-square crossover](finite-module-q-square-crossover.md): in the stated sparse regime, the random two-point minimum law is clipped by the deterministic energy floor (q^2); includes the exact universal ideal calculation.
- [Arbitrary odd prime moduli](finite-module-nonuniversal-all-moduli.md): remove deterministic universal relations and the same sparse probability law holds, including for fixed moduli.
- [All odd moduli](finite-module-nonuniversal-odd-moduli.md): the same law for prime powers and odd composite moduli, via a common block decomposition and local valuation bounds.
- Small, generated examples: run each `verify-finite-module-*.js` here with Node.js. The examples check finite identities, not the asymptotic theorems by experiment.
