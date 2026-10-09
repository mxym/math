# Complete quantum semantics: proof plan (not yet formalized)

The polynomial certificate is not by itself a complete APPT theorem. Avoid importing the Hildebrand criterion as an unproved Lean axiom or defining APPT to mean its conclusion.

A potentially shorter route proves only the necessary matrices A,B and the two attaining orbits, rather than the full criterion for every spectrum.

## Necessary matrices by explicit conjugations
For a sorted spectrum lambda in dimension D=3n, rotate the 3x3 corner product basis into the three diagonal vectors |ii> and the symmetric/antisymmetric pairs (|ij> +/- |ji>)/sqrt(2). Assign eigenvalues:
- diagonal |00>,|11>,|22>: lambda_D, lambda_(D-2), lambda_(D-5)
- symmetric 01,02,12: lambda_(D-1),lambda_(D-3),lambda_(D-4)
- antisymmetric 01,02,12: lambda_1,lambda_2,lambda_3.
Assign all remaining eigenvalues bijectively to the remaining product basis vectors. These vectors form an orthonormal eigenbasis. The partial-transpose quadratic form on sum_i v_i |ii> is v^T A v / 2, for every real v. Hence APPT implies A PSD. For B, exchange the eigenvalue assignments to diagonal |11> and symmetric 02. This is a necessary implication with an explicit unitary witness; no Schmidt ordering cases needed.

## Attainment requires full orbit positivity
The (3,1,...,1)/(D+2) orbit is (I+2|v><v|)/(D+2), ||v||=1. Need a full proof that the partial transpose of a pure rank-one projector is bounded below by -I/2. Standard proof uses Schmidt coefficients: negative eigenvalues are -s_i*s_j >= -1/2.
The (2 repeated n,1 repeated 2n)/(4n) orbit is (I+P)/(4n), where P is a rank-n orthogonal projection. Need partial transpose P >= -I for local dimension 3. One route: the partial transpose has operator norm at most 3 as a map on matrices; since ||P-I/2|| <=1/2, Gamma(P) >= -I. Proving this general induced norm bound may avoid full Schmidt eigenvalue classification.

These statements and the diagonalization/orbit bridge must be formalized, or the release must honestly state only complete spectral-optimization formalization with external quantum criterion. No axiom or named interface can silently stand in for them.
