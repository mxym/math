# Complete proof of the pure qutrit ECQC counterexample

Yongxian Zhang (张永贤), School of Computer Science and Engineering, South China University of Technology. Email: mxymmxym1@gmail.com. ORCID: 0009-0000-3864-3536.

This supplement supplies the mathematical interpretation of the Lean definitions and connects the manuscript's explicit qutrit construction to its actual quantum statement. It does not assert that the separate all-prime classification or the Holevo theorem has been formalized.

## 1. Actual quantum objects and the original minimum

In the standard product basis, a bipartite qutrit vector is a function on `Fin 3 × Fin 3` with complex coefficients. A density operator is a positive-semidefinite complex matrix of trace one on that nine-element index type. The pure density associated to a normalized vector v is exactly the matrix with entries v_i conjugate(v_j). The two partial traces sum the repeated index on the respective tensor factor.

A local measurement matrix B has its outcome vectors in its columns and satisfies B* B = I, where * is the conjugate transpose. In square finite dimension this is the usual orthonormal-basis condition. A complete qutrit MUB family consists of four such matrices, with every squared modulus of a cross-basis overlap equal to 1/3. These conditions are proved for the displayed matrices, not taken as hypotheses about the witness.

For local outcomes j,k, the joint vector is x ↦ B[x_1,j] B[x_2,k]. The probability is the real part of v* ρ v. The same B is used on both parties; Bob's basis is not separately conjugated. A general Lean lemma proves that for ρ = |ψ><ψ| this expectation equals |v* ψ|². Thus the table computation is linked to the actual density-operator Born rule.

For a real probability vector p, H(p) = -Σ p_i log(p_i), with 0 log 0 = 0. Mutual information uses the actual row and column sums of the Born table. The ECQC score is the infimum of all sums over three of the four distinct setting indices. We prove that its entire value set is the singleton {3 log 2}; hence this infimum is precisely the original attained minimum, not a conveniently selected subset score. Natural logarithms multiply the original bit-valued quantities by the positive constant log 2.

## 2. Spectral entropy is proved, not supplied

For a Hermitian matrix A, `vonNeumannEntropy A hA` is -Σ λ_i log λ_i, using Mathlib's actual eigenvalues from its proved spectral theorem. The function `matrixEntropy` extends this definition by zero outside the Hermitian domain; that unused branch is excluded for the state and both actual partial traces by explicit Hermitian proofs.

The key general result is: if A is Hermitian, A² = a A, and Tr(A) = 1, then S(A) = -log a. For every eigenvector u_i of norm one, A²u_i = λ_i²u_i and aAu_i = a λ_i u_i. Since u_i is nonzero, λ_i(λ_i-a)=0. Thus every actual eigenvalue is zero or a. In either case -λ_i log λ_i = -λ_i log a. Summing and using Mathlib's trace-eigenvalue identity gives the asserted entropy. This argument neither assumes the spectrum nor needs an externally certified eigenvalue multiplicity computation.

The explicit normalized vector is

    ψ = (|01> + |02> - |10> - |20>)/2.

The density ρ = |ψ><ψ| is positive semidefinite, has trace one, and satisfies ρ² = ρ. Both actual partial traces are

    R = [[1/2, 0,   0  ],
         [0,   1/4, 1/4],
         [0,   1/4, 1/4]].

The proofs establish R² = R/2 and Tr(R)=1. The same spectral lemma gives S(ρ)=0 and S(R)=log 2. It also proves the nonnegative eigenvalues needed to check that R itself is a density matrix. Therefore Q(ρ)=S(ρ_A)+S(ρ_B)-S(ρ)=2 log 2.

## 3. Exact bases and all Born probabilities

Put α = sqrt(3)/3 and β = -sqrt(3)/6 + i/2. The four measurement matrices are the identity and

    [[α,α,α], [α,β,conjugate(β)], [α,conjugate(β),β]],
    [[α,α,α], [β,conjugate(β),α], [β,α,conjugate(β)]],
    [[α,α,α], [conjugate(β),α,β], [conjugate(β),β,α]].

With ω = -1/2 + i sqrt(3)/2, we have αω=β, so these are the normalized quadratic Fourier matrices in the manuscript. The Lean certificates expand the finite sums over the actual complex entries, split real and imaginary parts, and reduce them using (sqrt 3)²=3. All orthonormality identities and all cross-basis overlaps are checked by kernel-checked algebraic proof terms. No numerical square root approximation or compiled decision oracle is used.

For every one of these four settings, the actual Born table equals

    P = [[0,   1/4, 1/4],
         [1/4, 0,   0  ],
         [1/4, 0,   0  ]].

The table is nonnegative and sums to one. Each marginal is (1/2,1/4,1/4), so each marginal entropy is (3/2) log 2. The joint entropy is 2 log 2, since exactly four entries have mass 1/4. Consequently each measured mutual information is log 2. The logarithm identities and finite entropy sums are proved in Lean, not delegated to a symbolic checker.

## 4. Unconditional original-statement contradiction

Every three-setting subset has sum 3 log 2. Such subsets exist, and their value set is proved to be exactly that singleton. Hence

    ECQC(ρ) = 3 log 2 > 2 log 2 = Q(ρ).

The strict inequality uses the proved positivity of log 2. The endpoint packages the normalized vector, the actual density matrix, the complete MUB family, the two exact information values, and the strict violation. A second endpoint explicitly negates the universal pure-state ECQC statement over all prime dimensions by specializing to the prime 3.

The complete qutrit counterexample does not use Holevo's accessible-information theorem, numerical optimization, an assumed entropy interface, unproved quantum-classical embedding, or extrapolation from finitely many dimensions. Its correctness does not imply that the sharp ratio bound, the two-dimensional positive theorem, the five-dimensional examples, full-Schmidt-rank strengthening, or all-prime asymptotics have been checked by this package.

## 5. Provenance, assistance, and rights

The mathematical construction is the one already recorded in `research/ecqc-pure-state-counterexamples/QUTRIT_EXACT.md` and the manuscript's three-dimensional subsection. The current contribution is its complete Lean proof chain and the reusable spectral and Born lemmas. The original conjecture is Iqbal, arXiv:2509.08286v2, Conjecture 3.1/equation (6). Prior mixed-state disproofs remain credited by the manuscript; no first-disproof or external-peer-review claim is made.

AI assisted derivation, implementation, debugging, documentation, and self-audit. No external funding supported this work. Separately authored original material is copyright 2026 Yongxian Zhang, all rights reserved. Mathlib and other dependencies retain their licenses. The proof-closure replay driver is adapted from the repository's earlier verification packages; its procedural code is not an axiom in any mathematical theorem.
