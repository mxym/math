# Independent mathematical and exact-computation review

Date: 2026-10-08. Final disposition: PASS.

This is an independent review within the research workflow, not external
journal peer review. It does not certify literature priority.

## Analytic result checked

The reviewer independently rederived and checked:

1. The linear-first Bargmann identity, the deletion of row i and column j
   without transposition, and the positive-semidefinite Gram representation.
2. The exact degree-(N−1)/degree-N factorial ratio, giving L/(nL+1).
3. The cluster-constant compression, including its full spectrum and extra zeros.
4. Concentration at a unique maximum, with the quotient poles bounded by
   |P|^(2L−2)|(P/ell_i)(P/ell_j)| before passing to the limit.
5. The limiting matrix (J+zz*)/n and the critical-point identity sum z_i=0.
6. The simultaneous real-part limit and its largest-eigenvalue lower bound
   ||z||^2/(2n).
7. Weak Haar convergence after moving unitary rotations, proved through
   compactness and uniform convergence of continuous test functions.
8. The globally continuous truncation min(|b/a|^2,T), with exact Haar integral
   log(1+T), and the resulting divergent lower bounds.
9. Appending the conjugate peak row u* to make the projective maximum unique;
   in peak coordinates this is (1,0), adding a zero slope.
10. The order of quantifiers: first a finite sufficiently large base, then a
    finite sufficiently large repetition count for that frozen base.
11. Strict-gap continuity and scalar normalization for the positive-definite
    correlation extension, without claiming rank two after that perturbation.
12. The explicit real-direction Taylor formula and its interpretation only as
    an unbounded local second-order relative coefficient.

The sole wording correction found during review concerned a general complex
Rayleigh direction with row-versus-column Gram conventions. The final proof
uses a real unit direction and explicitly defines every entry of B(epsilon).
It also explains the alternative complex column-Gram convention. The final
calculation and all theorem statements are correct.

The approved PROOF.md SHA-256 is

d6644e37f2463d3856819586579bd32a9ee10bc79b78942fae9ef0cca1d161aa.

## Final manuscript and display

The four-page TeX manuscript agrees with the approved expanded proof. All four
rendered PDF pages were inspected. No clipping, overlap, missing reference,
missing mathematical bar/star/index, or overfull-box warning was found.
Wanless's formal bibliographic metadata were checked against EMS Press:
The Physics and Mathematics of Elliott Lieb, volume II (2022), 501–516,
DOI 10.4171/90-2/48.

## Exact finite certificate

The first verifier was independently rerun and passed. With a linear-first
Gram matrix C_ij=<g_i,g_j>, the precise identity is

    w* C w = ||sum_i conjugate(w_i) g_i||^2.

The TeX and integer implementation correctly use conjugate(w_i).

A second implementation tracks the coefficient of a formal marker s in

    product_i [ell_i + s conjugate(w_i) v_i,alpha],

rather than constructing the omitted products separately. It reproduces the
saved permanent, vector norm, Rayleigh numerator and denominator exactly,
checks the all-ones identity, and independently verifies

    269/100 < Rayleigh ratio < 27/10.

The approximate value 2.6976482817354444 is only an orientation aid, not part of
the proof. Both certificate inequalities use exact integer comparisons.

The first four CSV columns were checked row by row against the companion
Bapat configuration. They are the same Gram rows, with a newly supplied
Rayleigh vector. The portable second checker replaces that external path
with the verified canonical SHA-256 of those four columns and was rerun
successfully after this path-only packaging change.

## Exclusions from the review conclusion

The PASS does not assert a dimension growth rate, monotonicity in repetition
count, a uniform finite-epsilon gain, a real-A rank-two theorem, exhaustive
novelty, or a resolution of Lieb's character/subgroup conjecture. The theorem
is for complex A; taking Re C(A) restricts the direction vector, not the field
of A itself.
