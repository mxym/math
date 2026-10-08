# Source and scope audit

Checked 2026-10-08. This is a bounded literature search, not an exhaustive priority
certificate. The mathematical proof is independent of an assertion that the
unboundedness theorem is new.

## Exact object

For every Hermitian PSD A, let C(A)_ij=A_ij per A(i|j), with row i and column j
deleted. The new claim proved in this package is

    sup lambda_max(C(A))/per A = infinity,
    sup lambda_max(Re C(A))/per A = infinity,

already over complex rank-two correlation matrices of unrestricted order. In fact
the same sequence can make both ratios arbitrarily large. The R=1 assertion was
already false, so this package does not announce a new disproof of that old
conjecture. It does not prove or refute Lieb's character/subgroup conjecture.

## Directly checked sources

1. Stephen Drury, *A counterexample to a question of Bapat & Sunder*,
   Mathematical Inequalities & Applications 21(2) (2018), 517–520,
   DOI https://doi.org/10.7153/mia-2018-21-37.
   Publisher PDF: https://files.ele-math.com/articles/mia-21-37.pdf.
   The full four-page formal article was read. Section 2 gives an 8 by 8 complex
   rank-two example and records a numerical search ratio about 1.01956. Section 3
   identifies the nontrivial cofactor spectrum with the (n−1,1) Fourier block of
   the Schur matrix. It does not state cofactor-ratio unboundedness.

2. Léo Pioge, Kamil K. Pietrasz, Benoit Seron, Leonardo Novo and Nicolas J. Cerf,
   *A logical implication between two conjectures on matrix permanents*,
   Linear Algebra and its Applications 725 (2025), 309–318,
   DOI https://doi.org/10.1016/j.laa.2025.07.011.
   Publisher record: https://www.sciencedirect.com/science/article/pii/S0024379525002952.
   Complete author manuscript checked: https://arxiv.org/html/2508.00111v1
   and https://arxiv.org/pdf/2508.00111v1; the arXiv record has only v1.
   Lemma 1 gives the local perturbation formula used, and rederived, in our final
   section. Theorem 1 gives a pointwise implication from the Hadamard conjecture
   to the cofactor assertion. Section 5 gives a real-Rayleigh violation for a
   complex 16 by 16 rank-two matrix, with ratio about 1.02982. No unbounded
   cofactor ratio is stated.
   A formally typeset copy is indexed at
   https://quic.ulb.ac.be/_media/publications/2025-laa-725-309.pdf,
   but direct fetches returned HTTP 502. Accordingly we checked publication
   metadata and the complete arXiv manuscript, not the full typeset text.

3. Léo Pioge, Benoit Seron, Leonardo Novo and Nicolas J. Cerf,
   *Anomalous bunching of nearly indistinguishable bosons*,
   https://arxiv.org/abs/2308.12226, latest v2 dated 2024-07-31.
   Complete v2 PDF and HTML were checked:
   https://arxiv.org/html/2308.12226v2.
   Sections 4–5 link the normalized cofactor spectrum to local bunching curvature,
   use Drury's 8-photon example, and report a finite enhancement. The conclusion
   asks for simpler scenarios and a clearer mechanism. This is a prior local
   perturbation result, not the unrestricted cofactor-ratio theorem here.

4. Benoit Seron, Leonardo Novo and Nicolas J. Cerf,
   *Boson bunching is not maximized by indistinguishable particles*,
   Nature Photonics 17 (2023), 702–709,
   https://doi.org/10.1038/s41566-023-01213-0.
   The institutional archived formal PDF was checked:
   https://dipot.ulb.ac.be/dspace/bitstream/2013/371550/3/2023-nat-photon.pdf.
   Equation (11) already gives asymptotically unbounded bunching-violation ratios.
   Those are Hadamard-product ratios per(H circ S)/per H at finite distinguishability,
   not lambda_max(C(H))/per H. This earlier unboundedness must not be advertised
   as newly discovered. Conversely, the cited statement does not by itself supply
   unbounded local cofactor curvature.

5. Nima Anari, Leonid Gurvits, Shayan Oveis Gharan and Amin Saberi,
   *Simply Exponential Approximation of the Permanent of Positive Semidefinite
   Matrices*, FOCS 2017, 914–925,
   https://doi.org/10.1109/FOCS.2017.89.
   Formal conference PDF checked:
   https://ieee-focs.org/FOCS-2017-Papers/3464a914.pdf.
   Claim 1 gives exponentially growing violations for the largest eigenvalue of
   the full Schur-power matrix. The cofactor matrix is a particular representation
   block and is much smaller. The full-matrix amplification does not establish
   this package's cofactor-block assertion or its fixed rank-two restriction.

6. Léo Pioge, Leonardo Novo and Nicolas J. Cerf,
   *Limits of multimode bunching for boson sampling validation: anomalous bunching
   induced by time delays*, https://arxiv.org/abs/2601.13792.
   The current HTML, particularly Section IV and its conclusion, was checked:
   https://arxiv.org/html/2601.13792.
   Equations (39)–(48) express Gaussian-delay derivatives using Re C(A) and use
   the complex 16 by 16 example with ratio about 1.0298. The finite-delay maximum
   reported there is a different quantity. No cofactor-ratio unboundedness was found.

7. Léo Pioge, Leonardo Novo and Nicolas J. Cerf,
   *A unified framework for anomalous boson bunching*,
   https://arxiv.org/abs/2607.19499, current v1 dated 2026-07-23.
   Complete current PDF and HTML were checked:
   https://arxiv.org/html/2607.19499v1.
   It distinguishes full Schur-power, Hadamard, local, and time-delay phenomena.
   No statement of the unbounded cofactor ratio was found.

8. Logan R. Chalmers, *The Bapat–Sunder eigenvalue conjecture fails over the reals*,
   September 2026 manuscript, full author-posted text at
   https://www.researchgate.net/publication/414009185_The_Bapat-Sunder_eigenvalue_conjecture_fails_over_the_reals.
   The theorem, certificate, and consequences were checked. They give a real
   rank-four order-32 counterexample, positive-definite perturbations and larger
   orders by identity padding. The displayed ratio is about 1.0004244. This
   already resolves the R=1 real-field question; it does not state unboundedness.
   We did not locate a peer-reviewed publication of this manuscript.

9. Ian M. Wanless, *Lieb's permanental dominance conjecture*, in
   *The Physics and Mathematics of Elliott Lieb*, vol. II, EMS Press (2022),
   501–516, https://doi.org/10.4171/90-2/48.
   The formal metadata were checked at https://ems.press/books/standalone/236/4538;
   the complete author version is https://arxiv.org/abs/2202.01867.
   It supplies the precise distinction between the general Lieb conjecture,
   permanent-on-top, and the cofactor assertion. Formal chapter full access is
   subscription-restricted; no claim of inspecting its typeset full text is made.

## Database consistency check

MathDB's page
https://mathdb.com/p/369591/bapat-sunder-s-largest-eigenvalue-conjecture-for-the-permane
correctly marks the R=1 conjecture refuted. Its numerical description, however,
mixes Drury's 2016 order-7 Hadamard example with the 2018 cofactor counterexample:
45 and 525/8 are respectively per A and per(A circ conjugate(A)) in the former
example, not per A and its cofactor maximum eigenvalue. Pioge et al. explicitly
state that the 2016 example satisfies the cofactor assertion. We also checked
that distinction directly by a separate permanent/minor computation. The
publisher's 2018 article is the controlling source for the cofactor example.

## Search limits and result

Searches covered the title/author citation chains above and combinations of
Bapat–Sunder, permanental cofactor, permanent matrix, spectral ratio, largest
eigenvalue, rank two, unbounded, arbitrarily large, and anomalous boson bunching.
No correction or later result establishing this exact unbounded rank-two
cofactor statement was found in the checked sources. This is a finite negative
search result. It does not prove that no such result exists anywhere.

The mathematical theorem and its proof remain meaningful without a priority
claim. The short manuscript therefore says neither “first” nor
“solves Lieb,” and does not relabel any previously disproved R=1 conjecture as
newly settled.

## Artifact and data provenance

The 200 Gaussian-integer Gram rows in witness_n200.csv are reused from the
parallel Bapat q-permanent construction in this research project. The last two
columns give a separately chosen Gaussian-integer cofactor Rayleigh vector.
No independent discovery of the underlying Gram rows is claimed. The finite
certificate is not an input to the analytic unboundedness proof.

Only the authorship team's proof, TeX/PDF, exact programs, certificate data,
review reports and source links belong in the public package. Downloaded
third-party PDFs, extracted full texts, build products and page-preview images
are not part of that package.
