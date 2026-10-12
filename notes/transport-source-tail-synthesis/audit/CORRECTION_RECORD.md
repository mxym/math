# Synthesis B correction record

Date: 7 October 2026

The corrected synthesis applies these 11 exposition and review-status changes. Section 1 and all 10 theorem, lemma, corollary and proof environments are unchanged. The entries preserve the applied correction text, except that entry 11 omits a workflow-only label from the status value. No new mathematical claim, authorship attribution or license is introduced.

The underlying mathematical audit was independent and model-based. No human peer reviewer participated; no Lean or other formal verification, literature-novelty certification, or general transport-necessity claim is made.

The replacement strings below show the approved correction-stage wording before the public-copy edits recorded in [RELEASE_DELTA.md](../RELEASE_DELTA.md); they are not all literal final-file strings.

## 1. synthesis.tex

Purpose: accurate completed model-audit status.

Corrected text:

```tex
The proposed synthesis has undergone an independent model audit. This is not external human peer review or formal verification.
```

## 2. synthesis.tex

Purpose: exact compact-source and proper-extension hypotheses.

Corrected text:

```tex
For a full-dimensional log-concave probability density supported on a compact convex body $K\subset B_R$, $R>0$, its Theorem 1.4 instead supplies $A_\rho=(1+\sqrt{162})R$. Its centered potentials are in $L^2(\rho)$ and finite and convex on $\operatorname{int}K$; their proper convex extensions to $\R^d$ supply the domain convention of Lemma 3.1.
```

## 3. synthesis.tex

Purpose: explicit source marginal for the critical slowly-varying application.

Corrected text:

```tex
For sufficiently small $a>0$, the first marginal is $f(x)=c x^{s-1}L(x)e^{-x^2/2}$ on $0<x<a$, with the same transverse factors $g$ as above. It is extended with a $C^2$, $1$-strongly convex potential and quadratic tail.
```

## 4. synthesis.tex

Purpose: separate finite-q, stretched-exponential and logarithmic-second-moment endpoint quantifiers.

Corrected text:

```tex
The fixed smooth steep-layer construction in 007 has the optimal finite-moment power and a vanishing endpoint ratio. The strengthened construction in 001 v5 also has a vanishing endpoint ratio for its stretched-exponential obstruction, while its logarithmic-second-moment lower comparison has a positive ratio along a sequence. These conclusions differ from 008's two-sided all-small-distance envelope.
```

## 5. synthesis.tex

Purpose: complete historical L1 and sufficient-root citations.

Corrected text:

```tex
\item 001 v5, Lemma 3.1, Propositions 4.1--4.2 and 5.1, and Theorem 6.1; its root sufficient condition overlaps 008 and is counted once.
```

## 6. synthesis.tex

Purpose: complete boundary-translation and critical inverse citations.

Corrected text:

```tex
\item 008 v1, Lemmas 2.1 and 4.1, Theorem 2.2, Corollary 2.3 and Theorems 1.1--1.2; its later critical slowly-varying supplement, Theorem 1, Corollary 3 and Remark 4, supplies the implicit modulus, the criterion within that family, and the inverse-substitution limitation.
```

## 7. REVIEW.md

Purpose: completed review status without a stale page count.

Corrected text:

```text
The proposed proof and its imported statements have undergone an independent model audit. This does not constitute external human peer review, proof-assistant verification, or a literature-novelty certification.
```

## 8. REVIEW.md

Purpose: matching exact compact-source domain.

Corrected text:

```text
Its compact companion, Theorem1.4, assumes a full-dimensional log-concave probability density supported on a compact convex body K contained in B_R, R>0, and has A=(1+sqrt162)R. Centered potentials lie in L2(rho), are finite and convex on int K, and use proper convex extensions to R^d for interpolation.
```

## 9. README.md

Purpose: accurate review boundary.

Corrected text:

```text
It adopts no publication decision. The proposed proof and imported statements have undergone an independent model audit; this is not external human peer review or formal verification.
```

## 10. README.md

Purpose: avoid a stale page count after exposition edits.

Corrected text:

```text
[Proof PDF]
```

## 11. DEPENDENCIES.json

Purpose: accurate dependency review status.

Corrected text:

```json
"status": "independent model audit completed; no external human peer review or formal verification"
```

## Preservation and verification boundary

The correction record changes exposition, source attribution, review status and a PDF-link label. It does not modify the theorem statements or proofs. The earlier audit's rendering checks concern the pre-correction PDF. A release-specific PDF build and equality checks must be recorded separately; this file does not assert that those release checks were performed by the mathematical audit.

The mathematical imports still require the stated proper-convex domains, L² conditions and the separate all-P₂ potential estimate (P). The proof characterizes the density-overlap method; it does not establish necessity for general transport stability. Existing sufficient directions and the older density-level L¹ limit retain their original attribution.
