# Proof review and verification scope

This is a complete written counterexample to the precisely dated
arbitrary-mass conjecture. The review was performed within this AI
research workflow; it is not external professional mathematical review.

## Mathematical review

| Possible failure | Resolution in the proof |
|---|---|
| Wrong target functional | Equation (2) shows that the centering in Problem 1.15 adds the fixed constant $4\|w\|^2$; the common factor is positive. |
| Refuting only an invented subclass | The source's arbitrary positive mass statement contains the displayed four-cell mass vector, and the theorem constructs a competing measurable partition with exactly those masses. |
| A different regular apex might work | Strict mass-price ordering forces the three equal prices. The remaining one-parameter mass function is strictly decreasing, hence has a unique apex. Orthogonal transformations preserve the objective. |
| The facet comparison might depend on floating values | Two exact Gaussian planar integrals give nested domains: $A(t)<A(0)=B(0)<B(t)$ for every $t>0$. No decimal comparison is used. |
| Flux sign or missing normalization | Inward normals are $(v_i-v_j)/(2\sqrt2)$ and the truncated spherical Gaussian flux vanishes. Exact algebra independently checks both tangent and normal components. |
| Variation might not preserve mass | Two interior concentric balls are selected with exactly equal Gaussian measure by a continuous strictly increasing radius function; their membership transfers preserve every mass. |
| A formal first variation might fail to imply an actual gain | Equation (15) is the exact change for the actual changed moments and has a strictly positive margin. |
| Balls might cross other cells | The $12$-plane distance is $\eta$, and all other relevant separating-plane distances exceed $1/2$. Each radius is less than $\eta/2$. |
| There might be no optimizer, making the claim vacuous | Weak compactness supplies a fractional optimizer; an extreme point of its maximizing linear face is an indicator partition and has the same maximum. |
| Equal-mass conjecture might be inadvertently included | The parameter interval is strictly $0<p<1/4$; at $p=1/4$ the tangent imbalance vanishes. No equal-mass conclusion follows. |
| Positive-noise prior work might already state the result | HMN's cited theorem concerns $\rho\ne0$. The first-moment claim here is proved directly, and its historical novelty is not certified. |

## Recorded verification

The exact standard-library checker checks 144 positive rational facet
parameter pairs in $\mathbb Q(\sqrt2)$ and rejects reversed facet order.
It verifies ball containment at the fixed apex $(1,1,1)$, centering,
both moment-difference components, the exchange identity and its strict
margin. Ordinary and optimized Python outputs are byte-identical.
Finite parameter checks are diagnostics, not a proof that Gaussian
facet measures satisfy the ordered hypotheses; Lemma 2 proves that
analytically for every $t>0$.

`Algebra.lean` proves four universal lemmas: the centering constant for
any finite number of scalar coordinates, the tangent identity, the
exchange norm identity and the strict-margin inequality for all ordered
positive facet values. The file is freshly compiled with official
Lean 4.34.1. `Replay.lean` rejects unexpected axioms/unsafe dependencies
and replays all 7,680 declarations in those roots' proof closure into
an empty trust-level-zero kernel environment. It checks unchanged root
types and universe parameters. A false ordered-gap control is rejected.

The entire Gaussian theorem is **not** Lean-formalized: integrals,
measure selection, strict ordering of masses, Gaussian flux and weak
compactness/existence have written proofs. The standard foundational
results used in existence are stated in Section 6. No numerical search
or solver certificate is part of the mathematical proof.

Source hashes distinguish the precise public conjecture version from
reused infrastructure. The exact outputs, raw Lean logs and typeset
PDF report are in `results/`; the inventory verifier checks the final
published bytes. Standard Lean axioms `propext`, `Classical.choice`,
`Quot.sound`, the official compiler/kernel/runtime and the machine are
trusted. Literature priority and external human review remain separate
from correctness of the stated proof.
