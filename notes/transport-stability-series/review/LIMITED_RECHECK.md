# Limited recheck of the endpoint repair

Date: 8 October 2026.

## Final decision

**PASS. The previously identified local endpoint-proof gap is closed.** The replacement arguments prove both endpoint formulas under their original hypotheses. No differentiability, doubling, regular-variation, or logarithmic-derivative assumption on Phi or E has been added. The harmless R-domain defect is also repaired.

This is a limited recheck of the repair and necessary surrounding definitions, not a repetition of the complete batch review. The original review remains the record of the previous snapshot and the reasoning behind the finding. This receipt supersedes its open-repair status for the new third-manuscript hash below.

## Exact reviewed revision

- Revised manuscript: `research_math/binary_source_moment_envelope_20261008/PROOF.md`
- SHA-256: `2e683e3cf79a373e6f7921bf2d25e45783484548cb7abf85c765a0486f46efbe`
- Preserved original snapshot SHA-256: `2eaedf293a1661678f5cde712fd18b094c6e20d5e1c4dea7ea098de44feb8fc6`
- Revised README SHA-256: `7832240eb1c2ff97d61f9b5b81b268a128ee0e248848493742b512cc586dcbc7`
- Supplied `endpoint-repair.diff` SHA-256: `381c22c9381b14140e7090a48910a586d351f34157129d3a160ce9f786441dc9`

The supplied diff was independently regenerated from the preserved originals and current files. It matches byte-for-byte. The original snapshot agrees with the hash recorded in the first review. The source hashes were checked directly, rather than accepted from `REVISION.json` alone.

## Changes checked

### Section 7.1

The revised proof uses only the two-sided estimate J(t) comparable to [log(e/t)]^(-gamma/2). It takes the running maximum by comparison with an explicitly differentiable model function; it does not differentiate J or claim an index limit for E.

The inverse-moment step is valid under comparison alone: if R=Phi^-1(1/m), then

    1/m is comparable to R^2 [log(e+R)]^gamma.

Taking logarithms first gives log R comparable to log(1/m), with their ratio tending to 1/2. Substitution then gives sqrt(m)R comparable to [log(e/m)]^(-gamma/2). No doubling assumption is needed.

For a=gamma/2>0, the model k(t)=t^-1[log(e/t)]^-a is eventually decreasing in t and diverges at zero. It therefore controls the full running maximum after absorbing the fixed compact remainder. The proof correctly obtains H(h) comparable to J(h)/h, then uses the exact identity w=h_w J(h_w). Its logarithmic inversion and the stated non-Hölder formula are correct.

### Section 7.2

The proof now applies the main envelope directly to J(t) comparable to t^A[log(e/t)]^b, where A=alpha/2 and b=gamma/2+1/theta. Writing theta for the stretched-exponential exponent locally avoids conflict with the quantile function.

Here the inverse-moment step follows immediately by taking logarithms of 1/m comparable to exp(R^theta), giving R^theta=log(1/m)+O(1). The proof needs no derivative of Phi.

All three ranges are correct:

- A<1: the explicit quotient model diverges and is eventually decreasing in t, so the lower endpoint controls the running maximum up to constants. The exact scalar equation gives the displayed two-sided inverse and both powers in the modulus.
- A>1: the quotient tends to zero, so the running maximum stays between fixed positive constants for small h.
- A=1: the compact positive contribution and the logarithmic comparison give the exponent max(b,0), including b=0 and every negative b. The final exponent max(gamma+2/theta,0)/4 is unchanged.

There is no remaining invocation of Section 6's extra regularity hypotheses in either endpoint argument. The smooth staircase counterexample from the original review no longer invalidates any step: the repaired proofs apply to it through comparison alone.

### Definitions and scope

R(u)=Phi^-1(1/u) is now defined for 0<u<=1, so R(1-m) is legal. E remains on 0<m<=1/2. The added bound E<=1 follows from Phi(r)>=r^2 for r>=1 and R(m)>1. This is a consequence of existing assumptions, not a new hypothesis.

Writing the exact local formula of the already-fixed source clarifies the existing dependency and does not narrow an independently promised larger source class. The original text already fixed the single source from the preceding binary manuscript. The definition of two-sided comparison is consistent with the theorem statements.

The main theorem statement, Sections 2-6, Section 8, and the endpoint hypotheses and displayed conclusions were independently compared with the original snapshot and are unchanged verbatim. Other changes concern the repaired definition, source clarification, and accurate review-status metadata.

## Batch status after repair

- Top-N source/complexity theorem: **CONDITIONAL PASS ON (P)**, unchanged.
- Binary fixed-mass, minimum-weight, unrestricted envelope, and phase law: **PASS**, unchanged.
- General-Phi binary envelope, continuity criterion, index principle under its stated extra assumptions, bounded-radius variant, and the repaired endpoint applications: **PASS** at the revised hash.

The first two manuscript hashes remain unchanged:

- `c3cf5061de5ac9298f3fb88e07800c9d88257b01a1cd80f82fdc5e1a083055c1`
- `6858879d5acb26657b7d83ffc1b99386e67cd5c9fbf60ab451b579d132f1b9d8`

No open mathematical repair remains from this batch review. These decisions do not constitute formal verification, historical-priority certification, publication approval, or an audit of the proof of the imported theorem (P). No manuscript was modified or published during this recheck.
