# Bounded step walks on irreducibles in quadratic orders

Latest version **v4**, prepared 7 October 2026.

Version 4 proves an exact optimality statement for the Gaussian eight-neighbor principal-ideal sieve: the smallest possible common scalar period is exactly 130. Every period below 130 is ruled out by a complete family of exact nonzero-voltage certificates, while the historical period-130 potential is independently replayed. It also proves the parallel sharp classification in \(\mathbb Z[\sqrt2]\): minimum period 14, with exactly the two conjugate two-generator endpoint sieves.

- [Version 4 theorem and proof](v4/paper.md)
- [Version 4 proof audit](v4/PROOF_AUDIT.md)
- [Version 4 exact replay](v4/README.md)

Version 3 remains the full all-quadratic-order manuscript, with infinite-unit exception restoration and exact finite certificates.

- [Complete PDF, 26 pages](v3/quadratic_order_moat_v3.pdf)
- [Editable LaTeX](v3/source.tex)
- [Version 3 files and reproduction instructions](v3/README.md)
- [Mathematical changes](v3/CHANGELOG_v3.md)
- [Exact certificate instructions](v3/certificates_v3/README.md)
- [Build and verification status](../../verification/STATUS.md)
- [Historical version 2 PDF](v2/paper.pdf) and [source](v2/source.tex)
- [Historical version 1 PDF](v1/paper.pdf) and [source](v1/source.tex)
- [Upstream source, OpenAI family 028](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Bounded-Step-Walks-on-Gaussian-Primes-September-26-2026/paper.pdf)

## Version 3 scope (preserved)

The main all-quadratic-order existence theorem and A1–A5 analytic interface are unchanged. New finite certificates permit individual nonzero nonunit principal generators, including ramified norm-prime and composite-norm cases. Two adjugate congruences determine ideal membership, and the least scalar period is |N(alpha)|/gcd(a,b). Exact quotient-component sizes and selected norm values yield stronger conservative integer restoration bounds.

Complete four-step/eight-step examples give full irreducible component bounds of 20/92820 for Z[i] and 179200/351232 for Z[sqrt(2)]. These are upper bounds, not optimal component sizes. The failed Q30 Gaussian eight-step candidate has an explicit nonzero-voltage walk; the Q130 certificate succeeds. Failure concerns the avoiding sieve and does not imply an infinite irreducible walk.

The 41 norm-prime tests, 24 general-principal tests, independent finite-lift/direct-multiplication reconstructions, and 184-generator arithmetic checks pass. Finite tests do not prove the general analytic theorem. Computability is proved only for integral order models and supplied finite coefficient-step sets. The bounded programs do not implement unrestricted search and make no practical-runtime or arbitrary-real-input effectiveness claim.

## Build

Use a complete TeX Live installation in the v3 directory:

```sh
pdflatex source.tex
pdflatex source.tex
```

The source includes its bibliography and needs no external figures or bibliography database. Build output is source.pdf; the frozen supplied PDF is quadratic_order_moat_v3.pdf. The supplied SHA256SUMS checks the frozen version-3 files.

## Status and citation

Research proof draft with explicit upstream attribution. No external peer review, complete machine formalization, publication-priority claim, or personal authorship assertion is made. Versions 1 and 2 remain byte-for-byte preserved. Cite the exact version and Git commit actually used.

## Eisenstein quadratic-order continuation

A separate [exact Eisenstein graph research note](../../notes/eisenstein-prime-components/README.md)
proves global largest irreducible-element component sizes 48 for the
six-unit step set and 132 for the full eight-neighbor step set, together
with sharp principal-sieve scalar periods 6 and 546 and the sharp
period's complete optimal four-generator classification, even
for arbitrary composite-generator lists.
Complete finite proof witnesses and an independent integer checker
are provided. This is an additive note; the v3 all-order and v4
Gaussian/real-quadratic records remain unchanged.

## Sharp small-radius Z[sqrt(-2)] classification

The additive [Z[sqrt(-2)] prime-graph research note](../../notes/sqrt-minus-two-sharp-moats/README.md)
proves the **full infinite graph classification** for Euclidean step
radii D<2, with exactly two 3-vertex components and all remaining
components of size at most 2. It further proves the **least principal-
ideal sieve period 6** for the coefficient eight-neighbor graph,
and classifies every successful optimal-period generator list,
including composite generators and redundant ideals. Its full paper,
12 exact finite witnesses, independent checker, and mutation tests are
published separately, leaving the v3 all-order proof and v4 sharp
Gaussian/real-quadratic results unchanged.

## Exact Euclidean radius-two phase transition in Z[sqrt(-2)]

The [new radius-two continuation](../../notes/sqrt-minus-two-radius-two/README.md)
extends the entire irreducible graph classification through every
real D<sqrt(6), with a sharp largest component jump 3 to 7 at D=2,
and identifies the **unique** inclusion-minimal successful principal-
ideal sieve at the unchanged optimal scalar period 6 for the ten-step
set. Full proof, finite witnesses, checker, tamper tests and historical
comparison are supplied separately; older v3 and v4 are unchanged.

## Sharp norm-six threshold: exact minimal sieve period 1122

The [additive Z[sqrt(-2)] norm-six note](../../notes/sqrt-minus-two-sqrt6-period/README.md)
proves the sharp minimum principal-ideal scalar period **1122**
for all 14 steps of squared Euclidean norm at most six,
and a complete exact positive sieve decomposition of
204,800 residues. Its 682 lower-period voltage certificates
are checked independently of the generator, and it separately
proves a closed 90-irreducible component and uniform bound 2,283.
The exact unrestricted prime maximum is not determined;
historical entry 002 versions are unchanged.

## Exact norm-six sieve optimum and conditional genuine prime-graph equality

[The exact optimum](../../notes/sqrt-minus-two-exact-sieve-optimum/README.md) of finite principal-ideal sieve component size is 197, with matching constructive upper and universal admissible-pattern lower certificates. This also gives unconditional prime-only bounds **90 <= B_D <= 197**. A [separate explicitly conditional number-theoretic reduction](../../notes/sqrt-minus-two-conditional-prime-197/README.md) proves B_D=197 if one fully specified admissible family of 197 monic quadratic forms satisfies the unproved Schinzel Hypothesis H. Distinguish the completed unconditional sieve theorem from the not-yet-solved unconditional prime-only exact maximum. Independent exact checkers and proof audits are included; older 002 source files remain intact.
