# Independent mathematical fidelity audit

Date: 7 October 2026.
Verdict: **PASS.** No mathematical transcription defect, omitted governing hypothesis, altered constant, lost case, invalid geometric identification, or unsupported strengthened conclusion was found in the audited typesetting.

## Scope

Read all 318 lines of `POLYNOMIAL_REFINEMENT.md`, all 74 lines of `SQUARE_PYRAMID_LOWER_BOUND.md`, and all 681 lines of `proof.tex` in `notes/polynomial-dimensional-simplex-stability/`. Compared every displayed formula and the intervening arguments, including inline assumptions and case conditions. Consulted the relevant pinned invariant, truncation, affine-invariance, pyramid, and classical-attribution passages. Read the typesetting ledger after the primary texts to check the declared editorial changes.

This is an independent model-based mathematical/textual audit, not human peer review, proof-assistant verification, a universal theorem established by finite computation, or a novelty assessment. No frozen source or published artifact was edited. Work output is confined to this audit directory.

## Complete source-to-TeX coverage

Line references below use the audited local files.

| Source passage | `proof.tex` passage | Result |
|---|---|---|
| Refinement 7–37, invariant, theorem and exact constants | 50–109 | PASS: definitions, all quantifiers, exponent, exact constants, local half-coefficient, and arbitrary-law assignment bound retained |
| Refinement 39–77, determinant moments, witnesses and weighted selection | 111–162 | PASS: first absolute moments, witness count, determinant normalization, singular-tuple restriction, selection and D=0 all retained |
| Refinement 79–100, pointwise clipped witness and dispersion implication | 164–203 | PASS: Borel tie-breaking, both negative-coordinate cases, general norm, and separate dispersion assumption retained |
| Refinement 102–119, prescribed-simplex normalization | 205–228 | PASS: fixed original simplex, inradius, vertex inner products, radius calculation and global d+1 bound retained |
| Refinement 121–154, actual cone-law dispersion | 230–272 | PASS: actual cone law, source representation, Cauchy factor, chord bound and polar enclosure retained |
| Refinement 156–185, projection conversion | 274–312 | PASS: weighted inverse/barycentric correction, mass control, mixed-volume scale and absolute deficit retained |
| Refinement 187–209, improved cap | 314–345 | PASS: enclosing convex geometry in context, compactness, K-radius dependence, smallness gate and zero deficit retained |
| Refinement 211–250, local gate and original-simplex retention | 347–397 | PASS: all gates, permanent argument, original maximum and e=0 retained |
| Refinement 252–260, global branch and affine pullback | 399–414 | PASS: exact threshold identity, large-defect bound, prescribed centroid and affine invariance retained |
| Refinement 262–290, polynomial estimates | 416–442 | PASS: all inequalities and numerical factors retained |
| Refinement 292–306, sharpness and scope | 444–486 | PASS: lower obstruction, asymptotics, mean-versus-support distinction, exclusions and open target retained |
| Refinement 308–318, sources and literature scope | 488–519 and bibliography 635–679 | PASS: source roles and non-novelty caveats retained |
| Square-pyramid 3–26, conclusion and universal excess bound | 522–567 | PASS: full quantifiers, barycentric argument and centroid homothety retained |
| Square-pyramid 28–46, construction and maximality | 569–595 | PASS: exact polytope, simplex, invariant, arbitrary-vertex maximality and E=d+1 retained |
| Square-pyramid 48–62, direct facet certificate | 597–619 | PASS: complete facet data, volume, both sums and contributing-minor counts retained |
| Square-pyramid 64–73, comparison and numerical examples | 621–633 | PASS: exact small-truncation comparison and all three illustrative values retained |

## Analytic pressure points

1. **Every prescribed maximum simplex.** The theorem at TeX 72–80 quantifies over every maximum-volume inscribed simplex. TeX 206–209 normalizes that same prescribed simplex, rather than choosing a better one. The final comparison at 364–395 uses its maximal volume, not an auxiliary maximum. TeX 409–414 pulls back the homothety about its centroid. No best-simplex, translated-containment, or Banach–Mazur substitution occurs.

2. **Weighted anchor selection and division.** TeX 119–162 uses N=(d+1)(d+2)/2 witnesses. V is the absolute lifted determinant, not simplex volume. The selection law has density V/B, and the exact expectation is E[H 1_{V>0}]/B. Singular tuples may contribute to E H but do not appear in the ratio. Thus the proof does not replace E(H/V) by E(H)/E(V), require an inverse determinant moment, or assume a minimum on the open nonsingular set. The explicit D=0 statement is retained.

3. **Pointwise assignment.** TeX 164–196 retains the clipped negative coefficients. For x in the support, any coefficient at most -1 gives phi at least 1 and distance at most the support diameter. Otherwise clipping is inactive, and the pairs involving the chosen maximal positive coefficient control the remaining positive mass. The affine barycentric identity then controls distance in any fixed norm. This does not produce a support Hausdorff bound. TeX 198–203 invokes dispersion separately, at exactly the point where origin inclusion is needed.

4. **Real cone law, not arbitrary-law realization.** TeX 231–244 defines the normalized surface-area pushforward of the actual normalized K. The cited identity a=B/((d+1)A) yields D/B=(d+1)e/(1+(d+1)e); all factors agree with pinned entry005 v3, lines 173–190. The first-moment inequality gives e at least zero. TeX 245–262 retains the Cauchy factor 2 and the geometric chord-width argument for positive-direction dispersion. The latter is never inferred just from bounded support. Selected points on the actual polar boundary give K contained in P.

5. **Weighted inverse correction.** TeX 275–286 preserves alpha_i(x)=lambda_i(1-q_i dot x), with positive lambda_i summing to 1. Since alpha_i(c)=p_i, the identity p_i-lambda_i=-lambda_i q_i dot c is exact. Summation gives total variation at most M h using the weighted sum of q_i norms. No unsupported unweighted inverse norm estimate, minimum-weight bound, or extra factor d is inserted or required.

6. **Scale and projection conversion.** TeX 296–305 uses h_P(x) at least 1 on the cone-law support, Lipschitz control z at most M h, and the mixed-volume identity. Minkowski's first inequality gives |P|/|K| at most (1+z)^d in the displayed direction. Combining the normalized projection error, |P|-|K| at most d 2^(d-1) M h |K|, and pi_P/|P| at most d/2 gives exactly J=(d/2)(2R)^d[1+M+d 2^(d-1) M]. Genuine inclusion gives the required nonnegative deficits.

7. **Projection cap.** TeX 323–342 retains the farthest point, nearest-point supporting normal, and crucial radius bound ||q|| at most R+s. The projected ball lies strictly beyond the supporting hyperplane for s>0. Its inscribed cube gives the displayed cap-volume inequality. Rearrangement needs precisely sqrt(m) epsilon^(1/m) at most 1/2. The same inequality handles epsilon=0. P is the enclosing simplex already constructed; no larger polar-radius factor is silently substituted.

8. **Local/zero/global cases.** Exact e_0 gives y at most 1/(8dL), h at most 1/M, and s at most 1/(8d). The stochastic matrix W has all column norms at most 1, so Hadamard and its determinant lower bound force every column norm at least 1-delta. A repeated dominant row would lose at least (1-2delta)^2 in the permanent, contradicting delta at most 1/8. Matching all vertices gives the original-simplex containment and local coefficient G_d/2. At e=0 the same route gives h=s=delta=0. Finally G_d e_0^(1/m)=R+1 at least d+1 closes e>e_0 by the universal maximality bound, with no gap at the threshold.

9. **Polynomial constant.** Independently recombined the estimates at TeX 419–426: J C at most 3d^5 M(4R)^d; extracting 4R from its 1/(d-1) power and using R+1 at most 2R and L at most 4 sqrt(d) R gives exactly 256 d^(3/2) R^3 [12d^5 M R]^(1/(d-1)). M=4dR produces 48d^6R^2. R^2 at most (5/3)d^3 gives 80d^9 and outside growth d^6. The integer induction bound on d yields the factor below 1280; the final coefficient is 737280<2^20. The exact asymptotic 64d^6 at TeX 482–483 also follows: (JC)^(1/(d-1)) is asymptotic to 4R and R is asymptotic to d^(3/2). No O(d^2) result is claimed.

10. **Square-pyramid certificate.** The d+2 listed facets contain the coordinate nonnegativity constraints as well as the two upper square constraints. The square cross-sectional volume integrates to 2/d!. Every full-dimensional vertex simplex contains all e_3,...,e_d and three square vertices; separate convexity of absolute volume then covers arbitrary interior vertices. The point e_1+e_2 has barycentric coordinate -1, giving E=d+1. For the horizontal minor sum the groups with zero, one and two top facets have coefficients 1,d,d-1 times c^d 2^(d-2), summing to c^d d2^(d-1). Exactly four lifted minors contribute c^(d+1)2^(d-2), giving L=c^(d+1)2^d. Since d|C_d|=2c, their ratio is a=1/d and e=1/[d(d+1)]. Thus the stated universal coefficient obstruction and its strict comparison with the small-truncation obstruction follow. The optional pyramid recursion is correct but not needed for this certificate.

## Source-derived clarifications and citations

- TeX 51–62 adds standard compactness/interior and projection-body conventions, and identifies the pyramid operator. These match entry005 v3, lines 9–15; they do not change the invariant. Evaluation of the projection ratio in its argument's dimension is necessary and correct.
- TeX 534–544 recalls the facet-minor definitions and explains the local H,L reuse. These exactly match entry005 v3, lines 19–22. At a boundary origin some b_i are zero, but they are only entries in the valid facet determinant formula; they are not used as positive cone-law probabilities.
- TeX 445–452 explicitly restricts E=(d+1)t to the maximum simplex used in the obstruction. This is a useful faithful clarification: truncation-proof.tex, lines 127–143, gives E=(d+1)t max_i p_i for all maxima, with supremum (d+1)t. Its defect asymptotic appears at lines 114–118; the coefficient obstruction appears at lines 338–358.
- The affine invariance and pyramid recurrence are directly confirmed in pinned entry005 v2, lines 74–86, 153–169 and 219–227. The bibliography's Schneider attribution is present in the pinned main manuscripts, including entry005 v3 line 388 and released-explicit-modulus.md line 241.
- The four pinned manuscript URLs in the bibliography agree with the corresponding entries in SOURCE_PINS.json. All seven local source-pin entries match their recorded byte lengths and SHA-256 values. This audit verified local pins; it does not newly claim that every GitHub file was remotely refetched.
- Fresh primary-source inspection confirmed the limited literature descriptions. [Böröczky's author-hosted paper](https://www.renyi.hu/~carlos/rogerstab.pdf), printed page 3, Theorem 3, concerns polar projection-body volume and a selectable-simplex Banach–Mazur modulus with coefficient n^(88n) and exponent 1/n. [Böröczky–Henk](https://www.renyi.hu/~carlos/cone-volume-stability.pdf), abstract and Theorems 1.1–1.3, concerns subspace concentration and the U-functional. [Böröczky–Fodor–Hug](https://arxiv.org/abs/2001.10706), abstract, concerns mean width and the ell-norm in John/Löwner positions. They are used only for literature positioning, with no quantitative estimate imported into the proof.

## Scope and provenance claims

TeX 45–47, 108–109, 471–486 and 516–519 preserve the distinction between written model-reviewed mathematics, human peer review, formalization and priority. Historical review and search statements are attributed to the frozen refinement. The text does not claim human peer review, Lean verification, an exhaustive novelty search, first discovery, a best-known bound, a theorem for a different deficit, dimension-free constants, O(d^2), anisotropic stability, or simultaneous/multiple truncation results. The only improved-growth research target mentioned is O(d), expressly open here.

## Supplemental finite replay

Ran the existing `check_independent_refinement_audit.py` read-only, after inspecting its source for writes. It passed the five exact rational law/witness cases, direct square-pyramid facet sums for dimensions 3–12, and log-domain constants/gates for dimensions 3–10000. These finite checks supplement the full analytic comparison above and do not prove the universal claims. No output-writing constant checker was run against the frozen release.

Audited primary hashes:

- POLYNOMIAL_REFINEMENT.md: `2b398cba3afd73819dbf90d5106e64be64ba06a07f9e42d23f4c2037ff5cd791`
- SQUARE_PYRAMID_LOWER_BOUND.md: `dee887e50590cd750d5b211acd9015fa57db5bd70786dcd67ec701674139596e`
- proof.tex: `73ff46719e442da83eb773ff0f1ee7d9b49d30bfa2200786a11fe433fe09572c`

## Disposition

The frozen release’s complete `sha256sum -c SHA256SUMS` check passed after this audit (33 entries), including both source markdown files, proof.tex, proof.pdf and the pinned sources.

PASS. No mathematical correction is requested. This audit supplies no authorization to publish or mutate the frozen release.
