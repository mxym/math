# Uniform real-rootedness of the (132,213)-avoiding permutation-polytope family

Status: complete parent proof candidate, pending independent review. No public
claim of a solved conjecture is authorized on the basis of this draft alone.

## Statement

For every integer d>=3, the Ehrhart h*-polynomial of the convex hull of
(132,213)-avoiding permutations in S_d has only negative real zeros. The d=1,2
polynomials are constant 1. This is Conjecture 10.1 in Pedro M. M. de Castro,
Ehrhart h*-polynomials of (132,213)-avoiding permutation polytopes: A repair
cone and eventual real-rootedness, arXiv:2609.06096v1 (5 September 2026).
Fixed primary source: https://arxiv.org/html/2609.06096v1 .

## Imported prior results, explicitly delimited

We use the source's exact refined Eulerian transform, primitive/divisor series
and marked identity (Sections 5 and 8, equations (34)–(37)); its compatible
repair-cone criterion, Proposition 6.2; its nonnegative endpoint coordinates;
the elementary product and periodic estimates in Lemma 9.1; and its proved
finite Theorem 1.3 for d<=1000. We also use Darroch's integer-mean mode theorem
for independent Bernoulli sums. None of these inputs is a claimed new result.
The source's d<=1000 CSV has NOT been independently reconstructed in this
parent work. A final paper must state that dependence transparently and make
the source finite-certificate provenance accessible. The new proof covers ALL
d>=1001 without using the source's d>=2^72 conclusion.

## Proof for every d>=1001

Let c=2-sqrt(3). The repair-cone criterion asks for nonnegative endpoint
coordinates and positive geometric tails S_(d,r)(c), 1<=r<=d-2.

1. FORWARD_BLOCK_1001.md proves the criterion for r<=floor(d/4). It sharpens
   the connected-series mass bound and replaces exp(140) by exp(30).
2. For the remaining coordinates j>=floor(d/4)+1 and j<=d-2, write
   m=d-1-j. Then 1<=m<=d-2-floor(d/4). There is a unique saddle x>0 with
   mu_d(x)=m. The source's elementary estimate mu_d(15)>3d/4 for d>1000
   gives x<15.
3. SMALL_SADDLE_POSITIVITY.md proves positivity of each reversed coefficient
   for 0<x<=1/10. LARGE_SADDLE_POSITIVITY.md proves it for 1/10<=x<=15.
   Their common tools and explicit constants are proved in
   CENTERED_COMPARISON_LEMMA.md, SHARP_FOURIER_CONSTANTS.md,
   CENTERED_MAJORANT_LEMMA.md and LARGE_COMPONENT_SMOOTHING.md.
   Infinite dimensions are handled analytically; finite rational certificates
   establish only scalar interval envelopes and induction bases.
4. Thus all a_(d,j)>0 for floor(d/4)+1<=j<=d-2. Each remaining geometric tail
   is a positive sum of these coordinates. Proposition 6.2 now gives real
   roots. Nonnegative Ehrhart coefficients and H_d(0)=1 exclude nonnegative
   roots, hence every root is strictly negative.

For d<=1000 apply the cited finite theorem (including constant d=1,2 and the
repeated negative root at d=3). This completes the claimed uniform theorem,
subject to independent checking of this new argument and its stated inputs.

## Exact reproduction of the new scalar certificates

Run, using ordinary Python 3 with only the standard library:
 python verify_small_x_majorant.py
 python verify_majorant_tail_constants.py
 python verify_large_x_intervals.py

The second imports the third's rational-enclosure helpers. All logical checks
use explicit exceptions, not Python assert. Float displays are non-evidentiary.
The older probe*.py files and their finite floating-point logs are exploratory,
not proof premises and must not be included as purported verification.

## Scope and novelty

This resolves a specific one-family Ehrhart real-rootedness conjecture if the
proof survives review. It does not establish a general real-rootedness theorem
for arbitrary pattern-avoidance classes, arbitrary poset permutahedra, or all
Ehrhart polynomials. No priority claim, external referee endorsement, or Lean
verification is asserted. The initial bounded source search found v1 as the
current open statement; recheck newer versions and citations before publication.
