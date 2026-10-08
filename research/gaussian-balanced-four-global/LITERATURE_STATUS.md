# Literature status: equal-mass Gaussian four-cell first moment

Screen date: 8 October 2026. This is a focused source comparison, not a proof
review, exhaustive citation search, or priority assessment.

## Target

For every measurable partition C1,...,C4 of standard Gaussian R^d, d >= 3,
with gamma_d(C_i)=1/4, the candidate statement is

    sum_i || integral_{C_i} x d gamma_d ||^2
        <= 12 (arctan(sqrt(2)))^2 / pi^3,

with equality only for a centered regular tetrahedral conical partition,
extended cylindrically in dimensions d > 3, up to null sets, orthogonal
maps, and relabeling. The draft PROOF.md was not reviewed here.

## Direct prior conjectures

1. Steven Heilman, “Euclidean Partitions Optimizing Noise Stability,”
   Electronic Journal of Probability 19 (2014), no. 71, 1–37,
   [arXiv:1211.7138](https://arxiv.org/abs/1211.7138), v2 read in full.
   Conjecture 3 (printed pp. 36–37) takes k=4, n=3 and says that a
   maximizer of the first-moment functional psi_0 among equal-mass
   fractional partitions is simplicial conical. The surrounding text
   distinguishes the unrestricted fractional class, where the result is
   known, from the equal-measure class at issue. This is a direct statement
   of the three-dimensional equal-mass case, presented as a conjecture.

2. Steven Heilman, “Stable Gaussian Minimal Bubbles,”
   [arXiv:1901.03934](https://arxiv.org/abs/1901.03934), v1 read in full.
   Problem 1.15 and Conjecture 1.16 (printed p. 8) state the prescribed-mass
   first-moment problem for m > 3, m-1 <= n+1, and conjecture that its
   maximizers are simplicial cones over a regular simplex. At equal masses
   with m=4, the centering vector in the problem is zero, so this includes
   the current objective and all d >= 3. The introduction (printed p. 4)
   explicitly describes the m > 3 first-moment question as open at the
   time of writing. This historical statement does not establish its status
   in 2026.

These are prior conjectures for the target, not prior proofs of it.

## Nearby results checked and distinguished

- Emanuel Milman and Joe Neeman, “The Gaussian Double-Bubble and Multi-Bubble
  Conjectures,” Annals of Mathematics 195 (2022), no. 1, 89–206,
  [DOI 10.4007/annals.2022.195.1.2](https://doi.org/10.4007/annals.2022.195.1.2),
  [arXiv:1805.10961](https://arxiv.org/abs/1805.10961), full text checked.
  Theorems 1.1–1.2 prove unique minimization of Gaussian perimeter by the
  simplicial cluster for 2 <= q <= n+1 and every positive prescribed
  mass vector. This includes the equal-mass tetrahedral cluster, but the
  optimized functional is perimeter, not squared first moments.
- Abhijeet Mulgund, “Stochastic Domination of Gaussian Maxima by the Regular
  Simplex,” [arXiv:2609.28452](https://arxiv.org/abs/2609.28452), v2 full text
  checked. Theorem 1.1 concerns the CDF of the maximum of a centered
  unit-variance Gaussian vector; Corollary 1.2 gives a circumscribed-simplex
  volume inequality. These do not optimize over arbitrary equal-mass
  measurable partitions.
- OpenAI Mathematics, “The Gaussian Propeller Bound in Every Dimension,”
  24 September 2026, local PDF checked at
  https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Gaussian-Propeller-Bound-in-Every-Dimension-September-24-2026/main.pdf.
  Theorem 1.1 permits arbitrary cell probabilities and empty cells, and its
  sharp value is attained by three planar sectors. It is not the positive
  four-cell equal-mass problem.
- Heilman–Mossel–Neeman, “Standard Simplices and Pluralities are Not the Most
  Noise Stable,” Israel Journal of Mathematics 213 (2016), no. 1, 33–53,
  [arXiv:1403.0885](https://arxiv.org/abs/1403.0885), is about positive-noise
  stability and unequal masses in the counterexamples checked. It does not
  state the equal-mass zero-noise first-Hermite extremal theorem.

## Search scope and status

The check read the primary full texts listed above, searched the repository's
Gaussian partition and centroid literature records, and checked the local
OpenAI Mathematics snapshot at commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. A focused Crossref query for
Gaussian quantization / principal points / equal-probability clustering did
not reveal a direct theorem; returned records were not treated as evidence of
absence. The equal-mass objective can be recast as a Gaussian squared-error
quantization problem with prescribed equal cell probabilities, but the
quantization sources found in this screen were not verified to prove or
disprove this exact global claim.

No exact published proof or counterexample for the target was located in this
limited screen. This does not establish that none exists, does not prove the
conjecture remains open, and supports no first/priority claim. The candidate
result would settle the direct Heilman conjecture in the equal-mass four-cell
case if its proof is independently validated.
