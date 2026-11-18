# When do the corners maximize diversity on a Euclidean cube?

For which side lengths does a Euclidean square have a maximum-diversity probability measure supported on just its four corners? The answer is exactly $0<s\leq s_*$, where $s_*$ is the unique positive solution of

$$
e^{-s_*}+\frac{e^{-\sqrt{2}\,s_*}}{\sqrt{2}}=1,
\qquad 0.46019<s_*<0.46020.
$$

The measure gives the four corners equal mass. Above the threshold the note excludes **every** measure supported only on corners, but does **not** identify the new maximizing measure. Here the similarity is the exponential of minus Euclidean distance, not squared Euclidean distance or a product kernel.

**Uniform result.** In every dimension $d\geq2$, the uniform measure on the $2^d$ vertices is the unique simultaneous maximum-diversity measure of the solid cube of side $s$ whenever $0<s\leq s_*$. Its maximum diversity is
$$
\frac{2^d}{\sum_{k=0}^{d}{d\choose k} e^{-s\sqrt{k}}}.
$$
This is the best interval **common to all these dimensions**, because it is sharp for the square. It does not give the separate transition in every dimension. The same interval works for every finite square grid with those corners, and every fixed larger side length fails on all sufficiently fine square grids.

[Leinster and Roff, §10(2)](https://doi.org/10.1093/qmath/haab003) ask for the maximizing measure on a Euclidean cube or ball. This note answers only the first vertex phase on a square and gives a common interval for cubes, not the whole question. [Salim's 2021 thesis](https://etheses.whiterose.ac.uk/id/eprint/29673/) already treats finite square grids: sufficiently small-scale corner optimality for each fixed grid in the scope of her results follows from her orbit theorems. The corner-orbit value is also known. The energy characterization is standard, and [Dajani, §2](https://arxiv.org/abs/2610.38031) gives the potential criterion used here. What needs proving on the solid cube is the potential inequality at **every** point, up to the sharp common threshold.

- [Proof](PROOF.md): the corner potential has negative Laplacian along each face of dimension at least two. This reduces the sufficiency test to an edge; the sign of a single edge derivative controls all dimensions. A right derivative proves necessity on the square.
- [Independent internal mathematical review](REVIEW.md), including a second proof of the edge inequality.
- [Prior work and search limits](SOURCES.md).
- [Recorded verification output](CHECKS.txt). Run `python3 -B -O verify.py` and `python3 -B -O independent.py` with the Python standard library. Both are exhaustive outward-rounded interval certificates, not point samples; they use different derivatives and different bounds on the exponential.

AI-assisted research, independently checked by a second AI. Not externally peer-reviewed; no claim of priority.
