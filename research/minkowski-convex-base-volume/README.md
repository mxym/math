# Two proofs of a convex-base sumset volume inequality

**Research draft.** For nonempty compact subsets of Euclidean space, the draft gives an affirmative answer to [Fradelizi–Madiman–Zvavitch, Conjecture 3.11](https://doi.org/10.1093/imrn/rnae095), and to the stronger question on nonconvex bases immediately preceding it. The latter was originally asked in [Fradelizi–Madiman–Marsiglietti–Zvavitch, Remark 4.16(1)](https://ems.press/content/serial-article-files/37001#page=41). The write-up has undergone an independent internal AI mathematical review. It has not undergone external peer review; no claim of priority.

For any dimension $d≥1$ and nonempty compact $A,B,C\subset\mathbb R^d$, the result is
$$
 |A+B+C|+|\operatorname{conv} A|\ge |A+B|+|A+C|.
$$
If $A$ is convex, the correction is simply $|A|$. The compact summands $B,C$ may be nonconvex, disconnected or of zero volume. Without a convex base the hull correction cannot in general be replaced by $|A|$. The proof applies to ordinary Lebesgue volume and ordinary Minkowski addition; it is not a claim of log-submodularity, a fractional result, or a solution for higher iterated differences.

**Idea.** A point outside a convex obstacle violates a supporting halfspace inequality. Translate it by a point of $B$ furthest in that direction. By ordering the directions and using the *first* violation, each translated piece stays separate from the others. This preserves exterior volume by translation. A second proof recovers the translating point from a Euclidean projection instead.

- [Proofs and corollaries](PROOF.md): two self-contained arguments for the exterior inequality, followed by the deduction for sumsets.
- [Sources, priority search and limits](PRIOR-AND-CHECKS.md): known one-dimensional, all-convex and zonoid cases, recent multiplicative counterexamples, and scope of duplicate checks.
- [Independent AI review](REVIEW.md): mathematical audit of the submitted projection proof and a separate halfspace argument.
- [Author's exact area test](verify.py) and [reviewer's independent pointwise test](independent.py): standard Python only. From this directory run:

```sh
sha256sum -c SHA256SUMS
python3 -B -O verify.py
python3 -B -O independent.py
```

These finite checks illustrate the proofs; they are not formalizations or substitutes for the arguments.
