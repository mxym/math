# Five planar signed steps can reach their root-mean-square radius only 3/16 of the time

[Dvořák and Klein, §7](https://arxiv.org/pdf/2104.10005#page=34) asked whether the scalar bound 7/32 could fail already for vectors in the plane. Yes: take independent fair signs times the following five vectors and divide their sum by √12:

    (0,1), (1,−1), (1,−1), (1,−1), (2,1).

The resulting vector has expected squared Euclidean norm one. Its norm is at least one for exactly 6 of the 32 sign assignments; no norm equals one. Hence **O₂≤3/16<7/32**. With at most four summands the probability is at least 1/4; with at most five it is at least 3/16 in any dimension. Thus 3/16 is sharp for five summands in fixed dimension d≥2. **The unrestricted exact O₂ is not determined.**

The six sign patterns are exactly those of Dvořák and Klein's existing five-step **inner** event in dimension three, after permuting and reversing some signs. The point here is the **outer** realization in dimension two and the finite-length sharpness statement, not a new Boolean pattern or the first failure in some unspecified dimension.

* [Proof, histogram and comparison with Dvořák–Klein](PROOF.md)
* [Literature and scope of priority checks](SOURCES.md)
* [Independent internal review](REVIEW.md) and [reproduction](CHECKS.md)

AI-generated work with independent internal AI review, not external peer review or formal verification. No priority guarantee.
