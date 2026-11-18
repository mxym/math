# The size and largest atom of a subset-sum distribution with two weight magnitudes

Choose each entry of a finite real vector independently with probability $1/2$ and add the chosen entries. Let $K$ be the number of different sums that can occur, and $\rho$ the largest probability of any one sum.

**Result.** If the vector uses at most two distinct nonzero *absolute* weights, then
$$
K\rho^2\le1.
$$
The inequality is strict unless every weight is zero. The multiplicities are arbitrary, the weights may have either sign, and the ratio of the two magnitudes need not be rational.

[Jain, Sah and Sawhney](https://doi.org/10.19086/aic.24872) conjectured the general trade-off between the number of sums and the largest atom. [Li's Conjecture 1.1](https://arxiv.org/html/2609.01529v2#S1.SS1) states it as $H_0\le2H_\infty$ and credits Madiman for communicating the question. The result here proves only the two-magnitude case. If the two binomial counts give different sums, their probabilities simply multiply. The difficulty is the case of collisions: after rescaling to coprime integer weights, sums with the same value lie in a single residue class in each coordinate. The proof bounds the mass in these classes and counts the number of distinct sums exactly.

[Proof](PROOF.md) · [Independent mathematical review](REVIEW.md) · [Prior results](SOURCES.md) · [Exact integer checks](CHECKS.txt).

AI-assisted research with independent internal AI review. No external peer review, proof-assistant verification, or claim of priority.
