# Subset-sum anticoncentration with one rational relation among weight types

Choose each entry of a finite real weight vector independently with probability $1/2$. Write $K$ for the number of distinct resulting sums, and $\rho$ for the largest probability of any one sum. Group weights by nonzero absolute value, not by how many times they occur.

**Theorem.** If there are $s$ weight types and their span over $\mathbb Q$ has dimension at least $s-1$, then $K\rho^2\le1$. Any number of copies of each type is allowed. The same conclusion holds for disjoint blocks of such configurations when their rational spans form a direct sum.

For example, the magnitudes $1,\sqrt2,2+2\sqrt2$ have one independent rational relation, so the result applies to all their multiplicities. Three distinct rational magnitudes, such as $1,2,3$, span dimension one and have *two* independent relations: the theorem does not cover them in general.

[The previous two-magnitude result](../two-weight-subset-sum-anticoncentration/README.md) bounds the support size times the squared peak mass by 1. The present argument needs a stronger local estimate: if two binomial counts are grouped along translates of the integer multiples of any step $(d,e)$, with $de\ne0$, that product is at most $8/9$. Even if the full relation has coprime coordinates, its first two coordinates need not be coprime. Keeping the exact projected step makes it possible to use this estimate for arbitrarily many types.

[Proof](PROOF.md) · [Independent mathematical review](REVIEW.md) · [Prior work and scope](SOURCES.md) · [Integer checks](CHECKS.txt).

This is a special case of the Jain–Sah–Sawhney conjecture, stated by Li as Conjecture 1.1 and communicated to Li by Madiman. The arbitrary-weight problem remains open. AI-assisted research with independent internal AI review; no external peer review, proof-assistant verification, or claim of priority.
