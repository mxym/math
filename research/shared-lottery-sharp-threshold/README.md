# A sharp application of the Feige bound to a weighted ticket lottery

Yongxian Zhang · research note

In Arnosti and Bonet's weighted individual lottery, fix the requests and scores of all outsiders. When the resulting cutoff satisfies $0<t\le1$, the unique best strategy for the group is for each member to request the entire group's ticket requirement. This settles the conditional conjecture in their paper. For any fixed $t>1$, there are sufficiently large groups whose members can instead make a common smaller request and succeed with probability approaching one. There is no claim about unconditional dominance or efficiency.

The [proof](PROOF.md) applies Fu, Han, Wang, Yan, Zhang and Zhou's 2026 small-deviation theorem to Arnosti and Bonet's Poisson relaxation. Its contribution is the connection between those results, uniqueness in the conditional model, and the sharp uniform cutoff; it does not reprove Feige's inequality. The [source comparison](SOURCES.md) records the two manuscript numberings and nearby cases.

For the finite examples, run `python3 check.py` and compare with [CHECKS.txt](CHECKS.txt). `sha256sum -c SHA256SUMS` verifies file integrity. The general theorem is analytic. This work was AI-assisted and [internally reviewed](REVIEW.md), not externally peer reviewed. No global priority is claimed.
