# The local–global conjecture for power-cost scheduling

**Yongxian Zhang.** For a pair of single-machine jobs, suppose putting one immediately before the other strictly reduces the weighted power-of-completion-time cost at *every* start time. Must that order hold in every optimal schedule, even with other jobs in between? Bansal, Dürr, Thang and Vásquez answered yes for convex powers and when the preferred job is shorter. This note proves the remaining case: a concave power and a longer preferred job.

The exchange is concrete. If the inverted pair surrounds a nonempty block of jobs, either swapping the endpoints or putting the entire block before the corrected pair strictly improves the schedule. The result characterizes dominance **of a given pair**. It does not make every locally optimal permutation globally optimal or determine the complexity of finding an optimal permutation.

* [Analytic proof and endpoint conventions](PROOF.md).
* [Sources, adjacent results, and scope of comparison](SOURCES.md).
* [Independent internal review](REVIEW.md). AI-assisted research and internal checking; no external peer review or priority guarantee.
* Run `python -B -O check.py` for [finite exact checks](CHECKS.txt); `sha256sum -c SHA256SUMS` verifies the files. The continuous theorem rests on the proof, not this test grid.
