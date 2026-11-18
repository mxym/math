# Maximum entropy of a bounded integer sum when all but one input are symmetric

For independent variables on the same integer alphabet $\{0,\ldots,r\}$, Kovačević proposed an exact formula for the largest Shannon entropy of their sum. This note proves that formula **when at least $n-1$ of the $n$ input laws are invariant under $x\mapsto r-x$**. The remaining input may have any law. No identical-distribution or full-support assumption is made.

With $H_m=H(\mathrm{Bin}(m,1/2))$ in nats and $H_0=0$, the maximum in this class is

$$
\log\big(e^{H_n}+(r-1)e^{H_{n-1}}\big).
$$

Kovačević's construction, which uses $n-1$ fair endpoint inputs, attains this value. To prove the bound, the note compares all admissible output laws with that construction using a single score. A classical signed-sum inequality controls the score between lattice interfaces. A midpoint inequality handles atoms *on* those interfaces, where a differential-entropy argument alone need not apply.

The unrestricted problem for general $n,r\ge3$ remains open in the literature located here. Earlier unrestricted solutions include $n\le2$ or $r\le2$; there is also an overlapping class allowing up to two inputs to use interior symbols. This is not a claim to an unrestricted solution, a characterization of all equality cases, or priority.

- [Proof](PROOF.md)
- [Prior results and search scope](SOURCES.md)
- [Independent internal review](REVIEW.md)
- [Two reproducible finite checks](CHECKS.md)

AI-assisted research and internal adversarial review; not externally peer reviewed. No third-party paper, code, or license is reproduced or relicensed here.
