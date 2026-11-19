# Internal analytical check: smaller finite-threshold constants

PASS on frozen UNIVERSAL.md SHA-256 `00ecee57b2d15a571a0979d2756cd847cbe1048dab9544a0e8779439f1b0acde`. The 2026 author list, §24, explicitly asks the two existential comparisons and then the smaller-constant question. The result here is existential at a threshold 0<t≤2m, not an asymptotic rate claim.

Absolute continuity gives strict quantile ordering for distinct survival levels, even if the distribution has gaps. Positive survival on every compact interval ensures that a last quantile reaches 2m in finitely many steps. Clipping only this endpoint preserves the total m gained beyond the median. If no successive length exceeded half the previous one, the finite geometric sum would fall strictly short, so the selected length ratio is >1/3.

The rectangle [a,b]×[q_{n+1},∞) and its swap are disjoint up to null sets, and each pair contributes an interval of thresholds of length at least (c−b)/2, because c is the clipped (never larger) quantile. Tonelli then gives the stated numerator integral with product probability 2^(−2n−1); S(t)^2≤2^(2−2n) uniformly on [a,c]. Dividing, averaging and selecting a positive threshold gives a strict lower bound 1/24. The finite upper threshold and m≤2 EX imply both stated normalized constants.

No quantitative growth along thresholds tending to infinity, optimal constants, unconditional density-restricted estimate, external peer review, or priority claim.
