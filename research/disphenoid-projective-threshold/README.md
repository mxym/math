# Exact projective-simulation thresholds for unbiased four-outcome qubit POVMs

Rout, Horodecki and Bhattacharya (arXiv:2611.33559v1, §V) ask for exact
noise thresholds beyond their trine and tetrahedral SIC examples. We
resolve the question for **every unbiased extremal four-outcome qubit
POVM**. This is the full two-parameter family in their Equation (35),
including anisotropic measurements.

Order the three positive coordinate amplitudes \(r_1\ge r_2\ge r_3\),
with \(\sum_i r_i^2=1\). The exact critical white-noise fraction is
\[
 \eta_{\rm crit}=1-\frac1{g(r)^2},\qquad
 g(r)=\begin{cases}
 \sqrt{r_1^2+(r_2+r_3)^2},&r_1\ge r_2+r_3,\\
 (r_1+r_2+r_3)/\sqrt2,&r_1\le r_2+r_3.
 \end{cases}
\]
For example, their \((r_1^2,r_2^2,r_3^2)=(1/2,1/4,1/4)\) instance
has critical noise \(8\sqrt2-11\), about \(0.3137085\), compared to
the original guaranteed fraction \(1/4\). The SIC value \(1/3\)
is recovered.

More generally, a whole class of four-by-four probability matrices
with uniform marginals and three diagonal sign correlations has
exact criteria both for two PS realizations and for realizations
with at least one PS device. The latter gives the exact threshold
above which **both** devices must lie beyond projective simulation;
see Equation (6) for that different threshold. The upper bound uses the
original covariance witness with an optimized outcome encoding;
the lower bound is an explicit independent local simulation using
only qubit projective measurements. The norm \(g\) is the known
2-support norm, not a new norm. The arbitrary biased-outcome case
is not covered.

See [proof](PROOF.md), [sources](SOURCES.md), and [replay](RESULTS.txt).
Run `sh replay.sh` with Python 3 and NumPy.
