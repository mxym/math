# Analytic randomness certification with energy-constrained messages and shared entanglement

In the binary-input, binary-output prepare-and-measure model of Ranu, Wooltorton, Abbott and Fawzi (arXiv:2608.27357v1), let w be the common upper bound on each preparation's non-vacuum probability, D = |E_0-E_1|/2, and e = 1 minus Eve's optimal guessing probability on input zero. For normal tensor-product strategies and 0 <= w < 1/3, we prove

    D <= w(5-9w)/(1-w)
         + 2(2-w)(1-3w)/(1-w)^2 * sqrt(e)
         + (1-4w^2/(1-w)^2) * e.

The source's ideal benchmark strictly certifies randomness throughout 0 < w < 1/5, with positive noise tolerance at every such w. This is a sufficient interval and is not claimed to be optimal. At w=19/100, the rational threshold I_corr >= 39/25 certifies e > 1/90000; at w=199/1000, I_corr >= 399/250 certifies e > 1/25000000.

Separately, we show that the source's dimension-independent moment SDP still upper-bounds the guessing probability in the normal infinite-dimensional tensor-product model. This extends the validity of its existing certified bounds, independently of the new analytic witness. The proof also gives a finite-dimensional approximation that exactly preserves the two vacuum probabilities and the common marginal constraint.

See PROOF.md for all claims and hypotheses, SOURCES.md for primary sources and scope, and RESULTS.txt for the expected exact-checker output. Run the two deterministic, Python-standard-library checks with:

    bash replay.sh

These are single-round certification results under the stated energy and isolation model, not statements about arbitrary implementations, finite-round protocols, commuting models without tensor-product structure, or a tight characterization of guessing probabilities.
