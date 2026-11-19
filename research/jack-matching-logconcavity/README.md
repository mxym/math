# Two matching statistics from first-row log-concavity at fixed size

For every fixed n, two different distributions on perfect matchings of [2n] have strictly log-concave counts on their positive support:

1. the **maximum size of a crossing** of arcs (Chen, Conjecture 1.4);
2. the **longest increasing subsequence** of the one-line fixed-point-free involution (Bóna–Lackner–Sagan, Conjecture 4.2).

They already differ on four endpoints: the counts for statistic values 1 and 2 are (2,1) for crossing and (1,2) for LIS. Strictness is only at the interior indices 1<k<n.

The common theorem is that the first row under **fixed-size Jack–Plancherel measure** has a strictly log-concave distribution for every positive Jack parameter. The two matching applications use reciprocal parameters. The proof extends Yupeng Li’s ordered down–up coupling at ordinary Plancherel measure, using classical Jack transition and hook formulas. It is analytical; the finite checks are reproducibility tests, not substitutes for the all-n argument.

See [the proof](PROOF.md), [sources and scope](SOURCES.md), and [internal mathematical review](INTERNAL-REVIEW.md). The proof is the exact reviewed text, including its original private-candidate header. Neither the unrestricted-involution conjecture nor the even-column permutation conjecture with squared tableau weights is asserted.

Run `python3 -B -O verify.py` (Python standard library); compare with [the recorded output](CHECKS.txt). The checker also tests parameter reciprocals and the distinction between the two matching statistics by direct enumeration. Files other than the manifest itself are listed in `SHA256SUMS`.

AI-assisted research draft with internal AI mathematical review. Not externally peer reviewed; dated literature comparisons do not certify priority.
