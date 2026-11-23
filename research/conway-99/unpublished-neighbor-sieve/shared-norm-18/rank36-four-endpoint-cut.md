# Fano endpoint intersections exclude one more four-type support at rank 36

At Seidel rank 36, the four types neutral norm 20, unit neutral norm 26, and unit \((1,25),(3,37)\) cannot be the only present types among the twelve selected types. This leaves at most eleven exactly-four-type possibilities after the [preceding bounds](rank36-four-orthogonal-cut.md). It does not exclude rank 36 or address feasibility with more than four types.

## A dot-one pair forces norm 24

Every norm-14 Fano line has two endpoint 22-cocliques: its two positive/negative seven-sets adjoined to the same anticomplete fifteen-set. Their indicators differ by the Fano marking, up to its sign. By the [endpoint-partner theorem](../../marked-coset-shells/README.md), a 22-coclique has at most one partner meeting it in fifteen sites. Thus different Fano lines give disjoint pairs of endpoint cocliques.

For two different Fano lines form their \(2\times 2\) endpoint intersection matrix. Every row and column, up to order, is in the published list
\[
\{(0,2),(1,1),(3,6),(6,10),(4,5),(7,9),(9,14)\}.
\]
Its alternating sum is the dot product of the two oriented Fano markings. Checking the finite list of matrices, an absolute alternating sum of one forces the sorted entries \(3,6,6,10\). Thus each absolute-dot-one line pair gives one unordered coclique pair meeting in ten sites. Distinct line pairs give distinct such endpoint pairs by endpoint-partner uniqueness. By [graph-wide coclique difference uniqueness](global-coclique-sidon.md), their two ordered differences are distinct neutral unit norm-24 fields. If \(m_1\) counts absolute-dot-one pairs of Fano lines, this proves \(2m_1\le N_{24}\), without a rank hypothesis. The companion checker independently enumerates the matrices.

## Nonorthogonal pairs and the exact certificate

Write \(N=N_{14}\) for the number of oriented Fano markings and \(m_k\) for the number of unordered Fano line pairs with absolute dot \(k\). The possible values are \(0,1,2,4\) by [Fano difference packing](fano-difference-packing.md). The orthogonality graph on \(N/2\) lines is triangle-free by the [three-Fano exclusion](../README.md#three-orthogonal-fano-configurations-cannot-coexist). The elementary triangle-free edge bound therefore gives
\[
16(m_1+m_2+m_4)\ge N^2-4N.
\]
Apply the tangent \(N^2\ge100N-2500\). The [orthogonal Fano transport](rank36-four-orthogonal-cut.md) also gives \(4m_0\le2402S\) in the averaged rank-36 notation, where \(S\) is the mean compatible unit \((1,23)\) count. Summing all line pairs gives \(2402S+4(m_1+m_2+m_4)\ge N(N-2)/2\); use its tangent at 50 as well. The endpoint inequality is written \(2402W_{0,24}-2m_1\ge0\), since norm 24 is nonisotropic and the graph-wide count is \(2402W_{0,24}\).

The [exact checker](rank36_four_endpoint_cut.py) adds these three nonnegative slacks to the [published baseline](rank36-four-fano-palette-cut.md). It verifies a positive integer combination of 19 nonnegative rows equal to \(-11,913,036\) on the specified face. It uses no A8, higher-harmonic-tail, or new positive multiplicity assumption. Run `python3 rank36_four_endpoint_cut.py` in this directory with python-flint. No optimizer is used.
