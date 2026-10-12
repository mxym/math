# Erdős similarity conjecture: full-case reduction (2026-10-12)

## Problem
For every infinite A subset of R, construct a measurable E of positive Lebesgue measure containing no nontrivial affine copy y+cA, c != 0.

After the standard reductions, it is enough to consider strictly decreasing positive null sequences a_n -> 0.

## Dichotomy reduction
For a decreasing null sequence A, exactly one of the following broad cases applies.

1. Slow-ratio case: a_{n+1}/a_n -> 1. The classical Eigen/Falconer theorem gives a positive-measure avoiding set. This is prior work, not reproved here.

2. Non-slow-ratio case: there is q in (0,1) and infinitely many indices n with a_{n+1} <= q a_n. Choose successive such indices n_j and define b_j=a_{n_j}. Then b_{j+1} <= a_{n_j+1} <= q a_{n_j}=q b_j. Thus B=(b_j) is uniformly q-lacunary.

If E avoids every affine copy of B, then E avoids every affine copy of A, because a copy of A would contain the corresponding copy of the subsequence B. Therefore a full proof reduces to the following unresolved core:

> For every uniformly q-lacunary positive null sequence B, construct a positive-measure set avoiding all affine copies of B.

The exact geometric sequence q^j is only one member of this class. Existing geometric-case work does not automatically transfer to arbitrary variable ratios.

## Why the reduction is not a solution
The lacunarity condition gives z_{j+1}-z_j >= -log_2(q), but allows arbitrarily large and irregular gaps. The current growing-gap theorem instead assumes useful annuli with upper gap o(log log U); a q-lacunary sequence can fail this at every late scale. A naive finite-window blocker also fails when an annulus contains only one or zero usable samples.

A direct random-set proof must control an uncountable parameter family (translation and scale) even when one scale jump leaves no cluster of comparable points. The missing lemma is therefore a variable-ratio lacunary covering/entropy theorem, not a missing Lean wrapper.

## Candidate unified route: spacing-or-filling
A possible route is to abandon the requirement that every logarithmic window contain many samples. At a target exponent window, split the ordered logarithms into:
- filling pieces, where many selected points have bounded local gaps and the existing routing/tree estimate applies;
- spacing pieces, where a very large gap gives a point whose scale offset sweeps many dyadic grid levels as the dilation parameter varies.

The missing technical statement would be a single finite entropy lemma showing that the first regime supplies many independent addresses at one grid scale, while the second supplies enough independent addresses across nested grids, with total exceptional density summable over annuli. This must be proved for arbitrary irregular gaps; merely counting large gaps is insufficient because a fixed parameter does not vary during the hitting event.

## Concrete target lemma
Let b_{j+1} <= q b_j. For each epsilon > 0, prove or disprove the existence of a periodic closed E with density > 1-epsilon such that, for all x in R and t != 0, some j has x+t b_j outside E. A useful proof must specify:

- the finite parameter nets at each scale;
- the treatment of arbitrarily large ratio gaps;
- a summable miss-probability or deterministic blocker estimate;
- a compactness/limit argument over all x,t;
- exact endpoint and sign handling.

Any result covering only q^j, bounded ratio variation, or a prescribed countable family is a partial theorem, not the full conjecture.

## Status
This document records a rigorous reduction and the remaining bottleneck. It is not a proof of the full Erdős similarity conjecture and no release is created from it.
