# Focused prior-work comparison for 005 v4

**Date:** 7 October 2026.
**Purpose:** distinguish the version-4 equality classification from nearby cone-volume and U-functional results. This is a focused comparison, not an exhaustive novelty certification.

## 1. Upstream OpenAI family 088

The pinned upstream manuscript *A product counterexample to the simplex maximum for projection-body volume* (OpenAI family 088, commit \`adc7f1241b42e322a6451854ab7e4b4c146bf78a\`) proves the Cartesian-product identity for normalized projection-body volume, computes simplex values, and obtains product counterexamples. Its source discusses centrally symmetric lower constructions for the unrestricted projection-volume problem, but it does not define the later invariant \(a(K)\), state the symmetric bound \(a(K)\le1/2\), or give the version-4 equality classification.

Entry 005 versions 2--3 explicitly rederive and credit the inherited product and simplex ingredients before introducing the join/cone calculus and the invariant used here.

## 2. Cone-volume subspace concentration

A close conceptual antecedent is:

K. J. Böröczky, E. Lutwak, D. Yang, G. Zhang, *The logarithmic Minkowski problem*, Journal of the American Mathematical Society 26 (2013), 831--852, DOI 10.1090/S0894-0347-2012-00741-3.

For even measures, this work characterizes cone-volume measures of origin-symmetric convex bodies through the subspace concentration condition. In particular, equality in the subspace-mass inequality for a proper subspace forces concentration on that subspace together with a complementary subspace.

That theorem is highly relevant background for any decomposition argument involving cone-volume measures. The mechanism in 005 v4 is nevertheless different in statement and proof: equality in a random-determinant/Rademacher comparison first forces almost-sure circuits of size at most three; a separate Fubini argument converts this into a matching of one- and two-dimensional normal blocks; then a mixed-volume argument identifies the body as a Cartesian product.

## 3. Centered cone-volume measures and the U-functional

A second relevant source is:

K. J. Böröczky, M. Henk, *Cone-volume measure of general centered convex bodies*, Advances in Mathematics 286 (2016), 703--721, DOI 10.1016/j.aim.2015.09.021.

This extends subspace concentration to centered convex bodies and derives a sharp inequality for the Lutwak--Yang--Zhang U-functional. Related stability results appear in:

K. J. Böröczky, M. Henk, *Cone-volume measure and stability*, Advances in Mathematics 306 (2017), 24--50, DOI 10.1016/j.aim.2016.10.005.

The U-functional equality theorem has a parallelotope equality class. That does not match the version-4 class: here every centrally symmetric planar body is an equality factor, so in higher dimensions the equality family contains products of arbitrary centrally symmetric planar bodies as well as intervals. Thus the known U-functional extremum is not an equivalent formulation of Theorem 1.1.

The stability literature may, however, be useful for the next problem: obtaining an effective quantitative bound that measures the distance from \(K\) to the low-dimensional product equality class in terms of \(1/2-a(K)\).

## 4. Search outcome and claim discipline

Focused searches were made for combinations of projection-body volume, pyramids/cones, random determinant/simplex comparisons, cone-volume measures, centrally symmetric equality, and Cartesian-product decompositions. They located the classical cone-volume/subspace-concentration and U-functional literature above, but no exact statement matching
\[
a(K)=\frac12
\quad\Longleftrightarrow\quad
K\ \text{is affinely a product of symmetric factors of dimension at most two}.
\]

Search non-detection is not a novelty proof. The repository therefore makes no claim of first discovery. A full comparison should still inspect MathSciNet/zbMATH, citing papers around the logarithmic Minkowski problem, the cone/pyramid projection-body literature, and random-simplex equality theory.
