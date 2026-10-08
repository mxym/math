# Source screen: prescribed-quota Gaussian centroid ellipsoid

Screen date: 8 October 2026. This is a finite primary-source check, not a
proof review, exhaustive search, or priority claim.

## Candidate statement screened

For a positive mass vector p, let H_p be the interface-area Laplacian of
the regular-simplex Gaussian p-cluster, equivalently the matrix encoded by
the Hessian of the Gaussian multi-bubble perimeter profile. The candidate
inequality is

    tr(B^T H_p^+ B) <= I(p),

for every Gaussian simplex-valued measurable function f with E f=p and
moment rows B_i=E[X f_i(X)], with equality precisely at the translated
regular-simplex winning cells (in ambient dimension at least k-1). It is
also written -sum_a B_{.,a}^T Hess I(p) B_{.,a} <= I(p).

## Closest primary sources and exact scope

1. Emanuel Milman and Joe Neeman, “The Gaussian Double-Bubble and
   Multi-Bubble Conjectures,” *Annals of Mathematics* 195 (2022), no. 1,
   89–206, DOI 10.4007/annals.2022.195.1.2,
   https://doi.org/10.4007/annals.2022.195.1.2, arXiv:1805.10961v3,
   https://arxiv.org/abs/1805.10961. Full text was read from
   `/tmp/1805.10961.pdf/.txt`.

   - Theorem 1.1 proves Gaussian multi-bubble perimeter minimization in its
     stated range q <= n+1 for every positive prescribed mass vector.
   - Introduction equations (1.2)–(1.4), and Proposition 2.4, give the
     model-profile identity `Hess I_model(p) = -H_p^+`.
   - Lemmas 11.1–11.2, printed pp. 56–57, are explicitly for an
     **isoperimetric minimizing Gaussian cluster**. They relate the profile
     Hessian to its perimeter second variation and interface Laplacian.
     Under translations the paper writes `delta_w V=Mw`; it then uses the
     second variation and a matrix Cauchy–Schwarz inequality to classify
     perimeter minimizers.
   - These statements do not assert the candidate inequality for arbitrary
     simplex-valued functions / partitions. The minimizing-cluster
     hypothesis is essential to the stated variation argument.
   - Section 12.4 says a functional version of the Gaussian multi-bubble
     inequality for simplex-valued functions and related directions would
     be described in a work “in preparation.” The checked article supplies
     no statement, citation, or proof of the candidate centroid bound there.

2. Emanuel Milman, “Multi-Bubble Isoperimetric Problems,”
   arXiv:2510.07078v2 (31 July 2026),
   https://arxiv.org/abs/2510.07078. Full text read from
   `/tmp/2510.07078v2.pdf/.txt`.

   Section 8.5, Proposition 8.4, printed pp. 17–18, restates the model
   Gaussian profile PDE
   `tr((-Hess I_model)^(-1)) = 2 I_model`. Sections 8.5–8.6 derive profile
   differential inequalities from variations of perimeter-minimizing
   clusters. The application remains the multi-bubble perimeter profile;
   no arbitrary-partition centroid ellipsoid is stated. A text search of
   this survey found no centroid/first-moment theorem of the screened form.

## Functional-inequality scope and limits

The scalar Gaussian Bobkov/isoperimetric functional inequalities control
perimeter-type gradients and one-cell mass profiles. The multi-bubble
profile Hessian is a finite-dimensional identity for the model perimeter
profile. Neither statement, as written in the primary sources checked,
bounds all first-moment columns B of an arbitrary simplex-valued function.
The Hessian identity alone has no such B in its hypotheses; in the
variation lemmas B-like translation data occur only at perimeter minimizers.

The 2022 paper's “in preparation” citation is not a public primary theorem
that can be checked. Focused arXiv searches for the exact title and for
multi-bubble functional/vector-valued Gaussian inequalities did not return
a later source stating this centroid bound. These non-hits do not establish
that no unpublished or differently titled equivalent theorem exists.

## Limited conclusion

The checked sources contain the exact model-profile Hessian and closely
related second-variation inequalities, but only the latter under the
perimeter-minimizer hypothesis. I found no direct statement in them of
`tr(B^T H_p^+ B) <= I(p)` for every prescribed-quota Gaussian
simplex-valued function. This is a limited source-status finding, not an
open-status or novelty claim.
