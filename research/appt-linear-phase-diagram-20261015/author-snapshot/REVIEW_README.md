# APPT linear-order scalar phase package: review status

Author: Yongxian Zhang (张永贤), South China University of Technology.
ORCID 0009-0000-3864-3536; mxymmxym1@gmail.com. No external funding.
OpenAI AI assistants assisted research and writing. Copyright 2026 Yongxian
Zhang; original material all rights reserved, with third-party notices retained.

The four new manuscripts form a complete author-level classification of the
scalar geometry in the APPT linear-order finite-peak window. Ordinary independent
review of these exact frozen inputs is pending. Their status is author-only;
they are not added to a proved index or counted as another major problem solved.
There is no new Lean coverage or changed existing Lean audit scope.

Read [THEOREM_MAP.md](THEOREM_MAP.md) for the exact results and dependencies,
[REPRODUCE.md](REPRODUCE.md) for the standard-library replay, and
[SOURCE_INPUTS.json](SOURCE_INPUTS.json) for the independent input boundary.
All proof, code, certificate and earlier manifest bytes remain frozen. This
README and the accompanying metadata are new files; they do not rewrite old
manuscripts to refer to later results.

The original objects are complex trace-one positive semidefinite density
matrices that remain PPT after **every global unitary**. Dimensions satisfy
2<=m<=n,m->infinity,D=mn. The current spectral window has alpha>1,
alpha/m->c>0 and 3^alpha/D->r in [0,infinity), without an aspect-ratio
restriction. Existing L/V value and S nearoptimizer theorems are credited
scientific inputs, not newly proved results in this package. Their captured
source commit is c4e0d9e713ba349d376469231789bb7b36915b7d; this is a source
snapshot, not a claim that the parallel main branch still has that head.

The complete four-scope reading order is:

1. [LAST_MIXED_BOUNDARY.md](LAST_MIXED_BOUNDARY.md): uniform endpoint exclusion,
   boundary compactness, an interior mixed tie at every positive boundary,
   and actual APPT transfer. It includes its own c>=1 pure-envelope proof.
2. [NO_ISLANDS.md](NO_ISLANDS.md): one initial mixed-c interval (0,c_star),
   one crossing per fixed width, and full pure argmax above the threshold.
3. [CRITICAL_UNIQUENESS_CERTIFICATE.md](CRITICAL_UNIQUENESS_CERTIFICATE.md):
   one nondegenerate interior triple tie, 0.2595<c_star<0.26, and the exact
   local three-branch diagram. Its 73-leaf integer certificate is separate.
4. [GLOBAL_MIXED_PHASE.md](GLOBAL_MIXED_PHASE.md): at every 0<c<c_star one
   unique nondegenerate global mixed maximizer between exactly two unique
   analytic coexistence boundaries; all pure, double and triple ties. Its
   74-leaf certificate covers the entire K=2c interval down to K=0 using
   removable charts. It is an added review scope, not part of an earlier PASS.

The earlier [PURE_ENVELOPE_GE_ONE.md](PURE_ENVELOPE_GE_ONE.md) is a support
input. Parent reported completion of its separate ordinary read together
with the main-line C1/T/B corpus. That report does not approve any of the
four new scopes above; their final exact status comes from the separate
review and metadata binding.

Original actual-spectrum loss conditions are retained: distance of actual
(L,theta) to the complete scalar argmax, middle spread J->0, and actual
peak slack Pi_actual->0. At ties the distance is to the full set; alternation
is allowed. Every scalar maximizer is attained through the credited actual
APPT construction. No empirical law alone is silently substituted for all
three conditions, and no interior peak expansion is used at L=2.

The inherited [README.md](README.md), TARGET.json, discovery JSON and earlier
checkpoints are historical records. For example an early discovery file says
the phase geometry was open at its creation; it remains unchanged. The current
author/review boundary is stated here and in REVIEW_SCOPE.json. The floating
decimal c_star near 0.2596735 is discovery only; the proof enclosure is the
strict rational interval (519/2000,13/50).

Actual exploratory routes and guards are preserved in AUTHOR_ATTEMPT_LEDGER.json.
No unsuccessful mathematical sign assertion or failed control is hidden by
an overwrite; none of the accepted phase-4 controls returned FAIL. The
unrestricted-domain H inference was explicitly rejected and replaced by the
strict admissibility condition v>0. Earlier SC0/FEI/LR0 stages are immutable,
separate and outside this review. Historical source and scope files are not
reclassified as solved broad conjectures.

Not covered: exact finite-dimensional extrema, an all-order spectral rigidity
classification, effective physical dimension thresholds, external human peer
review, a novelty/priority certificate, absolute separability of all competitors,
new preprint submission, email, Release, DOI, or additional Lean claims. Main
publication and repository index changes remain with the root owner.
