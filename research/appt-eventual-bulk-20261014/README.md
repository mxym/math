# Exact eventual fixed-local APPT bulk entropy

[PAPER.md](PAPER.md) and [THEOREM_MAP.md](THEOREM_MAP.md) prove the actual
APPT minimum and all equality spectra at sufficiently large D for each
fixedm>=3 and every order in a fixed compact positive interval. The result
also holds for all a<=alpha<=c lnD, a>0 andc<1/ln(m-1).
Each minimizer is(I+tP)/(D+tk), with its rank selected by comparing the
two integers adjacent to the exact continuous stationary rank.
On compact positive intervals, the entropy loss from rank rounding is
J_alpha dist(D theta_alpha,Z)^2/(2D^2)+O(D^-3).

This is the same APPT research direction, not another independent major
conjecture. The scalar spectra and vonNeumann stationary rank are credited
in [LITERATURE.md](LITERATURE.md). The leading logarithmic coefficient here
is sharp for the one-halfspace relaxation; its winning single spike above
that coefficient is explicitly nonAPPT. It is not a physical phase threshold.

Ordinary written proof only; no new Lean or extension of existing audits.
Fixedm and a positive lower order bound are essential to the stated scope.
Arbitrary finite dimensions, joint growingm, the smallest onset and
ASEP bulk attainment remain separate. Internal independent AI reading
is disclosed in the review files when completed, not human peer review.

`python3 check_bulk.py --out diagnostics.json` (also with`-O`) checks finite
rational vertices, scalar identities, actual negativePPT controls and
finite order/dimension comparisons. Smaller relaxation failures are retained:
no effective finite threshold is inferred from passing larger samples.
The diagnostics are one implementation and do not certify the infinite proof.

Yongxian Zhang, SCUT, mxymmxym1@gmail.com, ORCID0009-0000-3864-3536.
No external funding. OpenAI AI assistants assisted.
All rights reserved for original material; third-party rights retained.
