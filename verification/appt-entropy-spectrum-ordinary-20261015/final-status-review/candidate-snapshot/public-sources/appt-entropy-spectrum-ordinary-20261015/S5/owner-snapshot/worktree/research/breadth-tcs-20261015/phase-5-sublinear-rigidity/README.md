# Growing sublinear APPT spectral rigidity, every aspect ratio

Author: Yongxian Zhang (张永贤), South China University of Technology.
ORCID 0009-0000-3864-3536; mxymmxym1@gmail.com. No external funding.
OpenAI AI assistants assisted. Original material all rights reserved, with
third-party attribution and notices retained.

Status: complete author manuscript [PAPER.md](PAPER.md), pending a new full
independent ordinary read. This is one further APPT depth result, not a new
major-problem count, Lean theorem, publication or broadened prior audit.

The complete original domain is complex trace-one PSD densities that remain
PPT after every global unitary, 2<=m<=n,m->infinity,alpha->infinity,
alpha/m->0. All n>=m and all oscillating peak/bulk ratios are allowed.
The max-value theorem G1 is credited existing work. The new scope is every
actual nearoptimizing spectrum at the first-nonzero moment-excess and
relative entropy-deficit scales.

The manuscript retains the actual peak loss h=alpha log(u_D/y_1) and the
actual bulk defect d_b=(2-L)+|theta-1/2|+J. Their two contributions enter
as a weighted sum, not a choice of one branch. Entropy replaces h by
h/(1+chi_plus) and needs its own large-peak-log proof. Theorem C supplies
W_2 body-law equivalence only where the physical bulk weight is retained;
Corollary D retains the physical peak/width compatibility margin.

[THEOREM_MAP.md](THEOREM_MAP.md) gives the full range and proof chain.
[LOCAL_COVERAGE_MAP.md](LOCAL_COVERAGE_MAP.md) records the previous ranges
actually checked to avoid duplicate work. SOURCE_INPUTS.json binds 15
complete locally read scientific manuscripts at captured main commit
1c76bb8dd03bb622e8ed1eabbe88e8abc5b3e59f. That is the source snapshot,
not a statement that main remains at that head. The four phase-4 scalar
manuscripts are not dependencies and their review does not cover this scope.

Author controls use only Python standard-library Fraction and integer
arithmetic. Copy PAPER.md and author_exact_controls.py to a private scratch
directory and run `python author_exact_controls.py`. Expected: 18 finite
physical regressions, all requested assertions passed. They check wrong-min,
omitted-J, actual mean-centering and vanishing-weight pitfalls. They are
finite supporting evidence, not the all-state proof or an independent PASS.

Natural logarithms and every real order in the asymptotic range are part
of the theorem; integer-order controls do not restrict it. The phase-5
ordinary review must read the whole proof, exact source boundaries and
the weighted loss/large-log arguments. It must keep all earlier Lean,
priority, external human review, submission, email, DOI and Release scopes
unchanged. Remaining changing-order regimes are explicitly outside this note.
