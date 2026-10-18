# Actual general-rank sharp double moments

The actual general-rank sharp double moments are closed. For all s>0, t>=0,
D=t+s, g=s*t, and c=sharpSupportConstant s t,

    rank(rankBudgetProjector D k s)/(s^k k^g) -> c,
    s^k k^g Tr((flatHaarAverage D s k)^2).re -> 1/c,
    rank(rankBudgetProjector D k s) * Tr((flatHaarAverage D s k)^2).re -> 1.

Roots: `rankBudget_general_rank_scaled_limit`,
`flatHaarAverage_general_purity_scaled_limit`,
`rankBudget_general_rank_times_purity_limit`.
Rank and purity equivalent-asymptotic forms and D,s forms are proved.
Only dimension, rank, and s>0 are premises. The support and Haar matrices
are literal existing-space constructions. No Young classification, block
multiplicity/dimension certificate, concentration statement, or desired
spectral/moment asymptotic is assumed.

Purity uses actual principal-minor moments, deterministic near-one power
comparison, integer reindexing and a parameter squeeze, as recorded in
MILESTONE_GENERAL_PURITY_20261018.md. That earlier document's open rank
upper and double-moment gaps are superseded by this milestone.

The support upper bound uses a new elementary operator route. For any
PSD contraction G of size s and k<=s*q, cyclically permuting G's eigenvalues
and applying scalar AM-GM on every tensor word proves

    HaarTwirl_s(G^tensor k) >= det(G).re^q I.

The actual canonical compression C* Omega C is fixed by the s-dimensional
twirl because actual copy-permutation intertwiners send the actual large
permutation span to the small one. Integrating the operator bound gives

    C* Omega C >= s^(-k) M(D,s,q) I.

The actual Omega commutes with C C* and every tensor unitary. A putative
positive eigenvector below that scalar must have zero compression after
every unitary. Integrating its actual orbit projections then forces Omega v=0,
a contradiction. Summing the proved positive eigenvalue bounds and using
Tr(Omega)=1 gives the finite bound

    r(D,k,s) <= s^k / M(D,s,ceil(k/s)).

The actual minor asymptotic supplies the matching sharp rank upper bound;
actual rank times purity >=1 supplies the sharp lower bound.

The proof includes full-rank t=0, zero determinant, blocklength k=0, and
all positive ranks; q is an arbitrary natural with k<=s*q in finite lemmas.
General forbidden-descent straightening was also proved, but no automaton
or rectangular-hook count is used in the sharp double moments.

Lean4.34.1 / Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
Aggregate SchurCompletion + GeneralRankCheck PASS 3751 jobs.
Build log D:/math/tmp/extraction-resume-20261018/build-logs/20261018T161827076317Z-extraction-schur-completion.log.
All ten selected operator/rank/product roots print only propext,
Classical.choice, Quot.sound. New files have no sorry/admit/new axioms.
BUILD_ONLY; independent audit remains separate. Existing frozen scopes unchanged.

Remaining scope: connect these actual double moments to the physical
target-uniform minimax statement and manuscript endpoint. Do not label the
complete manuscript fully formalized until that connection is established.
