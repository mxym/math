# Actual general-rank physical minimax

This independent package connects the actual general-rank sharp double moments
to the entire physical target profile. It depends on the existing Schur,
MinimaxProfile, and actual LOCC/closure interface packages. It does not modify
their quantum definitions or any frozen audit scope.

`RankBudgetInput D s` is the continuum of actual one-copy PSD trace-one matrices
of rank at most s. `tensorInput` uses the original bipartite tensor regrouping.
`rankBudgetPhysicalMinimax C m n k s K` is the supremum of constants guaranteed
by one fixed physical protocol before every input in that continuum. Each
protocol retains its actual global unitary and actual complete Kraus/PPT data.

The four values of `RankProtocolClass` impose actual product-local Kraus maps,
actual adaptive finite LOCC trees, actual coefficient-topology closure LOCC,
or all completely PPT Kraus channels. The LOCC interfaces are the mature
dependency d3f23c05891482340323726059de9d56a0326dd0, merged normally.
The cPPT minimax is proved equal to the original `MinimaxProfile.minimaxValue`;
the finite local <= finite LOCC <= closure LOCC <= cPPT chain is also proved.

For r=rank(rankBudgetProjector (m*n) k s), a=m^k, b=n^k, N=(mn)^k, define
d as the original integer packing maximum, w=min(a,sqrt(N/r)), and
eta=sqrt(r*Tr(Omega^2).re), with the literal flat Haar average Omega. The finite
physical lower bound uses an actual single product-local protocol constructed
from the actual rank-budget projection. The upper bound integrates each
guarantee over the actual unitary Haar orbit of the flat rank-s density and
applies the original physical cPPT envelope to that actual average.

`rankBudget_physical_relative_bound` proves that the supremum over every
positive integer target K is bounded by

    max (1-d/w) (eta-1).

`rankBudgetPacking_ratio_limit` proves d/w -> 1 from the actual sharp rank
theorem, including n=m*s. For n>m*s the full local dimension becomes feasible;
for n<=m*s the collision width is negligible compared with each local side,
and the original exact integer packing theorem applies. The actual double
moments give eta->1. Therefore `rankBudget_target_uniform_minimax` proves

    sup_{K>=1} |G_C(k,K;s)/min(1,w/K)-1| -> 0

for each of the four actual classes, every 2<=m<=n and 0<s<m*n.
`rankBudget_target_uniform_relative_error` expands the quantifiers explicitly:
for each epsilon>0, eventually in k, the same threshold works for every K>0.
There is no target growth/rate restriction. `rankBudget_full_rank_minimax`
proves the exact boundary G_C(k,K;m*n)=1/K for every k and K>0.

No Young/decomposition, concentration, moment, spectrum or endpoint certificate
is supplied to these final roots. The only abstract helper class premise is
structural inclusion of actual product-local protocols; every final physical
class discharges it internally.

Build with the authorized D-backed serial worker_build.py wrapper, package
formalizations/extraction-schur-completion/physical-minimax, targets
SchurMinimax SchurMinimax.Check. Existing pinned shared dependency links suffice;
the build does not require a new Mathlib source/cache copy.

Lean4.34.1 / Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
Aggregate+Check PASS 3845 jobs.
Log D:/math/tmp/extraction-resume-20261018/build-logs/20261018T164047530039Z-physical-minimax.log.
All nine selected roots in ROOTS_THEOREMS.txt print only propext,
Classical.choice, Quot.sound. Owned sources contain no sorry/admit/new axiom.
SOURCE_SHA256.json hashes owned Lean sources and package configuration.
Status is BUILD_ONLY. Independent audit, integration and manuscript review
are separate root tasks; no publication/push has been performed.
