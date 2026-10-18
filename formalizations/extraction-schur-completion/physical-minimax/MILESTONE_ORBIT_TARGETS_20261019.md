# Actual natural maxima and known-spectrum orbit corollaries

The original operational corollaries now have actual protocol witnesses rather
than a claim of real minimax-supremum attainment. This milestone extends
8804042691968291a3e527a9d468ce4afe48052a and fc8bd54d2dfeca95315404fcc54f4652c754e117.

For every actual class C (product-local, finite LOCC, closure LOCC, cPPT),
`exactRankBudgetTargets` and `errorRankBudgetTargets` contain positive natural
K for which one actual C protocol meets the exact/1-epsilon guarantee for
every actual PSD trace-one one-copy density of rank at most s. Each set is
nonempty and bounded above, and its natural supremum belongs to the set.
`*_isGreatest` records the attained maximum. The exact converse proves the
actual physical effect fixes the entire actual support, including k=0;
minimax value one alone is never treated as an exact protocol witness.

Write D=m*n, r=rank(rankBudgetProjector D k s), g=s*(D-s),
c=sharpSupportConstant s (D-s), d=integer packing, w=min(m^k,sqrt(D^k/r)),
eta=sqrt(r*Tr(Omega^2).re), and beta=1-epsilon. For 0<s<=D,

    d <= K_exact <= floor(w),
    floor(d/beta) <= K_error <= eta*w/beta  (0<=epsilon<1).

For 0<s<D, m<=n, and n<=m*s, the actual exact maximum satisfies

    log K_exact = k/2*log(D/s) - g/2*log k - 1/2*log c + o(1).

The threshold n=m*s is included. For n>m*s it is eventually exactly m^k.
For 2<=m<=n, 0<s<D and fixed 0<=epsilon<1,

    log K_error = log w - log(1-epsilon) + o(1).

`orbitExactTargets C m n k X` uses an arbitrary literal PSD trace-one
matrix X, and asks for exact fidelity on every global one-copy unitary
conjugate of X. Its true natural maximum is attained and obeys the same
d/floor(w) bounds at s=rank(X), the same logarithmic correction, and the
same eventual local-dimension formula. The proof pulls the actual physical
effect through the bipartite tensor transport, applies actual Haar support
exactness, and derives the physical support dimension budget. No restriction
to flat or repeated spectra occurs in these exact orbit results.

Only for the flat rank-s spectrum, `flatOrbitPhysicalMinimax` proves the
entire target-uniform relative minimax profile for the four actual classes.
Its lower bound is an actual common-projection product-local protocol; its
upper bound integrates the literal flat orbit into the actual Haar average.
`flatOrbitErrorTargets` and `flatOrbitErrorMaximum` give actual fixed-error
natural feasibility, nonempty/bounded sets, attainment, and the same log
target formula. No fixed-error/profile assertion for an arbitrary nonuniform
spectrum is made or used.

At full rank s=D, both rank-budget and flat-orbit minimax values are exactly
1/K for every blocklength. Exact rank-budget and arbitrary full-rank orbit
maxima are exactly 1. Fixed-error rank-budget and flat-orbit maxima are
exactly floor(1/(1-epsilon)); their actual protocol witnesses remain part
of the feasibility definitions.

Lean4.34.1 / Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
Authorized D-backed serial wrapper: aggregate + Check + TargetsCheck +
OrbitCheck PASS 3857 jobs. Log:
D:/math/tmp/extraction-resume-20261018/build-logs/20261018T170425019921Z-physical-minimax.log
All 34 listed final roots print only propext, Classical.choice, Quot.sound.
No sorry/admit/new axiom. Sources/configuration are recorded in SOURCE_SHA256.json.
Status BUILD_ONLY; independent audit and manuscript integration are parent tasks.
