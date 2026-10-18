# Genuine general-rank Haar purity

All-rank actual Haar purity is now closed. For every s > 0 and t >= 0,
with D=t+s and g=s*t, the literal Haar average Omega of (P_s/s)^tensor k satisfies

    s^k k^g Tr(Omega^2).re -> s^g * product_{i<s,j<t}(s+j-i).

The new root is `flatHaarAverage_general_purity_scaled_limit`; its premises are
only s,t and s>0. The equivalent-asymptotic form is proved, as is the D,s form
`flatHaarAverage_purity_scaled_limit` for 0<s<=D. No Young decomposition,
spectral certificate, concentration conclusion, or target moment is input.

The proof uses the previously proved actual principal-minor moment product.
For Z=|det U_[s],[s]|^2 and Y=Tr(P_s U P_s U*)/s, actual PSD contractions give
Z<=Y^s and Y<=(s-1+Z)/s. For each N>=1, b=s(N+1), an elementary deterministic
power inequality, proved internally using Bernoulli and geometric sums, gives

    Y^k <= Z^(N floor(k/b)) + r_N^(b floor(k/b)),  0<=r_N<1.

The lower bound uses Z^ceil(k/s)<=Y^k. Integer reindexing, polynomial times
geometric decay, and a parameter squeeze N->infinity then identify the sharp
constant. No probabilistic concentration or uniform-in-N convergence is used.
The exact integral identity connecting Y to actual Haar purity is also proved.

`rankBudget_general_sharp_lower` gives the corresponding sharp leading lower
bound for the actual rankBudgetProjector, from actual rank times purity >=1.
The matching actual general-rank support upper bound, and hence the general
double-moment product limit, remain OPEN. Physical target-uniform minimax also
remains OPEN. The codimension-one double moments are independently complete
in ancestor 3fb6e7469c27f2ca7ac351f07075f6dd85160496.

Lean4.34.1 / Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
Aggregate SchurCompletion + GeneralPurityCheck: PASS 3746 jobs.
Build log: D:/math/tmp/extraction-resume-20261018/build-logs/20261018T155944566849Z-extraction-schur-completion.log.
Selected new roots print only propext, Classical.choice, Quot.sound.
This is BUILD_ONLY, not independent audit. No frozen audit scope was enlarged.
