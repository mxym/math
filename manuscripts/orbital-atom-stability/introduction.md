# Orbital duality and sharp atom stability for permutation actions

mxym/math research project. AI-assisted manuscript, 7 October 2026.

We determine the best single-atom response to a marginal-preserving signed
perturbation of a uniform finite-group law. A universal orbital primal--dual
theorem reduces the problem to an exact rational linear program on conjugacy
classes. It applies to arbitrary finite actions, including nonfaithful and
nontransitive ones. It gives a sharp formula for doubly transitive actions and
an explicit parity-dependent formula for every symmetric-group action on
two-element subsets. For three-element subsets we give a complete finite
classification for degrees 3 through 120 and separately prove the all-degree
sharp asymptotic coefficient \(1-18/n+O(n^{-2})\). An all-rank short-cycle
transfer theorem gives polynomial-size exact rational optimization at each
fixed subset rank. Four-subset certificates determine every degree 11 through
50; the subset-rank hierarchy and uniform Bernstein limit are also proved.

The full proof of the general principle is in Section 18; Sections 15--17 give
the analytic applications. Sections 19--21 give the three-subset certificate
classification, Section 22 proves its asymptotic, and Section 23 proves the
Bernstein limit. Part J contains the general transfer theorem, rank hierarchy
and the four-subset certificates.
The original connected theorem/section/equation numbering is retained, so that
the independently published certificate documentation remains unambiguous.
Earlier permanent inequalities from the source note are not assumptions of
this paper. The finite-group actions and their familiar minimal degrees are
standard inputs; the orbital optimization and displayed sharp witnesses are
proved below. Ordinary finite-dimensional LP duality is stated and applied to
an explicit bounded feasible polytope, rather than inferred from a solver.

For each three-subset degree, the checker enumerates every conjugacy class,
computes all image-intersection orbital moments, and verifies the rational
primal feasibility, all dual inequalities and equality of objective values.
The published coefficients are optimal in the specified finite ranges. The
three-subset asymptotic is a separate analytic dual bound matched by four
explicit rational primal families; it is not extrapolated from the finite
certificates. A closed exact all-degree three-subset formula, and the proposed
higher-rank \(2k^2/n\) asymptotic, remain open. The two-subset formula is proved
for all degrees analytically; its finite checker is supplementary evidence.

The checkers use Python assertions. The reproduction launcher explicitly
compiles them with assertions enabled even when invoked under `python -O`,
restarting an isolated unoptimized child to preserve imported helper assertions.
An optimized execution that strips those assertions is not accepted as a proof
replay. This paper currently has no Lean formalization. The manuscript is
AI-assisted; external human peer review and literature-wide priority assessment
have not been supplied.
