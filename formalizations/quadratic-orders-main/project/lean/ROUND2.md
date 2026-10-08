# Round2 provenance

This continues the immutable first checkpoint, archive SHA-256
`847e176a0c25b42d3abb2ae6985d408e1ffc8c203e512f931e692828d908e737`.
All new owned sources, builds and evidence are in this new isolated directory.
The installed official Lean compiler is reused. The main project's package
source/cache copy is independent of the first project. Targets.lean, Sieve.lean
and PrimeSupply.lean retain their exact first-checkpoint bytes.

The first checkpoint independently passed a parent review as an explicitly
partial development. That review is evidence of review, not a Lean proof term.
This round again requires fresh compilation and recursive stored-type/body
audit of every safe owned definition/theorem, including generated/private
proofs. Every owned proof module must occur in the audited import closure.

The main project still locks only the nine official mathlib packages at the
reviewed pins. External PNT/class-field proof routes are compiled and audited
in the separately configured relative-path project under
references/upstream/arithmetic-audit; they are not silently imported by
Entry002.lean. Their exact source pins, patches, definitions and trust boundary
are documented in ../ArithmeticSupplyCoverage.md.

MainTarget, PrincipalSplitPrimeSupplyTarget, FiniteSieveTarget and its proved
equivalent FiniteSieveNoWalkTarget are open. A normalized-engine implication
is also conditional: positive rescaling proves the reduction, not the engine.
No GitHub push or publication occurred, and the unrelated mounted repository
was not inspected or modified.

Final verified state: 58 main owned modules freshly compile (3895 jobs);
1942 safe owned logical roots have complete stored-type/body dependency
audits, with only the standard three axioms and no unsafe/partial/missing
dependencies. Two generated Nat projection cached-metadata differences are
explicitly documented without dropping stronger body checks. Separately,
the portable arithmetic verifier passes exact 999-source closure/pins/patch
checks, a 5527-job build, and all 25 strict recursive endpoints. MainTarget,
FiniteSieveTarget, FiniteSieveNoWalkTarget and PrincipalSplitPrimeSupplyTarget
remain OPEN.
