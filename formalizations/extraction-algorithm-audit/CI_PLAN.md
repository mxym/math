# New hosted workflow plan

The new extraction-algorithm.workflow.yml template is an independent added-scope adaptation of the already frozen completion workflow. Parent installs it as a new file; no old workflow is edited. The mathematical/manuscript source head excludes that future installed path, so startup binds the owned frozen template and requires byte equality with the actual installed workflow. CI_CONTEXT records both path and hash. Push paths and manual dispatch are supported.

The driver pins Lean4.34.1, Mathlibd13f23b7 and the same checked official Lean/Lake Linux executable hashes; actions and the elan installer ref are immutable. Local execution always validates the D-backed image; explicit CI mode requires hosted Linux/X64 context, exact event-SHA checkout and exclusive runner-temp directories, and is rejected on WSL even with spoofed environment flags. It records available RAM/disk and fails below the selected minimum.

Hosted execution fresh-builds only the two new mathematical packages and this audit package against the pinned dependency cache. It prints all735 kinds/types/axioms, executes the bounded syntax probe, replays the whole actual new-root closure at trust0 and tests all65 exact same-type proof substitutions after positive type-dependency replay. It rechecks source/tool/old605+4378/archive hashes before and after.

The independent download job verifies every artifact byte, the exact checkout/run ID, the complete ordered stage list, true fresh status, exact positive roots/closure count, allowed axioms, all65 named rejections and their type closures, the exact bound AuditInvocation, execution hashes and actual workflow-template equality. The120-minute runner timeout and7200-second replay limit are conservative. No hosted CI PASS is claimed in advance.

The older completion workflow has its own broad formalizations push trigger. A future parent push may independently trigger that preserved job too; this template does not disable or rewrite it.
