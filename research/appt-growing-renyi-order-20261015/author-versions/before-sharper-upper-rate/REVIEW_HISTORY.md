# Source and ordinary-review history

The initial mathematical source c719b61b25e536d39221ac91a518a1c7c292e2935d2dce75f8de53a20fa480ee,
original map and first actual finite-control PASS are retained. The
independent reviewer found that the fixed-m P2 sentence did not explicitly
require D->infinity. Its literal c=infinity case would allow m=n=2 fixed,
which is false: the exact infinite-order maximum deficit is log2, not log3.
Indeed the two-qubit all-unitary Schmidt witness gives
lambda_1<=lambda_3+2sqrt(lambda_2*lambda_4)<=1-lambda_1,
so lambda_1<=1/2, attained by the normalized I+2|v><v| state.

The manuscript and target map now explicitly require D->infinity in the
fixed-m P2 branch, as in the global P1 regime. This corrects the literal
original corollary range; it is not represented as an unchanged target
or as a theorem for fixed D. P0's every-finite-dimension inequalities and
P1's uniform joint-growth statement are unchanged. The new control adds
the finite-D counterexample, and the revised full source receives its own
binding/run and complete independent read. Original bytes remain in
author-versions/before-fixed-dimension-quantifier-fix/ and the first run.

The initial controls were finite P0/family diagnostics and did not detect
this P2 quantifier error. Their PASS is not claimed to certify the original
entire P2 statement. These are internal AI-agent ordinary reviews and
finite diagnostics, not Lean, external peer review or priority certificates.
