# Historical failed audit wrapper: no complete verification claim

Source aa49f7fcf48c22b2ff7111ed6b5df9bd65b43ce2, run 38152532117, job 114508752588.

The fresh Lake build passed 2,844 tasks. Regression compilation passed. The first audit command independently replayed 42,101 declarations and 87 roots at trust level zero, and rejected the forged fixed-local supremum theorem. The overall workflow nevertheless FAILED: the second `run_cmd` expression ended at a newline before its arguments, so Lean reported a command type mismatch and unexpected token. The literal kernel.log records both the successful first audit and the terminal syntax/elaboration failure.

The repair joins the second corruption-control invocation and its arguments on one line. No mathematical module, theorem type, proof term, audit root, timeout or permitted-axiom policy was changed by that repair. The complete independent workflow must pass again at the repaired source before the checkpoint is labeled verified. This directory is retained as failed history and is not evidence of a completed second corruption check.
