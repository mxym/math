# Historical audit-development failures

These are failed runs, not successful completion records. They are retained to
explain the release-validation history without changing any original log.

Run 37961424823 passed all mathematical modules, all endpoint tests, and the full
155,787-declaration trust-zero replay, then timed out in an additional audit
that redundantly replayed the original large proof closure twice. Run 37965996844
again passed that full mathematical replay; its revised additional audit compiled
but failed at invocation because a line break ended the `run_cmd` term too early.
The explicit `run_cmd do` invocation and a fast preflight check correct that
parser issue. The actual mathematical sources are unchanged throughout.

The complete final success record, when present, is in `../complete-v1/`.
The compressed artifact contains the original run 37965996844 records and logs.
The other file contains the original job-level log for run 37961424823.
