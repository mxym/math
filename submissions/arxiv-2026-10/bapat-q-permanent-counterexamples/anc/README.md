# Exact complex witness and two independent checkers

From the extracted source archive, run:

```
python3 anc/verify_recurrence.py
python3 anc/verify_pairs.py
```

Both programs use Python's standard library and exact integer arithmetic.
Run without `-O`; both reject optimized execution to preserve assertion checks.
The second writes `verification_pairs_result.json` next to its source.
The CSV row order is part of the mathematical input and must be preserved.
The paper also prints all 200 tuples. `expected_values.json` records the four
reference integers; the recurrence checker derives its result independently
without reading that file.

The originals are in `notes/bapat-q-permanent-counterexample` in `mxym/math`.
These copies add only an explicit optimized-execution guard. The complete
Lean formalizations and their verification records are linked in the paper.
The real symmetric counterexample is an existence theorem, not this CSV.
