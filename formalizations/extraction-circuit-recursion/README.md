# Original-wire occupation recursion

Status: **BUILD_ONLY**. Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

This independent extension leaves the earlier 41-module/227-root
`extraction-circuit-completion` milestone and all older audit scopes unchanged.

`compressionCircuit k` is one literal list of existing-wire one-qubit gates
and CNOTs, on `originalWireCount k = 2*k` original qubits. Its definition
executes the previous circuit on the original suffix and then applies one
common occupation step to the fresh pair and the compact code. The remaining
original wires are spectators. No initialized ancillary input is assumed.

The compiled theorem `compressionCircuit_action` proves the all-k recursion
on every actual normalized `bitOccupation` vector. The previous-stage action
is discharged by induction, including the zero-copy base case.
`compressionCircuit_matrix` and `compressionCircuit_coherent` retain all
coherences. `compressionCircuit_purePower` applies the same word to the actual
unknown iid tensor amplitudes in the explicit original paired-bit convention.

The code occupies a prefix of `2 * clog_4(binomial(k+3,3))` qubits and the
remaining original qubits are zero. `compressionCircuit_length` binds the
actual recursively assembled list length to the sum of stage budgets, and
`compressionCircuit_polynomial_bound` proves the explicit bound

```
20480*k*(k+2)^6*(6*clog_2(k+3)+2)^2 + 100*k^2.
```

The full extraction proposition is still incomplete here: final multiple-Bell
preparation, its physical local discard channel, exact optimal integer yield,
an asymptotic Big-O statement, effective angle evaluation and finite-library
Solovay--Kitaev compilation remain to be connected/proved. The finite embedding
and real gate construction are still `noncomputable`; this package makes no
classical running-time claim.

Reproduction uses the shared pinned dependency without copying Mathlib.
On the current workspace, run the storage-verifying, shared-lock wrapper:

```
wsl -d Ubuntu-22.04 -- python3 /mnt/d/math/tmp/extraction-resume-20261018/worker_build.py /mnt/lean-research-d/worktrees/extraction-lean-protocol-20261016 formalizations/extraction-circuit-recursion
```

The ordinary build passed with 3771 jobs in
`D:/math/tmp/extraction-resume-20261018/build-logs/20261018T145238417719Z-extraction-circuit-recursion.log`.
No independent empty-kernel replay or forged-proof control is claimed.
