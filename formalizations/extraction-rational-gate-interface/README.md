# Concrete rational SU2 library and actual dyadic provider

This separate author package connects the five-state binary provider to the
existing original numerical compiler interface without altering that interface.
Four gates are constructed as genuine members of SU2: diag(q,qbar) and its
inverse, and [[3/5,4i/5],[4i/5,3/5]] and its inverse, with q=(3+4i)/5.
The explicit label involution swaps0/1 and2/3; rationalGate_inverse proves the
actual group inverse equality. Matrix coordinates are proved exactly.

entryBits performs four actual finite-state coordinate queries and returns
signed little-endian binary lists. dyadicEntry materializes their integer
denotations. dyadicEntry_correct is precisely the existing
CircuitRecursion.DyadicQApproximates statement for each constructed SU2 gate,
including precision0 and all coordinates. Every coordinate list has lengthp;
the four lists and the shared binary denominator have total length5p+1,
excluding signs. This output-volume fact is not an integer-materialization or
provider machine-time bound. Check.lean checks all six named theorem types and
axiom sets and executes the actual integer packet provider on the four labels.

The SU2 matrices are mathematical noncomputable denotations. Neither the
finite-state entryBits program nor dyadicEntry evaluates a real/complex gate.
This is not yet a full universal-library instantiation: dense integer powers
on Circle are proved in the companion provider package, while the final
two-axis SU2 density bridge remains separate. No uniform finite-net discovery,
canonical Word packet adapter cost, all compiler machine time or new
independent empty-kernel audit is claimed. Old frozen manuscript/config/audit
inputs are unchanged. All dependencies, outputs and temporary files use the
verified D-backed data area and shared pinned Mathlib cache.
