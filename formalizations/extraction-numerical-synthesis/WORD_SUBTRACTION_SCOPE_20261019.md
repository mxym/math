# Concrete Boolean ripple-borrow subtraction

This successor scope adds one actual algorithm on least-significant-bit-first Boolean lists. Each recursive step computes the three-input full-subtractor Boolean circuit, stores the output digit and borrow, and returns an execution trace. The program does not call natural-number subtraction or comparison to compute its output.

The proofs establish the general modular borrow identity, output width exactly equal to the maximum input width, the final-borrow test, and the ordinary natural-number difference when the initial minuend covers the subtrahend and incoming borrow. The returned branch trace has at most 20(maximum width + 1) actions in the explicit model charging 20 for a digit and 4 for the terminal node. These are specified Boolean/list/record model actions, not a machine-time claim.

Only narrow author checks have been performed for this scope while the separate raw-resource audit is frozen. There is no new aggregate-build or independent-kernel claim. All previously committed source and audit inputs remain byte-identical.

The whole compiler still needs a bridge from its integer operations to these concrete Boolean primitives, including signed arithmetic, division and square root, plus structural allocation, indexing, fuel and counter arithmetic, input/cache construction, and explicit fixed-library provider execution costs. This scope does not close those obligations.
