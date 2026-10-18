# Concrete Boolean restoring square root

This successor implements restoring square root on LSB-first Boolean lists. Each recursive frame reads two input bits (padding a final single bit with false), forms the candidate remainder 4r+d and threshold 4q+1 with literal list conses, executes the Boolean comparison program once, and conditionally executes the ripple-borrow subtraction program once. It returns the actual root/remainder lists and their comparison/subtraction execution tree. No Nat.sqrt, natural-number division, subtraction, multiplication or comparison computes the output.

The inductive invariant is A = Q^2 + R and R < 2Q+1. It proves that the root equals Nat.sqrt A. The root output width is exactly (input width + 1)/2, and the remainder width is at most input width + 1. The returned trace costs at most 64(input width + 1)^2 in the explicit Boolean/list/record action model: six terminal actions, twenty frame actions, and the actual nested comparison/subtraction trace charges. The cost of evaluating the annotation is excluded. This is not a machine-time assertion.

Nine roots pass narrow guarded author checks. No standard aggregate or independent kernel replay is claimed. All older source and metadata remains byte-identical, and the new module is unused by the separately frozen raw-resource audit closure.

The finite primitive algorithms now cover unsigned comparison, subtraction, division and square root, alongside the earlier Boolean adder and multiplier. A whole-evaluator representation/cost bridge, signed arithmetic, structural allocation/indexing, fuel/counter work, provider/cache construction and explicit fixed-library provider execution costs remain outside these local model theorems. No complete compiler bit-time theorem is asserted.
