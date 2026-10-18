# Canonical signed Boolean arithmetic

The representation is a Boolean sign and an LSB-first Boolean magnitude. The actual normalizer executes the linear trim program, then tests the returned list constructor to choose false for the sign of zero. It preserves the integer value and produces a canonical magnitude and a unique zero sign. Canonical signed values of absolute value at most 2^B have actual magnitude width at most B+1, so numerical height is not applied to padded inputs without normalization.

The signed adder compares signs; equal signs execute the retained-trace Boolean adder, while unequal signs execute one magnitude comparison and one directed ripple-borrow subtraction. The raw result is stored once, then normalized once. Its value is the integer sum for arbitrary input signs, including unnormalized negative zero. The returned traces have at most 48(maximum input width+2) specified actions. Signed subtraction adds the input with its Boolean sign flipped and charges two further model actions.

The signed multiplier stores the retained-trace schoolbook product once, computes the sign by xor, then normalizes once. Its integer value is the product. When both input widths are at most B, its returned traces and local normalization/sign overhead cost at most 100(B+1)^2 in the explicit Boolean/list/record model. Every arithmetic output is canonical, and each exposes a value-height to width theorem.

These finite local programs and their value/width/execution-tree model proofs have guarded narrow author checks only. No standard aggregate or independent kernel replay is claimed. Every earlier source and metadata file is byte-identical. The frozen raw-resource scope does not import these additions.

The remaining compiler obligations include canonical fraction/packet representation, the whole AST evaluator and selector bridge, structural allocation/indexing, shifts and input conversion/fuel/counter work, provider/cache construction and explicit fixed-library provider execution costs. The trace annotation's own evaluation is excluded. No complete compiler machine-time theorem is asserted.
