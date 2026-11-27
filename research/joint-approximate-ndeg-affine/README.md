# Sharp affine endpoints of joint approximate nondeterministic degree

An affine polynomial may nearly vanish on one Boolean label and have magnitude at least one on the other. How many variables can matter if there are such witnesses for both labels?

For witness errors \(\epsilon_0,\epsilon_1\in[0,1)\), put \(L_b=1+\lfloor 2\epsilon_b/(1-\epsilon_b)\rfloor\). The exact maximum, both for relevant-variable count and deterministic decision-tree depth, is \(L_0+L_1\). The proof decomposes one \(2m\)-vertex cycle into monotone chains in two different coordinate orientations. The bound is attained for every pair of errors, including zero and phase boundaries.

With one affine witness and an arbitrary degree-\(d\) witness for the opposite label, we prove a quadratic-in-\(d\) junta bound. This order is sharp for each fixed positive error on the degree-\(d\) side, using the standard endpoint approximation for OR. If that side is exact instead, the sharp maximum is \(2d+L_1-1\). Separately, for every symmetric Boolean function, a run-length argument gives \(D=O_\epsilon(\min(d_0,d_1)\max(d_0,d_1)^2)\) for two witness degrees \(d_0,d_1\).

These are restricted-case results for Kothari–Kovacs-Deak–Wang–Yang v3 Conjecture 3, not a proof for arbitrary Boolean functions. The note also distinguishes that conjecture from the two differently formulated Pednekar–Podder v1 conjectures.

Run `sh replay.sh | diff -u RESULTS.txt -` with Python 3. The first checker uses exact rational witnesses and adaptive minimax; the independent checker uses bounded affine-family enumeration, actual matching-product spans on slabs, and Hamming-run restrictions.
