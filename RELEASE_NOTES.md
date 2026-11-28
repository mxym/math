# Source-slice notes

- Research source fixed at `cbecb11223e799366a55cb3f22572197961593e4`. The manuscript and checker are kept byte for byte. The author-external replay is separately authored and also has its original bytes.
- The author-side verifier computes the coefficients of the first five generators both by actual subsets and separate cycle formulas, checks the two conjugacy orbits under \(A_6\), verifies all 720 monomial coefficients and checks the stated matching counts.
- The independent audit checked the analytic PSD and matching bounds and rebuilt the finite table by a two-state transfer matrix on each cycle. It derived the already standard split trace independently using the Frobenius formula and character orthogonality. Both ordinary-mode scripts passed.
- Only the degree-eight split characters have the stated strict \(S/10\) deficit. All seven irreducibles of \(A_6\) satisfy the non-strict inequality. This is the natural degree-six action, not a claim about all subgroups.
- [MANIFEST.sha256](MANIFEST.sha256) covers all files except itself.
