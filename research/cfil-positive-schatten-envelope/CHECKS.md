# Reproduction and limits of the checks

Run in this folder using Python 3, NumPy, and mpmath:

```sh
python -B verify.py
python -B -O verify.py
python -B verify_independent.py
```

The first two runs produced:

    EXACT: Tr A²B²=14351; shuffle(2,2)=40624/3; commutator norm²=4858; 143 sharp triples
    NUMERICAL: 1248 matrix/exponent trials (545 near equality); 312 sharp fixtures

The exact endpoint check is symbolic in origin. For Hermitian A,B, the symmetrized average of the six (2,2) words is W=(4 Tr A²B²+2 Tr ABAB)/6, while Tr A²B²−W=‖AB−BA‖₂²/6. Thus the direction in (9) is correct and can be strict; the coefficient of s²t² in Tr(e^(−sA)e^(−tB))−Tr e^(−sA−tB) is ‖AB−BA‖₂²/24. The code checks these identities by enumerating words over integer matrices, and checks the sharp-diagonal parameterization with rational Pythagorean data. The stress trials compare the actual matrix Schatten norms with (1) and (2), including singular, complex, near-equal, unequal-norm, and zero examples. Finite trials cannot verify an all-exponent theorem. The analytic proof in README.md is the evidence for the universal assertion.

The same endpoint computation gives a useful additional consistency check: if finite matrices A,B do not commute, the GT difference inside (5) has positive fourth-order coefficient in h (at any fixed s,t>0); hence it is positive for sufficiently small h>0. Consequently L(s,t)>0 for all s,t>0, and (9) is strict for 1<r,l<2. For p=4 strictness is directly the displayed fourth-moment commutator expression. Thus in finite dimension the sharp upper envelope (1) is strict on noncommuting pairs for 2<p≤4, and then for all p>2 by doubling, since if A²,B² commute, so do their positive square roots. This is not needed in the proof of (1).

The separate independent script, which uses closed-form rank-one pencil eigenvalues rather than the first program or a numerical eigensolver, produced:

    closed-form envelope comparisons: 1152 ; two-projector GT comparisons: 150 ; precision: 80 decimal digits

These high-precision comparisons are numerical, not interval certificates. The mathematical argument establishes the stated all-exponent result; the checks are designed to catch sign, normalization and endpoint mistakes.
