# Internal proof audit and exact evidence

Status: complete written proof plus a **partial** standalone
Lean 4 kernel formalization for Boolean code isometry.
This is not a formalization of Gaussian probability theory.

## Analytic quantifier and proof audit

1. Every bound allows ALL measurable equal-mass Gaussian
   k-partitions, up to null sets, including arbitrary
   cell geometry. Optimizer attainment is not assumed.
2. The a_i are conditional Gaussian centroid lengths,
   not cell first-moment norms; they are related by
   a_i=k||b_i||. Then kP = (sum_i a_i^2)/k.
   The dispersion V is the empirical variance of a_i,
   and the identity k(U-P)+V=h_k^2-(mean a)^2
   is exact (no asymptotic or inequality).
3. Choosing unit directions along b_i gives
   E max_i <u_i,G> >= sum_i||b_i||=mean a.
   This holds even when individual b_i vanish.
4. A Gaussian spherical cap union bound applies to
   ANY unit directions. Its integrated prefactor
   yields E max <= s+d/((d-1)s) when the explicitly
   defined cap envelope B(s)<=1.
   The expected spherical maximum is nonnegative,
   allowing multiplication by E||G||<=sqrt d.
5. Both mean a and cap H(s) are nonnegative, so
   (mean a)^2<=H(s)^2, yielding the exact
   variance-corrected cap transfer.
6. For L=log k>=100 and d>=L^2/logL, the prior
   exact threshold with s²=2L-logL-2L²/d+16
   yields B(s)<1 and H(s)^2<=2L-logL-2L²/d+24.
   Mills gives h_k²>=2L-logL-4; subtraction gives
   the claimed 2L²/d-28 **without halving**.
7. For d/L²->c, retaining -logL-log4pi in the
   threshold yields H(s)^2=h_k²-2L²/d+eta+o(1).
   Taking eta down to zero gives 2/c.
   All error terms are uniform under the fixed c
   hypothesis and are proved in the published
   sharp-dimension-rate companion.
8. If a Gaussian orthogonal group maps cells
   transitively, Gaussian invariance gives
   b_(gA)=g b_A, so all ||b_i|| are equal and V=0.
   **No converse of this statement is assumed**.
9. Near-global C/k accuracy and regular-simplex
   normal-max Gumbel comparison yield
   k(U-P)<=C+2(1-gamma)+o(1).
   Combining with the variance-corrected bound gives
   V>=max(0,2/c-C-2(1-gamma))-o(1).
10. Every a_i and their mean lie in [0,h_k].
    Splitting the variance sum at sqrt(v0/2)
    implies at least v0*k/(2h_k²) exceptional
    cells, asymptotic to v0*k/(4log k).
11. The forced nonhomogeneity is a statement
    about any sufficiently accurate partition,
    not a proof that every exact optimizer is
    symmetry broken for all k or d.

## Lean kernel checks

The module formal/GaussianCodeCore.lean imports Init.
It proves the binary coordinate dot homomorphism
under vector XOR, Boolean-sign multiplicativity,
the code sign-twist action, and exact preservation
of the sum of coordinate squares by arbitrary
sign-diagonal transforms. It needs no imported
Gaussian measure theory.

It compiles with Lean 4.34.1; #print axioms reports
only [propext] or [propext, Quot.sound], which are
Lean standard logical axioms. No custom axiom,
sorry, unsafe term substitution, or admit is used.
The checked formal module **does not** claim to
prove the Gaussian measure transformation
or the spherical cap bound.

## Exact rational checker

The Python standard library Fraction checker
confirms the algebraic variance and support
implications for 17 finite rational norm profiles,
including homogeneous and highly heterogeneous
cases up to k=1024.

A deliberately heterogeneous algebraic profile
demonstrates that omitting V from the cap-transfer
inequality can fail. It is **not** claimed to
be realizable by a two-cell Gaussian partition,
which would have equal and opposite moments.

The universal inequalities are derived
analytically in paper.md, never inferred from
these finite demonstrations.

## Outstanding research

- Prove or disprove asymptotic centroid-length
  homogeneity for actual dimension-constrained
  Gaussian partition optimizers.
- Identify the sharp fixed-C dimension coefficient
  and whether it differs between general
  partitions and symmetric constructions.
- Extend Lean formalization to the Gaussian
  integrals, spherical marginal density and
  the full cap theorem.
- Complete independent mathematical
  originality checking against quantitative
  Gaussian width and vector-quantization literature.
