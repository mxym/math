# Symmetric border rank 30 for Lovitz's 27-variable cubic

**Yongxian Zhang.** AI-assisted proof development and internal verification; no external peer review claimed.

For the specific symmetric tensor constructed in [Lovitz, *A 27 x 27 x 27 counterexample to Comon's conjecture*, §4.1](https://arxiv.org/html/2609.28292v1#S4.SS1), we prove over the complex numbers that the symmetric border rank equals **30**. The ordinary border rank is either **29 or 30**. This does not resolve border Comon's conjecture, which is a question about equality of these two border ranks, not the ordinary-rank statement settled in Lovitz's paper.

- [Upper bound and ordinary lower certificate](upper.md): a 30-cube limiting construction and a Koszul flattening.
- [Symmetric lower bound](lower.md): a degeneration and [Buczyńska–Buczyński's border apolarity](https://arxiv.org/abs/1910.01944). The argument excludes any torus-homogeneous apolar ideal with the degree-one through degree-three Hilbert dimensions of 29 generic points.
- The exact checkers use NumPy for the modular Koszul elimination and SymPy for the apolar product dimensions and local syzygy certificate. Run `python3 lovitz-koszul.py` and `python3 apolar-check.py` without disabling assertions.

Lovitz's original exact ranks 55 and 56 are different invariants and are credited to him. No claim is made about general symmetric tensors or the ordinary border rank beyond the stated interval.
