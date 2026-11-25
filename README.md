# Both border ranks are 30 for Lovitz's 27-variable cubic

**Yongxian Zhang.** AI-assisted proof development and internal verification; no external peer review claimed.

For the specific symmetric tensor constructed in [Benjamin Lovitz, *A 27 x 27 x 27 counterexample to Comon's conjecture*, §4.1](https://arxiv.org/html/2609.28292v1#S4.SS1), we prove over the complex numbers that both its ordinary border rank and its symmetric border rank equal **30**. Thus this tensor is **not** a counterexample to border Comon's conjecture. The general border-rank conjecture is not resolved here. The same two equalities hold for the grid degeneration used in the lower bound.

The main new lower bound uses border apolarity and an explicit solvable symmetry group. If ordinary border rank were at most 29, a fixed apolar ideal would need degree \((2,1,0)\) quotient dimension 29. The first polar prolongation of its pair inverse system instead has dimension at most 28. A limiting construction with 30 cubes gives the matching symmetric upper bound.

- [Ordinary lower bound](ordinary-lower.md): fixed ideals, shear constraints and the first polar prolongation.
- [Symmetric lower bound and grid calculations](lower.md): an independent symmetric obstruction and the exact pure-grid syzygies used in the ordinary proof.
- [Symmetric upper bound and optional Koszul check](upper.md): the 30-cube limiting construction and the earlier lower bound 29 from a flattening.
- Run `python3 apolar-check.py` with SymPy for the exact grid data. The optional `python3 lovitz-koszul.py` needs NumPy. Neither script should be run with assertions disabled.

Lovitz's original ordinary and symmetric ranks, 55 and 56 respectively, are ranks without taking limits and are credited to him.
