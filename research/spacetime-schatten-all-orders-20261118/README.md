# A two-qubit family violating spacetime Schatten subadditivity at every order above one

[Read the proof (PDF)](paper.pdf) · [LaTeX source](paper.tex)

[Milekhin, Adamska and Preskill, Conjecture 1, Eq. (25)](https://arxiv.org/html/2502.12240v2#S4) asks whether the joint spacetime matrix has Schatten norms satisfying
$$
1+\lVert T\rVert_p \ge \lVert \rho_A\rVert_p+\lVert \rho_B\rVert_p.
$$
This is the matrix defined by a time-ordered correlation, not the symmetrized pseudo-density matrix and not an ordinary spatial density matrix.

**Result.** Fix one real unitary on an observed qubit and an environment qubit. The same qubit is observed at both times. For each finite real threshold $p_0>1$, one explicit rational initial weight gives a violation simultaneously for every $p_0\le p\le\infty$. Only the mixture weight changes with the threshold; the unitary and the two product states being mixed stay fixed. The strict witnesses are separable but correlated across the observed qubit and its environment, not product initial states. They do not contradict Theorem 2 of the source paper.

The distinction at order one is sharp. Every physical spacetime matrix satisfies the inequality at $p=1$; no single fixed finite-dimensional matrix violates it along a sequence $p\downarrow1$. Nevertheless, the infimum of all violating exponents is one. With the whole system observed at both times, the inequality holds for all $p\ge1$.

**Prior results.** [The Omega Institute](https://www.trureturing.org/research/milekhin-adamska-preskill-2025-spacetime-schatten-subadditivity/) already gives a three-qubit counterexample at $p=2$, describes its negative Kirkwood–Dirac weight, reports a separate exact but not formalized $p=4$ example, and asks for the infimum of violating exponents. This is not the first counterexample to the original conjecture. The ordinary density-matrix inequality is due to [Audenaert](https://arxiv.org/abs/0705.1276). [Costa Rico and Wolf, Proposition 9](https://arxiv.org/html/2507.18278v1) prove a related inequality for arbitrary matrices with the joint trace norm $\lVert T\rVert_1$ instead of the scalar 1. The present family does not violate that bound.

## Reproduce the algebra

The continuum of exponents is handled by the analytic proof, not by sampling values of $p$. Two independently written scripts check the construction in different ways:

- [check_two_qubits.py](check_two_qubits.py) reconstructs all 16 defining matrix-unit correlations using Python's exact rational arithmetic. It checks the two endpoint branches and a concrete $p=2$ witness at mixing weight $1/8$. Python standard library only.
- [audit_full_swap.py](audit_full_swap.py) constructs the whole-system $16\times16$ spacetime operator and traces out both environmental slots. It verifies the claimed blocks and both marginals for symbolic weight $x$, as well as the Frobenius and trace-norm identities. Requires SymPy (tested with 1.14.0).

From this directory:

```text
python -O check_two_qubits.py
python -O audit_full_swap.py
pdflatex paper.tex
pdflatex paper.tex
```

AI-assisted draft, 18 November 2026. Separately reviewed internally by an AI reviewer; no external peer review or formal proof certification. No claim of historical or worldwide priority.
