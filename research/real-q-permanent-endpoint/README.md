# A real positive definite counterexample to q-permanent monotonicity on [−1,1]

**Research draft for review, 18 November 2026.** We give a formula for a real symmetric, non-diagonal, positive definite **rational** matrix $A$ and a rational $0<q<1$ for which
$$
P_q(A)>P_1(A)=\operatorname{per}(A).
$$
In particular the failure is a strict decrease between two points in the original interval, not merely equality. The certificate is analytic. Its order is
$$
n=10^{46}\prod_{j=0}^{10000}(10000+j^2).
$$
The integer $n$ itself has **71,503 decimal digits**. Its size and all 10,001 integer multiplicities were checked exactly; the matrix, its permanent, and its full coefficient list were **not** computed. No small or minimal witness is claimed.

### Read the proof

1. [Endpoint identity and existence proof](PROOF.md). Start with a rank-at-most-four Gram matrix of real rows. Express the derivative at 1 through a polynomial norm, then sort the rows to make the derivative negative. Integration uses complex test points; the matrix entries remain real.
2. [Finite rational construction](FINITE.md). Explicit row and multiplicity formulas, deterministic ordering, effective bounds, a positive diagonal perturbation and a concrete rational comparison point. The final positive definite matrix is full rank, not rank four.
3. [Internal audit](REVIEW.md). Independent derivations, possible failure modes, literature comparison, and scope of the computations.

### What this adds and what was already known

[Bapat’s 1992 research problem](https://doi.org/10.1080/03081089208818174) concerns monotonicity on $[-1,1]$. [Bapat and Lal (1994)](https://doi.org/10.1016/0024-3795(94)90497-9) state the strict version for non-diagonal positive definite matrices. [Bapat’s 2007 survey, §6, Conjecture 7](https://www.isid.ac.in/~rbb/imsperm.pdf) states the semidefinite monotonicity version and attributes the problem to the 1992 paper. [Mitchell (2020), Theorem 1](https://files.ele-math.com/articles/oam-14-56.pdf) relates the strict positive definite and singular positive semidefinite formulations.

The universal **complex Hermitian** conjecture was already disproved: [Kitamura’s public formalization](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/tree/4200da4fc1a132d69c23fb877795b5b72089544b) gives an order-144 complex construction, an endpoint-derivative identity using pairs of indices, and a rank-two Fischer-norm calculation. We adapt that endpoint approach; the new construction uses real coefficients and two conjugate maxima of a complex-sphere integral. [Da Fonseca and Goyal (2026), §1 and Corollary 4.4](https://arxiv.org/html/2611.14694v1) already give real PD integer examples with negative derivative at every prescribed $r>1$. Their examples concern the interval extension, not the real case on $[-1,1]$.

This note addresses **real symmetric positive definiteness**, not entrywise positivity. It does not contradict the known nonnegativity of $P_q$ on $[-1,1]$. AI tools assisted the construction, manuscript and a separate internal audit; the new argument has not been externally peer-reviewed or verified by a proof assistant. The literature search was targeted, not exhaustive. No worldwide priority claim is made.

### Run the diagnostics

Python 3, standard library only:
```sh
python3 -B -O verify.py
python3 -B -O audit_real_q.py
```
The scripts compare small exact permutation sums against independently computed coefficient norms, and check rational slack in the large construction. They are diagnostics, not an enumeration of the counterexample or a substitute for the proof.
