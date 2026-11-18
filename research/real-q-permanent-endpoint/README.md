# An explicit order and rational witness for the real q-permanent counterexample

**Effective construction, 18 November 2026; historical scope corrected.** The [October 8 existence proof](../../notes/bapat-real-symmetric-existence-counterexample/proof.md) had already disproved real symmetric monotonicity on the original interval. Here the additional result is a formula with all choices fixed for a real symmetric, non-diagonal, positive definite **rational** matrix $A$ and a rational $0<q<1$ for which
$$
P_q(A)>P_1(A)=\operatorname{per}(A).
$$
In particular the failure is a strict decrease between two points in the original interval, not merely equality. The certificate is analytic. Its order is
$$
n=10^{46}\prod_{j=0}^{10000}(10000+j^2).
$$
The integer $n$ itself has **71,503 decimal digits**. The digit count and all 10,001 integer multiplicities were checked exactly; the matrix, its permanent, and its full coefficient list were **not** computed. No small or minimal witness is claimed.

### Read the proof

1. [Endpoint identity and existence proof](PROOF.md). Start with a rank-at-most-four Gram matrix of real rows. Express the derivative at 1 through a polynomial norm, then sort the rows to make the derivative negative. Integration uses complex test points; the matrix entries remain real.
2. [Finite rational construction](FINITE.md). Explicit row and multiplicity formulas, deterministic ordering, effective bounds, a positive diagonal perturbation and a concrete rational comparison point. The final positive definite matrix is full rank, not rank four.
3. [Internal audit](REVIEW.md). Independent derivations, possible failure modes, literature comparison, and scope of the computations.

### The October theorem and the November construction

The [October 8 existence proof](../../notes/bapat-real-symmetric-existence-counterexample/proof.md), §§2–7, proves that **some** order $N>4$ admits a non-diagonal symmetric integer matrix $B$ which is positive definite over the reals, with $P'_1(B)<0$ and a strict decrease between two rational interior points. For this same $B$, continuity gives $P'_t(B)<0$ on a left neighborhood of 1. Hence $P_q(B)>P_1(B)$ for every $q<1$ sufficiently close to 1, in particular for some rational $q$. The endpoint comparison, realness, positive definiteness, and an integer witness in existence are **not** new conclusions of the present note. See also the [October combined manuscript](../../submissions/arxiv-2026-10/bapat-q-permanent-counterexamples/README.md).

Both proofs use real four-coordinate Gram rows, a Fischer/exterior-square endpoint identity, complex-sphere concentration at two conjugate peaks, and row ordering by a real ratio with a complex-Cauchy Gini estimate. October used an equidistributed real sphere cloud, four selector rows and then a sufficiently large contiguous repetition; it left the dimension and witness parameters unspecified. Here a pinned bounded ratio law leads to a weighted finite polar grid, rounded roots of unity and explicit concentration margins. [FINITE.md](FINITE.md) fixes the row count and ordering, rational coordinates, diagonal perturbation and rational comparison point without a “sufficiently large” choice. This is an effective realization of an already known phenomenon, not the first real counterexample. No best dimension or historical priority is asserted.

**Lean scope.** The October [Lean root theorem](../../formalizations/bapat-real-symmetric-existence-counterexample/formalization/sources/BapatIntegerCounterexample.lean) covers existence of an integer matrix with a negative endpoint derivative and a strict decrease at rational interior points (see the [formalization coverage](../../notes/bapat-real-symmetric-existence-counterexample/LEAN_COVERAGE_V1_1.md)). The endpoint comparison above is an immediate mathematical consequence; it is not a claim of a separate Lean execution. The October certificate does **not** verify the November grid, its dimension, any of its constants, the designated matrix or its designated $q$. This effective construction has a written proof and internal AI-assisted checks, not Lean certification or external peer review.

### Other prior work

[Bapat’s 1992 research problem](https://doi.org/10.1080/03081089208818174) concerns monotonicity on $[-1,1]$. [Bapat and Lal (1994)](https://doi.org/10.1016/0024-3795(94)90497-9) state the strict version for non-diagonal positive definite matrices. [Bapat’s 2007 survey, §6, Conjecture 7](https://www.isid.ac.in/~rbb/imsperm.pdf) states the semidefinite monotonicity version and attributes the problem to the 1992 paper. [Mitchell (2020), Theorem 1](https://files.ele-math.com/articles/oam-14-56.pdf) relates the strict positive definite and singular positive semidefinite formulations.

The universal **complex Hermitian** conjecture was already disproved: [Kitamura’s public formalization](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/tree/4200da4fc1a132d69c23fb877795b5b72089544b) gives an order-144 complex construction, an endpoint-derivative identity using pairs of indices, and a rank-two Fischer-norm calculation. Those results concern complex matrices; the October real proof above already used real coefficients and conjugate maxima. [Da Fonseca and Goyal (2026), §1 and Corollary 4.4](https://arxiv.org/html/2611.14694v1) already give real PD integer examples with negative derivative at every prescribed $r>1$. Their examples concern the interval extension, not the real case on $[-1,1]$.

This note addresses **real symmetric positive definiteness**, not entrywise positivity. It does not contradict the known nonnegativity of $P_q$ on $[-1,1]$. AI tools assisted the construction, manuscript and separate internal audit. The initial version of this November note omitted the October repository result; this correction supersedes its incomplete prior-work assessment.

### Run the diagnostics

Python 3, standard library only:
```sh
python3 -B -O verify.py
python3 -B -O audit_real_q.py
```
The scripts compare small exact permutation sums against independently computed coefficient norms, and check rational slack in the large construction. They are diagnostics, not an enumeration of the counterexample or a substitute for the proof.
