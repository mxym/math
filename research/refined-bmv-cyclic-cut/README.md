# When does clustering increase a two-letter word trace?

Research draft, 18 November 2026. **Internal AI review only; no external peer review, proof-assistant formalization, or claim of priority.**

Given a cyclic product of positive powers of two positive semidefinite matrices, when is its absolute trace always at most that of the product with like powers collected? The proposed answer is a finite cut test. Give each boundary between an X-run and a Y-run capacity 1/2. The comparison holds for all matrix sizes exactly when the normalized exponent of each run can be distributed across its two boundaries without violating a capacity. Outside this region the positive real trace ratio is unbounded already for real positive definite matrices of size three.

For four factors the closed diamond is sharp in the *open* unit square of exponents; on every edge of the square a zero power collapses the word and gives equality. The positive diamond is [Ando–Hiai–Okubo’s Corollary 2.2](https://files.ele-math.com/articles/mia-03-32.pdf#page=5). The negative side addresses the [Carlen–Lieb sharpness question](https://arxiv.org/pdf/2203.06136#page=12), not the first failure of the unrestricted inequality.

For the **clustered upper bound only** in [Open Quantum Problem 40](https://oqp.iqoqi.oeaw.ac.at/refinement-of-the-bessis-moussa-villani-conjecture), average over the traces of all words containing n copies of A and m of B, each with the same weight. For positive integers n and m, the proposed criterion for this average never to exceed Tr(AⁿBᵐ) is

$$
\frac{1}{n}+\frac{1}{m}\ge\frac12.
$$

The least failing total length is nine, at (4,5) and (5,4). The averaged upper bound was already disproved by [Cha–Lee](https://arxiv.org/html/2603.19927v5) for all n,m ≥ 5. Our proof uses their projection-walk and bridge mechanisms; it is not a new discovery of the general counterexample. The sufficient single-word bound follows from the 2000 theorem of Ando, Hiai and Okubo after cyclic splitting. What is classified here is the complementary necessity and the full integer threshold. The separate lower bound by a trace exponential is not decided.

* [Proof and endpoint conventions](PROOF.md)
* [Prior art and search limits](PRIOR.md)
* [Independent internal review](REVIEW.md)
* [Verification output](CHECKS.txt)

Run both exact checkers with a standard Python 3 interpreter:

```sh
python3 -B -O verify.py
python3 -B -O independent.py
sha256sum -c SHA256SUMS
```

These finite calculations test the proof and do not replace the all-dimensional argument.
