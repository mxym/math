# Projection-volume calculus for joins and Cartesian products

**Version 2 — complete written proofs and replayable exact certificates, 7 October 2026.**

Read the [manuscript](paper.md), [proof audit](PROOF_AUDIT.md), and [post-disclosure literature and direction assessment](RESEARCH_LOG.md). The previous [v1.1](../v1.1/) remains unchanged: its optimizer is restricted to products of simplices. This version moves beyond that class rather than revising its correct conclusions.

## Main results

For $R(K)=|\Pi K|/|K|^{d-1}$ and $g(d)=d^d/d!$, we introduce a positive affine invariant $a(K)$ and prove an exact two-invariant calculus for Cartesian products, joins and iterated pyramids. The formulas apply to every full-dimensional convex body. Among polytopes, $a(K)=1/(d+1)$ holds exactly for simplices.

For $\dim A=r$, $\dim B=s$ and $n=r+s+1$,

$$R(A*B)=\frac{g(n)}{g(r)g(s)}R(A)R(B)(a(A)+a(B)),\qquad
 a(A*B)=\frac{a(A)a(B)}{a(A)+a(B)}.$$

Every fixed positive-dimensional body can be replaced by a join of two sufficiently large Cartesian powers having a strictly greater value of $R^{1/d}$. Thus no finite-dimensional body attains the all-dimensional supremum of this root functional, either unrestrictedly or in any product/join-closed class.

For the entire class generated from points by products and joins, the exact maximum equals the simplex value $c_n=(n+1)g(n)$ through dimension thirteen. In dimension fourteen it is exactly $(385/384)c_{14}$, attained by $\mathcal P^6(T_4\times T_4)$. More generally,

$$\frac{R(\mathcal P^{n-8}(T_4\times T_4))}{c_n}
 =\frac{175(n-3)}{128(n+1)}>1\qquad(n\ge14).$$

The self-similar polytopes

$$K_0=T_5,\qquad K_{j+1}=(K_j\times K_j)*(K_j\times K_j)$$

have strictly increasing root values with a limit

$$2.8534<\Lambda<2.8535.$$

An explicit construction in every dimension has this same limiting root and eventually exceeds the complete simplex-product optimum $M_n$ of v1.1 by more than $(203/200)^n$. This compares two precisely specified construction classes; it is not a best-known unrestricted lower-bound claim.

## Replay

Python 3.10 or newer; standard library only. From this directory:

```sh
python3 code/generate.py --output certificates/exact.json
python3 code/check.py certificates/exact.json --self-test --report results/check.json
python3 -O code/check.py certificates/exact.json --self-test --report results/optimized_check.json
```

The certificate producer and checker are separate implementations. The checker does not call the producer or its convex-hull routine. It verifies exact rational hull closure over all ordered operation splits, recipe attainability, and the sharp finite maxima. It also computes all 120 horizontal and 16 lifted maximal minors of the explicit fourteen-dimensional witness, performs fourteen direct smaller-dimensional geometry tests, independently recomputes the self-similar sequence, and checks the large-integer endpoint inequalities at dimension 21845. Four deliberately corrupted certificates must be rejected. Optimized Python mode does not disable any check.

The [certificate](certificates/exact.json) stores the actual rational vertices, recipes and recurrence values. The [report](results/check.json) additionally stores the explicit witness's rational facet data and determinant sums. The [optimized-mode report](results/optimized_check.json) and [run log](results/run.txt) record successful replay. [SHA-256 hashes](MANIFEST.json) pin the release files.

The geometric identities, equality classification, convex-hull induction and infinite tail arguments are written proofs in `paper.md`; they are not replaced by the scripts. Separate exact checking is not external peer review or proof-assistant formalization.

## Prior work and limits

The product identity and simplex values are classical ingredients and were rederived in OpenAI family 088. The v1.1 simplex-product classification is prior work within this repository. Feng, Hu, Liu and Xu already give unrestricted counterexamples in every dimension at least nine; our fourteen-dimensional theorem is a sharp result **within the recursive product/join class**, not an improved unrestricted minimum dimension. Earlier cone studies and affine-invariant projection inequalities are recorded in `RESEARCH_LOG.md`.

The exact supremum of the root functional, the optimal rate in the recursive class, a classification of all fixed-dimensional maximizers, and the equality case of the lower bound for arbitrary nonpolytopal bodies are not claimed. No world-first or journal-tier assertion is made. Authorship: mxym repository account, prepared with AI assistance; no institutional affiliation asserted.

Core proof first publicly disclosed in commit `09c1d3e10839ac76eb3c861472c2ead3a929f1b9`. The finite-class and self-similar proofs, exact data, and equality classification were added in the completing release. The Git history records these distinct disclosure stages.
