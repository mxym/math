# Complete Lean counterexample to Wakhare's entropy-polynomial root conjecture

**Status:** Full Lean 4.34.1 kernel proof of the concrete published counterexample `(k,r)=(11,10)`. Extends the [independently checked, previously unformalized exact manuscript](../../notes/entropy-polynomial-counterexample/README.md) and does not modify or reassign the provenance of that paper.

## The exact conjecture being refuted

Conjecture 2 in Tanay Wakhare's *Iterated Entropy Derivatives and Binary Entropy Inequalities* (Journal of Approximation Theory **307** (2025), article 106143; [arXiv:2312.14743v2](https://arxiv.org/abs/2312.14743)) asserts that for each admissible coprime `k > r ≥ 1`, the polynomial

\[
\begin{split}
 h_{k,s}(x)&=\sum_{j=0}^{k-1}x^{sj}\sum_{v=0}^{j}
     \frac{(-1)^{j-v}}{v+1}\binom{sv+k}{k}\binom{k}{j-v},\\
 p_{k,r}(x)&=\alpha_{k/r}k(1-x^r)^k h_{k,k}(x)
     -r(1-x^k)^k h_{k,r}(x)
\end{split}
\]

has **exactly two zeros** in `(0,1)`, counting multiplicity. Here `α_s>0` solves `α_s(1+α_s)^(s-1)=1`. For the concrete pair `(11,10)`, this is algebraically equivalent (for positive α) to

\[
 \alpha^{10}(1+\alpha)=1.
\]

We construct the actual original two-level binomial sums inside Lean, not an interpolation polynomial or unchecked coefficient table.

## Fully Lean-verified theorem

The unique positive algebraic parameter satisfies

\[
 \frac{117}{125}<\alpha<\frac{937}{1000}.
\]

Lean directly computes all five rigorous **rational** sign certificates at

\[
 \frac15,\quad\frac25,\quad\frac35,\quad\frac23,\quad\frac45,
\]

with alternating signs `+,-,+,-,+`, then applies the intermediate value theorem to the **continuous original polynomial**. The strongest public theorem is:

\[
\boxed{\exists\;0<z_1<z_2<z_3<z_4<1,
\quad p_{11,10}(z_i)=0\quad(i=1,2,3,4).}
\]

This is a **complete refutation** of the two-root assertion, even when roots are counted with multiplicity. It does **not** assert there are exactly four distinct roots, that the parameters are lexicographically minimal, or that the associated binary-entropy inequality is false.

### The exact source-to-theorem chain

The [five owned Lean modules](EntropyWakhare/) and import root [`EntropyWakhare.lean`](EntropyWakhare.lean) establish:

1. **Core:** the *original* nested binomial-sum coefficient `innerCoeff` and original rational functions `hRat`, `A`, `B`, with the required exponents, denominators and binomial coefficients exactly as in the paper.
2. **Signs:** ten exact kernel-checked rational comparisons: the positive `A(x)` at every sample and the five strict bounds separating `B(x)/A(x)` from α.
3. **Alpha:** existence by real IVT, strict rational enclosure, and **uniqueness among every positive solution** of the exact equation `α^10(1+α)=1`.
4. **FourRoots:** equality between rational and real evaluations of the original sums, real-continuity proof, five alternating actual signs, and four **disjoint ordered** IVT root witnesses.
5. **Polynomial:** a genuine `ℝ[X]` polynomial built from the original sum; an exact Lean theorem says its evaluation equals the function proved to have four zeros, yielding `actual_polynomial_has_four_distinct_roots`.

The admissibility `0<10<11` and coprimality of the two integers are Lean-verified. The two-root statement is refuted **at its original algebraic definition**, not merely by evaluating a prefabricated polynomial.

## Reproduction and trust boundary

Use the **fixed** `lean-toolchain` (`leanprover/lean4:v4.34.1`) and `lake-manifest.json` (Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`). From this directory:

```sh
lake exe cache get
bash scripts/replay.sh
(cd . && sha256sum -c SHA256SUMS)
```

The replay script invokes a **clean Lake build**, checks the 12 named theorem roots' axioms, scans every owned proof source for `sorry`/`admit`/`native_decide`/`unsafe`/custom axioms, and requires the Lean kernel to reject an intentionally incorrect `False` proof. The [GitHub Actions workflow](../../.github/workflows/wakhare-entropy-four-roots-lean.yml) runs the same checks using pinned Lean/Mathlib; links to green CI runs are provided only after a real successful run.

The intended trusted base is Lean's small kernel and standard Mathlib definitions. The final theorem reports no `sorryAx` or custom axioms: permitted standard axioms are `propext`, `Classical.choice` and `Quot.sound`. Integer/rational arithmetic is discharged by kernel-checkable `norm_num` proofs, **not** by `native_decide` or external CAS solvers. Real root existence uses the standard Mathlib IVT rather than numerical roots.

[Audit](audit/AUDIT.md) · [Exact source checksums](SHA256SUMS) · [Root axiom inventory](results/axioms.txt) · [Hostile invalid-proof test](audit/InvalidProof.lean).

**Attribution:** The mathematical counterexample and exact integer certificates precede this formalization. This work is AI-assisted and is not external human peer review or a claim of historical priority.
