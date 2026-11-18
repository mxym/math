# Complementary quantum correlations: a five-dimensional discrimination bound and a qubit–qutrit state class

**Research draft for review · 18 November 2026.** For two local measurement settings, each a rank-one projective measurement in a basis mutually unbiased to the other local basis, write the complementary quantum correlations (CQC) gap as
$$
G=I(A:B)_\rho-I(Z_A:Z_B)-I(X_A:X_B).
$$
The first information is quantum, the other two are classical. CQC means $G\ge0$. A pair of local bases in dimension $d$ is mutually unbiased (MUB) if every squared cross-overlap is $1/d$. Logarithms in this note are natural.

1. **A sufficient bound in dimension five.** For any two density matrices and any MUB pair on $\mathbb C^5$, the sum $S$ of their two measured triangular discriminations obeys $S\le 53/14<3.8265583$. This meets the sufficient target in [Qian, §11(3)](https://arxiv.org/html/2608.14806v2#S11). For [Qian’s particular state family (8)](https://arxiv.org/html/2608.14806v2#S6.SS1), with equal priors, prescribed Alice rays and orthogonal Bob rays, it gives $G>3/1000$ nats. The sharper radical upper bound from the same argument is $3.76964420135\ldots$; it is not claimed to be optimal. [Derivation and exact constants](FIVE.md).
2. **A sufficient state condition in dimension $2\times3$.** For *any* two local MUB pairs, $G\ge0$ whenever the joint state is classical on at least one subsystem (has zero discord on that side). Its classical basis need not be measured. Thus any qubit–qutrit counterexample would have nonzero discord on *both* sides, which need not mean entanglement. There is no rank or probability restriction within the stated class. [Proof, including the qubit information-exclusion region](THREE.md).

**What remains open.** These are not proofs of CQC for general $2\times3$ states or of the proposed sharp five-dimensional value $(14+2\sqrt5)/5$. Unrestricted $2\times5$ CQC is already false. No stronger entanglement or nonlocality conclusion follows.

**中文摘要。** 五维两组互无偏基的三角判别量之和不超过 $53/14$，足以回答 Qian §11(3) 的充分界问题；在 $2\times5$ 系统上，CQC 的推论仅针对 Qian 式 (8) 指定的双分支态。另证 $2\times3$ 系统上一侧量子失协为零的态在任意局部互无偏基对下满足 CQC，无须测量经典记录基。一般 $2\times3$ 及五维锐常数均未解决。

## Relation to earlier work

* [Schneeloch, Broadbent and Howell (2014)](https://doi.org/10.1103/PhysRevA.90.062119) proposed CQC and proved cases including pure states, a maximally mixed marginal and a minimally disturbing measurement. Existence of an **unmeasured** classical record basis does not imply that a specified measurement has that alignment. [Iqbal (2026), Proposition 3](https://link.springer.com/article/10.1007/s11128-026-05258-2) gives another sufficient condition using information lost under the chosen readouts.
* [Wang, Wang and Chen, arXiv:2608.03828v3](https://arxiv.org/abs/2608.03828v3) give classical–classical counterexamples for equal local dimensions $d\ge3$. [Their qubit paper, Eq. (2) and Appendix B](https://arxiv.org/html/2608.04916v1) proves CQC for all two-qubit states and gives an asymmetric qubit Holevo bound with weights $(1,1/2)$. Our qubit curvature argument follows their Jensen-gap method and establishes the larger sufficient polygon used here.
* [Qian, arXiv:2608.14806v2](https://arxiv.org/html/2608.14806v2), §§6–7 and 11, gives the entropy reduction for (8), a certified $2\times3$ family bound, a five-dimensional attained discrimination value and a separate $2\times5$ counterexample. It distinguishes an upper bound sufficient for (8) from the sharp five-dimensional optimization. We use that entropy reduction, not the later counterexample, to deduce the family corollary.
* The November [*Sharp qutrit discrimination and unavoidable correlation overcounting for complementary measurements*](https://www.evidencepress.org/releases/qutrit-complementary-discrimination/) ([archived candidate](https://doi.org/10.5281/zenodo.23933731)) reports the **sharp qutrit value $8/3$**, a stronger positive gap on the smaller $2\times3$ family (8), and separable violations for every prescribed MUB pair on $2\times n$ for $n\ge4$. Our $2\times3$ result widens the **state class**, not that sharper gap or the sharp qutrit constant; the five-dimensional calculation is for a restricted family as far as CQC is concerned.
* The [Haagerup classification, as summarized by Tadej and Życzkowski](https://arxiv.org/abs/quant-ph/0512154), supplies the five-dimensional Fourier normal form. [Puchała, Rudnicki and Życzkowski](https://arxiv.org/abs/1304.7755) use submatrix singular values in majorization uncertainty relations. Threshold decompositions of divergences are classical; see [Sason](https://arxiv.org/abs/1804.06334). For the KL contraction by the total-variation row diameter, see [Cohen et al.](https://doi.org/10.1016/0024-3795(93)90331-H). Neither these general tools nor Qian’s known extremizing candidate are attributed to this note.

## Reproducing and interpreting the checks

From this directory:

```sh
python3 verify.py
python3 check_independent.py
```

* `verify.py` uses only the Python standard library. It computes rational Bernstein coefficients, rational radical majorants, the envelope integral, and rational enclosures for the entropy-gap inequality. No floating-point output is a proof premise.
* `check_independent.py` is a second implementation requiring SymPy and NumPy (replayed with Python 3.12.14, SymPy 1.14.0, NumPy 2.3.5). It uses exact Sturm chains instead of Bernstein coefficients, symbolic determinant checks, and an independent rational trapezoid sum. It also checks all 1,024 pairs of Fourier subset projections **numerically**; this corroborates, but does not replace, the analytic rank analysis in FIVE.md.
* Research, drafting, code, and an independent internal adversarial rederivation were AI-assisted. There has been **no external peer review or proof-assistant verification**. A targeted check of the cited primary papers, their references and public searches through 18 November 2026 did not find these precise two results; this is not a guarantee of priority. Sources are linked, not redistributed. No submission, release or DOI for this draft is claimed.
