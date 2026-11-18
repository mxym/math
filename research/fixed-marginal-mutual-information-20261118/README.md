# Sharp continuity of mutual information when one marginal is fixed

[Read the four-page proof (PDF)](paper.pdf) · [LaTeX source](paper.tex)

Let two bipartite states have the same marginal on A. With trace distance at most δ, how much can their mutual informations differ? Set r equal to the smaller local dimension. For r ≥ 2 the largest difference is

- h(δ) + δ log(r² − 1) for 0 ≤ δ ≤ 1 − 1/r²;
- 2 log r for 1 − 1/r² ≤ δ ≤ 1.

Here h is binary entropy in natural units. For r = 1 the answer is zero. The maximum ranges over common marginals, not over pairs with a single prescribed marginal. Isotropic states attain it. If the other marginal must differ, the same supremum is approached whenever r ≥ 2 and δ > 0.

**What the draft adds.** When the fixed marginal belongs to the larger subsystem, an anchor-dependent product reference gives the exact curve in the *smaller* dimension. The same curve is optimal for the entanglement-assisted classical capacity of channels between every pair of dimensions, with distance measured in half the diamond norm. The text proves sharpness for input dimension larger than output dimension without a divisibility assumption.

**What was known.** [Shirokov (2017), Corollary 1 and Proposition 10](https://arxiv.org/abs/1512.09047) gave a weaker continuity curve already involving the smaller dimension, and used the same isotropic and depolarizing examples. [Berta et al. (2026), Theorem 1.1 and Proposition 3.1 / Remark 3.2](https://arxiv.org/html/2607.24687v2) give the sharp answers when the fixed subsystem or channel input is no larger than the other side. The present proof uses the [max-information dimension estimate of Berta, Christandl and Renner (2011), Lemma B.7](https://arxiv.org/html/0912.3805v3#A2.SS3). It addresses the one-common-marginal question in [Berta, Lami and Tomamichel, § IV](https://arxiv.org/html/2408.15226v2#S4), not their stronger conjecture for unrestricted pairs.

**Review status.** Working draft, 18 November 2026. OpenAI AI assistance was used in developing and drafting the argument and in internal checks. Those checks do not constitute external peer review or formal verification. No historical priority is claimed.

To rebuild in a standard TeX Live installation, run `pdflatex paper.tex` twice in this directory.
