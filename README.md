# 数学研究 · mxym/math

张永贤（Yongxian Zhang）的数学研究仓库，收录论文、可复核的证明，以及仍在研究的问题。

**中文** · [English](README.en.md)  
[按领域浏览](RESEARCH.md) · [专题成果索引](SOLVED_PROBLEMS.md) · [论文目录](CONTENTS.md)

<a name="预印本"></a>
<a name="已书面证明的问题"></a>

## 精选成果

| 问题 | 证明了什么？ | 证据 |
| :--- | :--- | :--- |
| **Bapat 的 q-永久量猜想** | q 增大，q-永久量却可能变小。一个明确写出的 200 阶复正定矩阵就推翻了单调性猜想。 | [反例与 Lean 证明](submissions/arxiv-2026-10/bapat-q-permanent-counterexamples/README.md) · [DOI](https://doi.org/10.5281/zenodo.23252928) |
| **量子态的最大纯度** | 对每个 n ≥ 3，求出了 3 × n 系统中绝对 PPT（APPT）量子态的最大纯度，并构造了达到它的状态。 | [论文与主定理的 Lean 证明](preprints/appt-qutrit-purity-2026-10/README.md) · [DOI](https://doi.org/10.5281/zenodo.23269470) |
| **圈图的无限对数凹性** | 圈图的染色多项式系数取绝对值后，恰好在 3 到 11 个顶点时满足无限对数凹性。从 12 个顶点起全部失效。 | [论文与完整分类证明](preprints/lean-certified-2026-10/cycle-chromatic-classification/README.md) · [DOI](https://doi.org/10.5281/zenodo.23249722) |
| **布尔函数的 Walsh 谱支撑** | 把能用仿射变换重合的支撑看作同一种形状。支撑大小为 21 时只有一种；从 22 起，每个大小都至少有两种。 | [定理与冻结版本](https://github.com/mxym/math/releases/tag/walsh-support-last-unique-cardinality-v1.0.0) |

<a name="尝试过的问题"></a>

## 开放问题：推进到哪一步？

- **Conway 99 图是否存在？** [已排除二阶自同构](research/conway-99-involution/README.md)：如果这种图存在，它不可能有连续作用两次就回到原位的非平凡对称。图本身的存在性仍未确定。
- **六维最多能有多少个球同时接触一个同样大的球？** 若接触点已包含同一 D₅ 赤道的 40 个根中的至少 38 个，[总数不超过 72](https://github.com/mxym/math/blob/71206c3b40a6fd1b16bb8a14cf29ed9b39efbbce/research/euclidean-tensor-geometry/KissingPartialD5D6Equators.md)。没有这个假设时，问题仍开放。

[正在更新的研究分支](https://github.com/mxym/math/tree/research/euclidean-tensor-geometry) · [其他探索记录](research/research-attempts-20261015/README.md)

## 证明与复现

想实际跑一次，可以从[圈图 Lean 工程](formalizations/chromatic-cycles-all-n-lean/README.md)开始。在仓库根目录运行：

```sh
cd formalizations/chromatic-cycles-all-n-lean
lake exe cache get
bash scripts/replay.sh
```

[全部 Lean 工程](formalizations/) · [验证记录](verification/)。各专题页标明了验证范围；有限计算证书只覆盖它检查的子问题。

## 引用、版本与许可

引用时请使用对应成果的版本 DOI 或冻结提交。[GitHub Releases](https://github.com/mxym/math/releases) · [Zenodo 归档索引](releases/ZENODO_RECORDS.md) · [来源与权利声明](NOTICE.md)。归档不等于同行评审。

[作者资料](AUTHOR.md) · [ORCID](https://orcid.org/0009-0000-3864-3536) · [联系作者](mailto:mxymmxym1@gmail.com) · [旧版完整中文目录](https://github.com/mxym/math/blob/1ccc139d8b573f5c71089382718f2ae864214a98/README.md)
