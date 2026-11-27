# 数学研究 · mxym/math

张永贤（Yongxian Zhang）的数学研究仓库：从一个问题出发，读它的证明，查看适用范围，再用公开的代码或证书复核。

[按领域浏览](RESEARCH.md) · [专题成果索引](SOLVED_PROBLEMS.md) · [论文目录](CONTENTS.md) · [English](README.en.md)

<a name="预印本"></a>
<a name="已书面证明的问题"></a>

## 精选成果

| 问题 | 已完成的结论 | 证明与归档 |
| :--- | :--- | :--- |
| **Bapat 的 q-永久量单调性猜想** | 构造一个具体的 200 阶复 Hermitian 正定矩阵，否定原猜想；也证明存在实对称整数反例。两项结论均有完整 Lean 证明。 | [论文与证书](submissions/arxiv-2026-10/bapat-q-permanent-counterexamples/README.md) · [DOI](https://doi.org/10.5281/zenodo.23252928) |
| **量子态的最大纯度** | 对所有 n ≥ 3，求出 3 × n 系统中绝对 PPT（APPT）量子态的最大纯度，并证明该值可以达到。此主定理已用 Lean 核验。 | [论文与形式化](preprints/appt-qutrit-purity-2026-10/README.md) · [DOI](https://doi.org/10.5281/zenodo.23269470) |
| **布尔函数的 Walsh 谱支撑** | 大小为 21 的支撑只有一种仿射形状；从 22 起，每个大小都至少有两种。分类对象是支撑，不是布尔函数本身。 | [冻结版本与复核说明](https://github.com/mxym/math/releases/tag/walsh-support-last-unique-cardinality-v1.0.0) |

<a name="尝试过的问题"></a>

## 开放问题：推进到哪一步？

- **Conway 99 图：**[排除了二阶自同构](research/conway-99-involution/README.md)。这限制了可能的对称性，尚未确定这种图是否存在。
- **六维接吻数：**若一个配置含有同一 D₅ 赤道的 40 个根中的至少 38 个，则总点数不超过 72。[证明与精确复核](https://github.com/mxym/math/blob/71206c3b40a6fd1b16bb8a14cf29ed9b39efbbce/research/euclidean-tensor-geometry/KissingPartialD5D6Equators.md)；不带赤道假设的一般问题仍开放。

[正在更新的研究分支](https://github.com/mxym/math/tree/research/euclidean-tensor-geometry) · [其他探索与未闭合问题](research/research-attempts-20261015/README.md)

## 证明与复现

从专题页开始：先看定理的假设，再按页面说明运行 Lean 工程或精确检查程序。有限计算证书只覆盖所列子问题，不等同于整篇论文已形式化。

[Lean 工程](formalizations/) · [验证记录](verification/) · [改版前的完整中文长目录](https://github.com/mxym/math/blob/1ccc139d8b573f5c71089382718f2ae864214a98/README.md)

## 引用、版本与许可

引用时请使用对应成果的版本 DOI 或冻结提交。[GitHub Releases](https://github.com/mxym/math/releases) · [Zenodo 归档索引](releases/ZENODO_RECORDS.md) · [来源与权利声明](NOTICE.md)。预印本与 DOI 归档不代表已通过同行评审。

[作者资料](AUTHOR.md) · [ORCID](https://orcid.org/0009-0000-3864-3536) · [联系作者](mailto:mxymmxym1@gmail.com)
