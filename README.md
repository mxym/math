# 数学研究 · mxym/math

数学研究论文、完整证明、Lean 形式化与可复现的计算证书。

**张永贤（Yongxian Zhang）** · 华南理工大学计算机科学与工程学院，大二本科生（2026 年 10 月）。

通讯邮箱：[mxymmxym1@gmail.com](mailto:mxymmxym1@gmail.com) · 备用邮箱：[3645500659@qq.com](mailto:3645500659@qq.com)

ORCID：[0009-0000-3864-3536](https://orcid.org/0009-0000-3864-3536) · [完整作者资料与署名模板](AUTHOR.md)

个人独立开展研究，无外部研究经费。使用AI进行辅助研究；各项目公开证明来源、验证范围和复现材料。

[主要论文](#主要论文) · [其他预印本](#其他预印本) · [分类研究目录](RESEARCH.md) · [证明与复现](#证明与复现) · [历史进展](RESEARCH_HISTORY.md)

## 主要论文

目前优先准备向 arXiv 投稿以下两篇。两篇均已在 Zenodo 公开；截至本次整理，尚未向 arXiv 提交。

| 论文与阅读入口 | 已证明的内容 | 验证范围 |
| --- | --- | --- |
| **[Bapat q-永久量单调性猜想的反例](submissions/arxiv-2026-10/bapat-q-permanent-counterexamples/README.md)** · [PDF](submissions/arxiv-2026-10/bapat-q-permanent-counterexamples/paper.pdf) · [DOI](https://doi.org/10.5281/zenodo.23248431) | 原区间内的指定复数有理矩阵反例，以及实对称整数正定矩阵反例的存在性证明 | 两项主结论完整 Lean；实反例尚无显式维数上界或数值矩阵 |
| **[高斯等质量单纯形一阶矩：全部 k](preprints/gaussian-equal-cells-2026-10/README.md)** · [PDF](preprints/gaussian-equal-cells-2026-10/paper.pdf) · [DOI](https://doi.org/10.5281/zenodo.23250730) | 所有 k ≥ 2 的精确上界；维数 d ≥ k−1 时的最优值与全部等号情形，包含分数分区 | 基于已发表高斯多泡定理的完整书面证明；全部 k 的 Lean 主链仍为部分形式化 |

高斯论文在 d < k−1 时证明该上界严格不可达，不声称给出这些固定低维情形的精确最优值。独立三胞 Lean 分支的锐界与等号分类已通过 [完整构建和公理审计](verification/gaussian-three-cell-independent-ci-2026-10-08/README.md)，其范围与全部 k 的形式化分开记录。

## 其他预印本

以下九篇已取得 DOI，其**各自限定的主定理**有完整 Lean 证明。论文中的附带结果、验证版本和定理入口见[完整预印本索引](preprints/lean-certified-2026-10/README.md)。

| 论文 | 主结论范围 | 版本 DOI |
| --- | --- | --- |
| [周期图染色系数的无限对数凹性分类](preprints/lean-certified-2026-10/cycle-chromatic-classification/README.md) | 全部 C_n，n ≥ 3；当且仅当 3 ≤ n ≤ 11 | [23249722](https://doi.org/10.5281/zenodo.23249722) |
| [单纯形稳定性与锐指数](preprints/lean-certified-2026-10/sharp-simplex-stability/README.md) | 所有 d ≥ 3；上界与指数不可改进，常数不声称最优 | [23249732](https://doi.org/10.5281/zenodo.23249732) |
| [二次整环中的有界步长图](preprints/lean-certified-2026-10/quadratic-order-moats/README.md) | 所有二次整环、固定步长界下的分量一致有界 | [23249743](https://doi.org/10.5281/zenodo.23249743) |
| [连续幂渐近的稳健避让](preprints/lean-certified-2026-10/continuum-power-avoidance/README.md) | 给定可数有界对数间隙族的避让定理 | [23249747](https://doi.org/10.5281/zenodo.23249747) |
| [有限群轨道原始—对偶定理](preprints/lean-certified-2026-10/orbital-primal-dual/README.md) | 通用有限作用定理、有理最优证书与锐性 | [23249749](https://doi.org/10.5281/zenodo.23249749) |
| [Wakhare 熵多项式根猜想反例](preprints/lean-certified-2026-10/entropy-polynomial-roots/README.md) | 参数 (11,10) 在 (0,1) 内至少四个不同实根 | [23249754](https://doi.org/10.5281/zenodo.23249754) |
| [单峰 CGF 素数阶因子猜想反例](preprints/lean-certified-2026-10/cyclotomic-unimodal-counterexample/README.md) | 指定 216 次多项式反例，不声称次数最小 | [23249757](https://doi.org/10.5281/zenodo.23249757) |
| [q-永久量半轴单调性反例](preprints/lean-certified-2026-10/q-permanent-halfline/README.md) | 指定实有理 4 × 4 矩阵在 q=49、50 间的反向不等式 | [23249758](https://doi.org/10.5281/zenodo.23249758) |
| [复三行永久量—行列式全参数精确范数](preprints/lean-certified-2026-10/complex-pencil-norm/README.md) | 实际复 3 × 3 矩阵的全参数最优常数 | [23249773](https://doi.org/10.5281/zenodo.23249773) |

半轴反例与 Bapat 原区间猜想是不同命题。Wakhare 新增的[五模块 Lean 工程](formalizations/wakhare-entropy-four-roots-lean/README.md)另有公开记录；上表 DOI 保留其归档时的证明版本。

其他书面证明、精确计算结果和探索项目按领域列在 [RESEARCH.md](RESEARCH.md)，包括置换群、投影体几何、最优传输、分数覆盖、张量刚性及 Ehrhart 实根性。早期编号稿件保留在 [001–009 稿件索引](CONTENTS.md)。

## 证明与复现

本仓库分别标明以下状态，范围以每项成果的具体定理为准：

| 标记 | 含义 |
| --- | --- |
| 完整 Lean | 链接中明确陈述的主定理及其必要依赖已形式化，附版本和验证记录 |
| 完整书面证明 | 论文给出完整推导及明确的已证明外部输入；不以完整 Lean 为发表前提 |
| 部分 Lean／精确证书 | 只覆盖指定引理或计算环节，不自动覆盖整篇论文 |
| 探索中／条件结果 | 猜想、实验或依赖未证明假设的结论另行标明 |

阅读和复现时，从论文入口进入对应的定理、源码与审计文件，按该项目固定版本的命令运行；仓库内不同 Lean 工程不共用一条构建命令。有限计算证书与一般数学证明的作用分别说明。

[完整形式化标准与后续计划](formalizations/MAJOR_RESULT_VERIFICATION_PLAN.md) · [验证记录目录](verification/) · [早期稿件验证汇总](verification/STATUS.md) · [五篇整合稿件](manuscripts/README.md)

## 引用、版本与许可

引用时优先使用相应论文的**版本 DOI**及冻结源提交。后续加强或修正保留旧版本并形成新的公开记录。

- [预印本 DOI 与 BibTeX](preprints/lean-certified-2026-10/README.md#本轮公开-doi) · [高斯修订稿 DOI](https://doi.org/10.5281/zenodo.23250730) · [早期 Release DOI 档案](releases/ZENODO_RECORDS.md)
- [GitHub Releases](https://github.com/mxym/math/releases) · [不可变 Release 工作流](releases/README.md) · [变更记录](CHANGELOG.md) · [整理前的完整首页](RESEARCH_HISTORY.md)
- [来源与权利声明](NOTICE.md) · [OpenAI/math 原许可证](third_party_licenses/openai_math_LICENSE.txt) · [文献比较记录](comparisons/)

仓库公开与 DOI 归档不等于期刊同行评审，也不自动认证原创性或历史优先权。各稿件注明借鉴的公开工作和自身贡献。保留已有许可证及第三方声明；未另行授权的原创材料保留全部权利。
