# 数学研究 · mxym/math

数学研究论文、完整证明、Lean 形式化与可复现的计算证书。

**张永贤（Yongxian Zhang）** · 华南理工大学计算机科学与工程学院，大二本科生（2026 年 10 月）。

通讯邮箱：[mxymmxym1@gmail.com](mailto:mxymmxym1@gmail.com) · 备用邮箱：[3645500659@qq.com](mailto:3645500659@qq.com)

ORCID：[0009-0000-3864-3536](https://orcid.org/0009-0000-3864-3536) · [完整作者资料与署名模板](AUTHOR.md)

个人独立开展研究，无外部研究经费。使用AI进行辅助研究；各项目公开证明来源、验证范围和复现材料。

[预印本](#预印本) · [已宣称解决的问题](#已宣称解决的问题) · [全部专题成果](SOLVED_PROBLEMS.md) · [分类研究目录](RESEARCH.md) · [证明与复现](#证明与复现)

## 预印本

公开论文与研究稿的阅读入口如下。证明状态针对各稿件明确陈述的主结论；具体定理、外部输入和复现方法见对应页面。

| 预印本／研究稿 | 主结论范围 | 证明状态 | 版本 DOI |
| --- | --- | --- | --- |
| [ECQC 满秩极值刚性与纯稳定子完整分类](research/ecqc-stabilizer-saturation/README.md) · [PDF](research/ecqc-stabilizer-saturation/paper.pdf) | 所有奇素数满秩等号态；全部双 qudit 纯稳定子分数；p≡1 mod 4 时全纯态最优比值 p/2 | 完整书面证明、两套精确重放；非完整 Lean | 未分配 |
| [纯态 ECQC：素数维数完整分类](research/ecqc-pure-state-counterexamples/README.md) · [PDF](research/ecqc-pure-state-counterexamples/paper.pdf) | 普遍成立当且仅当 p=2；每个奇素数维数有满 Schmidt 秩纯态反例；三维、五维比值最优 | 完整书面证明、精确证书；未完整 Lean 化 | 未分配 |
| [一般互信息连续性拟议界的三元反例](preprints/mutual-information-continuity-2026-10/README.md) · [PDF](preprints/mutual-information-continuity-2026-10/paper.pdf) | 实际 3×3 概率表；任意小正距离下反驳拟议界，两侧边缘均变化 | 经典反例完整 Lean；量子嵌入及必要系数下界为书面证明 | [23253944](https://doi.org/10.5281/zenodo.23253944) |
| [Bapat q-永久量单调性猜想的反例](submissions/arxiv-2026-10/bapat-q-permanent-counterexamples/README.md) · [PDF](submissions/arxiv-2026-10/bapat-q-permanent-counterexamples/paper.pdf) | 指定复数有理反例与实对称整数反例存在定理 | 两项主结论完整 Lean | [23252928](https://doi.org/10.5281/zenodo.23252928) |
| [高斯等质量单纯形一阶矩：全部 k](preprints/gaussian-equal-cells-2026-10/README.md) · [PDF](preprints/gaussian-equal-cells-2026-10/paper.pdf) | 所有 k ≥ 2 的上界、足够维数下的最优值与等号分类 | 完整书面证明；全部 k 的 Lean 为部分覆盖 | [23250730](https://doi.org/10.5281/zenodo.23250730) |
| [全图强 Chollet 不等式](preprints/all-graph-chollet-2026-10/README.md) · [PDF](preprints/all-graph-chollet-2026-10/paper.pdf) | 任意有限简单无权图、全部主子矩阵，保留原图度数 | [完整 Lean 固定源码](https://github.com/mxym/math/tree/4d2eefd40ee930216ccd8fc0f51e4bf694251967/formalizations/laplacian-chollet-all-graphs-progress) | [23252964](https://doi.org/10.5281/zenodo.23252964) |
| [周期图染色系数的无限对数凹性分类](preprints/lean-certified-2026-10/cycle-chromatic-classification/README.md) | 全部 C_n，n ≥ 3；当且仅当 3 ≤ n ≤ 11 | 完整 Lean | [23249722](https://doi.org/10.5281/zenodo.23249722) |
| [单纯形稳定性与锐指数](preprints/lean-certified-2026-10/sharp-simplex-stability/README.md) | 所有 d ≥ 3；上界与指数不可改进 | 完整 Lean，常数不声称最优 | [23253001](https://doi.org/10.5281/zenodo.23253001) |
| [二次整环中的有界步长图](preprints/lean-certified-2026-10/quadratic-order-moats/README.md) | 所有二次整环、固定步长界下的分量一致有界 | 完整 Lean；不声称有效数值界 | [23249743](https://doi.org/10.5281/zenodo.23249743) |
| [连续幂渐近的稳健避让](preprints/lean-certified-2026-10/continuum-power-avoidance/README.md) | 给定可数有界对数间隙族的避让定理 | 主定理完整 Lean | [23249747](https://doi.org/10.5281/zenodo.23249747) |
| [有限群轨道原始—对偶定理](preprints/lean-certified-2026-10/orbital-primal-dual/README.md) | 通用有限作用定理、有理最优证书与锐性 | 主定理完整 Lean | [23249749](https://doi.org/10.5281/zenodo.23249749) |
| [Wakhare 熵多项式根猜想反例](preprints/lean-certified-2026-10/entropy-polynomial-roots/README.md) | 参数 (11,10) 在 (0,1) 内至少四个不同实根 | 完整 Lean | [23253028](https://doi.org/10.5281/zenodo.23253028) |
| [单峰 CGF 素数阶因子猜想反例](preprints/lean-certified-2026-10/cyclotomic-unimodal-counterexample/README.md) | 指定 216 次多项式反例 | 完整 Lean；不声称次数最小 | [23249757](https://doi.org/10.5281/zenodo.23249757) |
| [q-永久量半轴单调性反例](preprints/lean-certified-2026-10/q-permanent-halfline/README.md) | 指定实有理 4 × 4 矩阵在 q=49、50 间下降 | 指定反例完整 Lean | [23249758](https://doi.org/10.5281/zenodo.23249758) |
| [复三行永久量—行列式全参数精确范数](preprints/lean-certified-2026-10/complex-pencil-norm/README.md) | 实际复 3 × 3 矩阵的全参数最优常数 | 范数主定理完整 Lean | [23249773](https://doi.org/10.5281/zenodo.23249773) |
| [指定置换多面体族的 Ehrhart 实根性](preprints/article-revisions-2026-10/ehrhart-real-rootedness/README.md) · [PDF](preprints/article-revisions-2026-10/ehrhart-real-rootedness/paper.pdf) | (132,213)-避免族全部 d ≥ 3 的结论 | 书面证明与有理证书，引用既有有限范围定理 | [23252971](https://doi.org/10.5281/zenodo.23252971) |
| [指定质量高斯重心椭球不等式](preprints/article-revisions-2026-10/gaussian-prescribed-mass/README.md) · [PDF](preprints/article-revisions-2026-10/gaussian-prescribed-mass/paper.pdf) | 所有正质量向量的质量依赖矩阵度量锐界 | 完整书面证明；部分 Lean | [23252992](https://doi.org/10.5281/zenodo.23252992) |
| [恒等补齐与永久量不等式](preprints/article-revisions-2026-10/permanent-padding/README.md) · [PDF](preprints/article-revisions-2026-10/permanent-padding/paper.pdf) | Pan–Skandera–Wang Conjecture 9.3 | 既有 Theorem 8.18 的书面推论 | [23252976](https://doi.org/10.5281/zenodo.23252976) |
| [归一化永久量余子式谱无界性](preprints/article-revisions-2026-10/cofactor-spectrum-unbounded/README.md) · [PDF](preprints/article-revisions-2026-10/cofactor-spectrum-unbounded/paper.pdf) | 排除任何维数无关的谱比值上界 | 完整书面证明与独立整数证书 | [23252977](https://doi.org/10.5281/zenodo.23252977) |
| [永久量余子式谱的锐渐近](preprints/article-revisions-2026-10/sharp-cofactor-asymptotics/README.md) · [PDF](preprints/article-revisions-2026-10/sharp-cofactor-asymptotics/paper.pdf) | 全大阶对数渐近及秩二 ramp／endpoint limsup 常数 | Theorem 1 完整 Lean；后续 ramp／endpoint 仍为书面证明 | [23255145](https://doi.org/10.5281/zenodo.23255145) |

[九篇完整 Lean 主定理预印本的详细范围与 BibTeX](preprints/lean-certified-2026-10/README.md) · [全部专题稿件](SOLVED_PROBLEMS.md) · [001–009 及扩展索引](CONTENTS.md)

[17 篇稿件的文章与范围审计](reviews/manuscript-quality-2026-10-08/README.md) · [9 篇修订版 DOI 与公开附件核验](releases/manuscript-revisions-20261008/README.md)

余子式谱 Theorem 1 的[完整 Lean 形式化与范围核对](verification/cofactor-spectral-theorem1-lean-2026-10-09/README.md)单独列出；后续 ramp／endpoint 结论不计入该形式化证书。

新增互信息预印本的[版面、来源与冻结证明核对](verification/mutual-information-index-2026-10-08/README.md)及[独立论文 DOI 归档核验](releases/mutual-information-preprint-20261008/README.md)另列，不混入此前 17 篇审计。

## 已宣称解决的问题

以下按仓库公开证明的**实际命题**列出。相同论文可对应多个命题，限定情形与一般猜想分开；此表不自动作出首次解决或历史优先权认定。

| 问题／来源 | 仓库结论及范围 | 证明入口 |
| --- | --- | --- |
| Iqbal ECQC Conjecture 3.1 的纯态问题（arXiv:2509.08286v2 Section 5） | 素数维数中仅 p=2 普遍成立；p=3 即有精确一比特超出，奇素数反例完整覆盖；此前一般混合态反例另行致谢 | [完整证明、定义、文献范围与重放](research/ecqc-pure-state-counterexamples/README.md) |
| Berta–Lami–Tomamichel，arXiv:2408.15226v2 Eq. (106) 的一般互信息连续性拟议界 | 反例；任意小正距离均存在，两侧边缘均变化；固定一侧边缘版本未解决 | [署名论文与完整经典 Lean 范围](preprints/mutual-information-continuity-2026-10/README.md) |
| Bapat 原区间 q-永久量单调性猜想 | 反例；复 Hermitian 版本及实对称限制均不成立，实反例为有限存在性结论 | [合并证明与完整 Lean](submissions/arxiv-2026-10/bapat-q-permanent-counterexamples/README.md) |
| da Fonseca 半轴 q-永久量单调性扩展 | 反例；4 阶最小，书面证明另给出每个 t > 1 的负导数族 | [书面证明](notes/q-permanent-halfline-counterexample/README.md)；指定矩阵完整 Lean |
| Wakhare Conjecture 2 的“两内部根”断言 | 反例；(11,10) 至少四个不同内部根，不涉及另一熵不等式 | [完整 Lean](formalizations/wakhare-entropy-four-roots-lean/README.md) |
| Billey–Swanson Conjecture 48 | 反例；非恒定基本单峰 CGF 可没有任何素数阶圆分因子 | [完整 Lean](formalizations/cyclotomic-prime-factor-counterexample/README.md) |
| Amdeberhan–Moll Conjecture 21／早期 Conjecture 13.1 | 一般染色系数无限对数凹性断言被 C17 反驳；周期图族另有完整分类 | [反例](notes/chromatic-infinite-logconcavity-counterexample/README.md)；[全周期图 Lean 分类](formalizations/chromatic-cycles-all-n-lean/README.md) |
| Heilman 2014 Conjecture 3 | 证明；四个等质量高斯单元在三维的正四面体极值及等号分类 | [全部 k 的书面证明](preprints/gaussian-equal-cells-2026-10/README.md) |
| Heilman 2019 Conjecture 1.16 的等质量子情形 | 证明；覆盖所有 k，达到等号要求 d ≥ k−1，低维仅得严格上界 | [书面证明与部分 Lean 范围](preprints/gaussian-equal-cells-2026-10/README.md) |
| Heilman 2019 Conjecture 1.16 的任意质量原表述 | 反例；指定四胞非均匀质量族的正四面体模型严格非最优 | [完整书面反例](research/gaussian-fixed-mass-propeller-counterexample/README.md) |
| de Castro Conjecture 10.1，arXiv:2609.06096v1 | 证明；指定避免置换多面体族全部 d ≥ 3 的实根性，结合既有 d ≤ 1000 定理 | [书面证明与精确证书](notes/ehrhart-uniform-real-rootedness/README.md) |
| Pant–Singh Section 6 的全图强／self-Chollet 问题 | 证明并加强到全部主子矩阵；仅限有限简单无权图 Laplacian | [完整论文](preprints/all-graph-chollet-2026-10/README.md)；[完整 Lean](https://github.com/mxym/math/tree/4d2eefd40ee930216ccd8fc0f51e4bf694251967/formalizations/laplacian-chollet-all-graphs-progress) |
| Pan–Skandera–Wang Conjecture 9.3 | 证明；由原作者 Theorem 8.18 经恒等补齐直接推出 | [完整书面推导](notes/permanent-inequality-padding/README.md) |
| Burgin–Goldberg–Keleti–MacMahon–Wang Question 1，arXiv:2210.09284v1 | 对该版本的全比值仿射几何序列问题给出否定回答；不声称其在本工作前仍未解决 | [来源说明](notes/continuum-power-avoidance/README.md)；[完整 Lean 几何避让](formalizations/geometric-avoidance/README.md) |

此外，仓库已证明通用有限群对偶、全固定秩 Chebyshev 锐渐近、全子集秩 5/14 精确值、锐单纯形稳定指数、递归投影体层级及首个嵌套维数、有限筛 minimax 与最优界等专题结果。全部入口按领域列在 [已证明专题清单](SOLVED_PROBLEMS.md)。一般 PSD Chollet、正相关高斯噪声稳定性、完整 Erdős 相似性猜想、Ryser rank-six 等未解决目标仍单独标明。

## 证明与复现

[复四行永久量—行列式锐界及全实参数范数](formalizations/four-row-permanent-tradeoff/README.md)新增完整主结论 Lean：实际复矩阵的普遍不等式、最优常数和上确界均已证明。本轮重新编译 6 个模块，空内核 trust level 0 重放 67 个自有声明及 14,151 个依赖声明；全等号分类等未覆盖内容单独披露。

“完整 Lean”只适用于所列具体定理；部分引理、有限证书和成功构建不自动覆盖整篇论文。完整书面证明可使用明确引用的已证明定理，完整 Lean 不是公开该证明的前提。

全图强 Chollet 的固定源码记录了 83 模块 fresh 编译、985 个自有声明与 44,173 个传递依赖的空内核 trust level 0 重放。本次索引更新核对了全部源码哈希及复核记录，未重跑该 Lean 工程：[核对记录](verification/chollet-all-graphs-index-2026-10-08.json)。高斯三胞独立分支的[完整构建与公理审计](verification/gaussian-three-cell-independent-ci-2026-10-08/README.md)不代表全部 k 已形式化。

余子式谱 Theorem 1 的公开记录报告 78 个模块、745 个自有声明及 55,731 个传递依赖的空内核 trust level 0 重放，仅出现 `propext`、`Classical.choice`、`Quot.sound`；本轮索引核对公开记录，未重新执行 Lean：[核对记录](verification/cofactor-spectral-theorem1-lean-2026-10-09/README.md)。

互信息经典反例的既有独立复核覆盖 38 个自有声明与 16,161 个依赖，包含真实概率表的独立语义核对；本次核对源码和复核记录，并下载核验两个不可变 Release 的 13 个附件，未重新执行 Lean 重放。量子对角嵌入与必要主导系数至少 2 仍为书面证明。

[形式化标准](formalizations/MAJOR_RESULT_VERIFICATION_PLAN.md) · [验证记录](verification/) · [分类研究目录](RESEARCH.md) · [五篇整合稿](manuscripts/README.md)

各项目使用自己的固定源码、工具链和复现命令。有限计算与一般证明的作用分别说明；条件结论明确列出未证明假设。

## 引用、版本与许可

引用时使用对应版本 DOI 及冻结源提交。后续修正或加强形成新版本并保留原记录。

[DOI 与 BibTeX](preprints/lean-certified-2026-10/README.md#本轮公开-doi) · [Release DOI 档案](releases/ZENODO_RECORDS.md) · [GitHub Releases](https://github.com/mxym/math/releases) · [不可变 Release 工作流](releases/README.md) · [变更记录](CHANGELOG.md) · [历史进展](RESEARCH_HISTORY.md)

[来源与权利声明](NOTICE.md) · [OpenAI/math 原许可证](third_party_licenses/openai_math_LICENSE.txt) · [文献比较](comparisons/)

公开稿件与 DOI 不等于期刊同行评审，也不自动认证原创性或历史优先权。各稿件注明借鉴的公开工作和自身贡献。保留已有许可证及第三方声明；未另行授权的原创材料保留全部权利。
