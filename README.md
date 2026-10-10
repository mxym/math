# 数学研究 · mxym/math

[English README](README.en.md)

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
| [qutrit–qudit APPT 最大纯度](preprints/appt-qutrit-purity-2026-10/README.md) · [PDF](preprints/appt-qutrit-purity-2026-10/main.pdf) | 所有 n≥3 的绝对 PPT qutrit–qudit 态纯度精确最大值，并证明实际取到 | 主 APPT 定理完整 Lean；绝对可分态推论为独立书面证明 | [23269470](https://doi.org/10.5281/zenodo.23269470) |
| [APPT 纯度：qutrit 精确定理与高维渐近律](preprints/appt-purity-unified-2026-10/README.md) · [PDF](preprints/appt-purity-unified-2026-10/main.pdf) | 合并 qutrit–qudit 精确最大值、一般维数反例、全域渐近律及充分长方形区间的精确最大值与极值谱分类 | qutrit 主定理完整 Lean；高维部分为书面解析证明与精确 checker | — |
| [四个等质量高斯单元：协方差变形与四面体刚性](preprints/gaussian-four-cell-global-2026-10/README.md) · [PDF](preprints/gaussian-four-cell-global-2026-10/paper.pdf) | 所有 d≥3 的全局锐界与正四面体等号分类；Heilman 2014 Conjecture 3 的三维情形 | 完整书面证明；有限精确诊断与部分 Lean，解析端点未形式化 | [23272806](https://doi.org/10.5281/zenodo.23272806) |
| [Erdős 相似性的增长对数间隙扩展](preprints/erdos-similarity-growing-gaps-2026-10/README.md) · [PDF](preprints/erdos-similarity-growing-gaps-2026-10/paper.pdf) | 对满足晚期环带填充条件的一类序列证明正测度仿射非普适性，含相邻比值趋零与间歇环带例子 | 完整书面证明；有限精确诊断与部分 Lean，完整 Erdős 猜想仍开放 | [23272807](https://doi.org/10.5281/zenodo.23272807) |
| [图态 MMI 禁止子图定理](preprints/graph-state-mmi-forbidden-subgraph-2026-10/README.md) · [PDF](preprints/graph-state-mmi-forbidden-subgraph-2026-10/paper.pdf) | 证明 Fuentes–Keeler–Munizzi–Pollack Conjecture 1；无爪 vertex-minor 分类与七顶点连通阈值 | 完整书面证明与双独立精确 checker；未完整 Lean 化 | [23272728](https://doi.org/10.5281/zenodo.23272728) |
| [全图强 Chollet 不等式](preprints/all-graph-chollet-2026-10/README.md) · [PDF](preprints/all-graph-chollet-2026-10/paper.pdf) | 任意有限简单无权图、全部主子矩阵，保留原图度数 | [完整 Lean 固定源码](https://github.com/mxym/math/tree/4d2eefd40ee930216ccd8fc0f51e4bf694251967/formalizations/laplacian-chollet-all-graphs-progress) | [23252964](https://doi.org/10.5281/zenodo.23252964) |
| [纯态 ECQC：素数维数完整分类](research/ecqc-pure-state-counterexamples/README.md) · [PDF](research/ecqc-pure-state-counterexamples/paper.pdf) | 普遍成立当且仅当 p=2；每个奇素数维数有满 Schmidt 秩纯态反例；三维、五维比值最优 | 三维真实量子反例[完整 Lean 与空内核重放](formalizations/ecqc-pure-qutrit-counterexample/README.md)；全分类未整体 Lean 化 | [23256948](https://doi.org/10.5281/zenodo.23256948) |
| [高斯等质量单纯形一阶矩：全部 k](preprints/gaussian-equal-cells-2026-10/README.md) · [PDF](preprints/gaussian-equal-cells-2026-10/paper.pdf) | 所有 k ≥ 2 的上界、足够维数下的最优值与等号分类 | 完整书面证明；全部 k 的 Lean 为部分覆盖 | [23250730](https://doi.org/10.5281/zenodo.23250730) |
| [高斯固定质量正四面体猜想反例](preprints/gaussian-fixed-mass-propeller-counterexample-2026-10/README.md) · [PDF](preprints/gaussian-fixed-mass-propeller-counterexample-2026-10/paper.pdf) | 对每个 0<p<1/4 的四胞质量族严格否定正四面体最优性；等质量情形不受影响 | 完整书面反例；精确 Q(√2) 诊断与部分 Lean，几何端点未完整形式化 | [23272917](https://doi.org/10.5281/zenodo.23272917) |
| [全整数高斯维数阶](preprints/gaussian-quadratic-dimension-all-k-2026-10/README.md) · [PDF](preprints/gaussian-quadratic-dimension-all-k-2026-10/paper.pdf) | 对所有充分大的整数 k 建立匹配的 Θ((log k)^2) 维数阶 | 完整书面证明、Berry–Esseen 外部定理和精确复核；非 Lean 完整化 | [23273190](https://doi.org/10.5281/zenodo.23273190) |
| [ECQC 满秩极值刚性与纯稳定子完整分类](research/ecqc-stabilizer-saturation/README.md) · [PDF](research/ecqc-stabilizer-saturation/paper.pdf) | 所有奇素数满秩等号态；全部双 qudit 纯稳定子分数；p≡1 mod 4 时全纯态最优比值 p/2 | 完整书面证明、两套精确重放；非完整 Lean | [23256934](https://doi.org/10.5281/zenodo.23256934) |
| [高斯维数—精度常数精化](preprints/gaussian-sharp-dimension-rate-2026-10/README.md) · [PDF](preprints/gaussian-sharp-dimension-rate-2026-10/paper.pdf) | 给出误差与 log² k 维数系数的显式权衡及球冠常数精化 | 完整书面证明与精确复核；非 Lean 完整化 | [23273299](https://doi.org/10.5281/zenodo.23273299) |
| [一般互信息连续性拟议界的三元反例](preprints/mutual-information-continuity-2026-10/README.md) · [PDF](preprints/mutual-information-continuity-2026-10/paper.pdf) | 实际 3×3 概率表；任意小正距离下反驳拟议界，两侧边缘均变化 | 经典反例完整 Lean；量子嵌入及必要系数下界为书面证明 | [23253944](https://doi.org/10.5281/zenodo.23253944) |
| [单纯形稳定性与锐指数](preprints/lean-certified-2026-10/sharp-simplex-stability/README.md) | 所有 d ≥ 3；上界与指数不可改进 | 完整 Lean，常数不声称最优 | [23253001](https://doi.org/10.5281/zenodo.23253001) |
| [指定质量高斯重心椭球不等式](preprints/article-revisions-2026-10/gaussian-prescribed-mass/README.md) · [PDF](preprints/article-revisions-2026-10/gaussian-prescribed-mass/paper.pdf) | 所有正质量向量的质量依赖矩阵度量锐界 | 完整书面证明；部分 Lean | [23252992](https://doi.org/10.5281/zenodo.23252992) |
| [高斯球冠维数下界](preprints/gaussian-spherical-cap-converse-2026-10/README.md) · [PDF](preprints/gaussian-spherical-cap-converse-2026-10/paper.pdf) | 证明加性 O(1/k) 逼近必须满足 Ω((log k)^2) 维数 | 完整书面证明与有理区间复核；非 Lean 完整化 | [23273187](https://doi.org/10.5281/zenodo.23273187) |
| [指定置换多面体族的 Ehrhart 实根性](preprints/article-revisions-2026-10/ehrhart-real-rootedness/README.md) · [PDF](preprints/article-revisions-2026-10/ehrhart-real-rootedness/paper.pdf) | (132,213)-避免族全部 d ≥ 3 的结论 | 书面证明与有理证书，引用既有有限范围定理 | [23252971](https://doi.org/10.5281/zenodo.23252971) |
| [任意质量高斯质心包络](preprints/gaussian-centroid-mass-envelope-2026-10/README.md) · [PDF](preprints/gaussian-centroid-mass-envelope-2026-10/paper.pdf) | 对所有正质量向量给出 U(p)-2Q(p) ≤ M_d(p) ≤ U(p) 及两对数尺度推论 | 完整书面证明与精确区间复核；非 Lean 完整化 | [23273177](https://doi.org/10.5281/zenodo.23273177) |
| [复三行永久量—行列式全参数精确范数](preprints/lean-certified-2026-10/complex-pencil-norm/README.md) | 实际复 3 × 3 矩阵的全参数最优常数 | 范数主定理完整 Lean | [23249773](https://doi.org/10.5281/zenodo.23249773) |
| [永久量余子式谱的锐渐近](preprints/article-revisions-2026-10/sharp-cofactor-asymptotics/README.md) · [PDF](preprints/article-revisions-2026-10/sharp-cofactor-asymptotics/paper.pdf) | 全大阶对数渐近及秩二 ramp／endpoint limsup 常数 | Theorem 1 完整 Lean；后续 ramp／endpoint 仍为书面证明 | [23255145](https://doi.org/10.5281/zenodo.23255145) |
| [Bapat q-永久量单调性猜想的反例](submissions/arxiv-2026-10/bapat-q-permanent-counterexamples/README.md) · [PDF](submissions/arxiv-2026-10/bapat-q-permanent-counterexamples/paper.pdf) | 指定复数有理反例与实对称整数反例存在定理 | 两项主结论完整 Lean | [23252928](https://doi.org/10.5281/zenodo.23252928) |
| [有限群轨道原始—对偶定理](preprints/lean-certified-2026-10/orbital-primal-dual/README.md) | 通用有限作用定理、有理最优证书与锐性 | 主定理完整 Lean | [23249749](https://doi.org/10.5281/zenodo.23249749) |
| [Wakhare 熵多项式根猜想反例](preprints/lean-certified-2026-10/entropy-polynomial-roots/README.md) | 参数 (11,10) 在 (0,1) 内至少四个不同实根 | 完整 Lean | [23253028](https://doi.org/10.5281/zenodo.23253028) |
| [归一化永久量余子式谱无界性](preprints/article-revisions-2026-10/cofactor-spectrum-unbounded/README.md) · [PDF](preprints/article-revisions-2026-10/cofactor-spectrum-unbounded/paper.pdf) | 排除任何维数无关的谱比值上界 | 完整书面证明与独立整数证书 | [23252977](https://doi.org/10.5281/zenodo.23252977) |
| [二次整环中的有界步长图](preprints/lean-certified-2026-10/quadratic-order-moats/README.md) | 所有二次整环、固定步长界下的分量一致有界 | 完整 Lean；不声称有效数值界 | [23249743](https://doi.org/10.5281/zenodo.23249743) |
| [连续幂渐近的稳健避让](preprints/lean-certified-2026-10/continuum-power-avoidance/README.md) | 给定可数有界对数间隙族的避让定理 | 主定理完整 Lean | [23249747](https://doi.org/10.5281/zenodo.23249747) |
| [单峰 CGF 素数阶因子猜想反例](preprints/lean-certified-2026-10/cyclotomic-unimodal-counterexample/README.md) | 指定 216 次多项式反例 | 完整 Lean；不声称次数最小 | [23249757](https://doi.org/10.5281/zenodo.23249757) |
| [周期图染色系数的无限对数凹性分类](preprints/lean-certified-2026-10/cycle-chromatic-classification/README.md) | 全部 C_n，n ≥ 3；当且仅当 3 ≤ n ≤ 11 | 完整 Lean | [23249722](https://doi.org/10.5281/zenodo.23249722) |
| [q-永久量半轴单调性反例](preprints/lean-certified-2026-10/q-permanent-halfline/README.md) | 指定实有理 4 × 4 矩阵在 q=49、50 间下降 | 指定反例完整 Lean | [23249758](https://doi.org/10.5281/zenodo.23249758) |
| [恒等补齐与永久量不等式](preprints/article-revisions-2026-10/permanent-padding/README.md) · [PDF](preprints/article-revisions-2026-10/permanent-padding/paper.pdf) | Pan–Skandera–Wang Conjecture 9.3 | 既有 Theorem 8.18 的书面推论 | [23252976](https://doi.org/10.5281/zenodo.23252976) |
| [未知态纠缠提取：精确指数、可靠性与高斯阈值](research/universal-schur-extraction/README.md) · [PDF](research/universal-schur-extraction/main.pdf) | 全部固定局域维数与任意谱；同一无状态信息协议达到已知态基准，并确定严格直接区间及高斯窗口 | 完整解析论证与精确附属检查；非 Lean、未外部同行评审；含显式全局酉预处理 | — |
| [全局酉预处理后的纠缠提取容量与强逆指数](research/global-unitary-ppt-extraction/README.md) · [PDF](research/global-unitary-ppt-extraction/main.pdf) | 任意固定 m≤n 与任意谱；LO、LOCC、完全 PPT 的容量和全速率指数一致 | 完整书面论证与精确附属检查；非 Lean、未外部同行评审；不声称解决普通固定态蒸馏 | — |

[九篇完整 Lean 主定理预印本的详细范围与 BibTeX](preprints/lean-certified-2026-10/README.md) · [全部专题稿件](SOLVED_PROBLEMS.md) · [001–009 及扩展索引](CONTENTS.md)

[17 篇稿件的文章与范围审计](reviews/manuscript-quality-2026-10-08/README.md) · [9 篇修订版 DOI 与公开附件核验](releases/manuscript-revisions-20261008/README.md)

余子式谱 Theorem 1 的[完整 Lean 形式化与范围核对](verification/cofactor-spectral-theorem1-lean-2026-10-09/README.md)单独列出；后续 ramp／endpoint 结论不计入该形式化证书。

新增互信息预印本的[版面、来源与冻结证明核对](verification/mutual-information-index-2026-10-08/README.md)及[独立论文 DOI 归档核验](releases/mutual-information-preprint-20261008/README.md)另列，不混入此前 17 篇审计。

## 已宣称解决的问题

以下按仓库公开证明的**实际命题**列出。相同论文可对应多个命题，限定情形与一般猜想分开；此表不自动作出首次解决或历史优先权认定。

| 问题／来源 | 仓库结论及范围 | 证明入口 |
| --- | --- | --- |
| Heilman 2014 Conjecture 3 | 证明；四个等质量高斯单元在三维的正四面体极值及等号分类 | [独立四胞预印本](preprints/gaussian-four-cell-global-2026-10/README.md)；[全部 k 扩展](preprints/gaussian-equal-cells-2026-10/README.md) |
| Erdős 相似性猜想的限定增长间隙类 | 证明满足晚期环带填充条件的一类正测度仿射非普适性；不解决完整猜想 | [独立预印本](preprints/erdos-similarity-growing-gaps-2026-10/README.md) |
| Fuentes–Keeler–Munizzi–Pollack Conjecture 1 | 证明；正三重信息蕴含局部等价图含诱导四星（claw） | [图态 MMI 预印本](preprints/graph-state-mmi-forbidden-subgraph-2026-10/README.md) |
| Pant–Singh Section 6 的全图强／self-Chollet 问题 | 证明并加强到全部主子矩阵；仅限有限简单无权图 Laplacian | [完整论文](preprints/all-graph-chollet-2026-10/README.md)；[完整 Lean](https://github.com/mxym/math/tree/4d2eefd40ee930216ccd8fc0f51e4bf694251967/formalizations/laplacian-chollet-all-graphs-progress) |
| Iqbal ECQC Conjecture 3.1 的纯态问题（arXiv:2509.08286v2 Section 5） | 素数维数中仅 p=2 普遍成立；p=3 即有精确一比特超出，奇素数反例完整覆盖；此前一般混合态反例另行致谢 | [完整证明、定义、文献范围与重放](research/ecqc-pure-state-counterexamples/README.md) |
| Heilman 2019 Conjecture 1.16 的等质量子情形 | 证明；覆盖所有 k，达到等号要求 d ≥ k−1，低维仅得严格上界 | [书面证明与部分 Lean 范围](preprints/gaussian-equal-cells-2026-10/README.md) |
| Heilman 2019 Conjecture 1.16 的任意质量原表述 | 反例；对每个 0<p<1/4 的四胞非均匀质量族，所有正四面体模型均严格非最优 | [独立预印本与完整书面反例](preprints/gaussian-fixed-mass-propeller-counterexample-2026-10/README.md) |
| Berta–Lami–Tomamichel，arXiv:2408.15226v2 Eq. (106) 的一般互信息连续性拟议界 | 反例；任意小正距离均存在，两侧边缘均变化；固定一侧边缘版本未解决 | [署名论文与完整经典 Lean 范围](preprints/mutual-information-continuity-2026-10/README.md) |
| de Castro Conjecture 10.1，arXiv:2609.06096v1 | 证明；指定避免置换多面体族全部 d ≥ 3 的实根性，结合既有 d ≤ 1000 定理 | [书面证明与精确证书](notes/ehrhart-uniform-real-rootedness/README.md) |
| Bapat 原区间 q-永久量单调性猜想 | 反例；复 Hermitian 版本及实对称限制均不成立，实反例为有限存在性结论 | [合并证明与完整 Lean](submissions/arxiv-2026-10/bapat-q-permanent-counterexamples/README.md) |
| Wakhare Conjecture 2 的“两内部根”断言 | 反例；(11,10) 至少四个不同内部根，不涉及另一熵不等式 | [完整 Lean](formalizations/wakhare-entropy-four-roots-lean/README.md) |
| Burgin–Goldberg–Keleti–MacMahon–Wang Question 1，arXiv:2210.09284v1 | 对该版本的全比值仿射几何序列问题给出否定回答；不声称其在本工作前仍未解决 | [来源说明](notes/continuum-power-avoidance/README.md)；[完整 Lean 几何避让](formalizations/geometric-avoidance/README.md) |
| Billey–Swanson Conjecture 48 | 反例；非恒定基本单峰 CGF 可没有任何素数阶圆分因子 | [完整 Lean](formalizations/cyclotomic-prime-factor-counterexample/README.md) |
| Amdeberhan–Moll Conjecture 21／早期 Conjecture 13.1 | 一般染色系数无限对数凹性断言被 C17 反驳；周期图族另有完整分类 | [反例](notes/chromatic-infinite-logconcavity-counterexample/README.md)；[全周期图 Lean 分类](formalizations/chromatic-cycles-all-n-lean/README.md) |
| da Fonseca 半轴 q-永久量单调性扩展 | 反例；4 阶最小，书面证明另给出每个 t > 1 的负导数族 | [书面证明](notes/q-permanent-halfline-counterexample/README.md)；指定矩阵完整 Lean |
| Pan–Skandera–Wang Conjecture 9.3 | 证明；由原作者 Theorem 8.18 经恒等补齐直接推出 | [完整书面推导](notes/permanent-inequality-padding/README.md) |

此外，仓库已证明通用有限群对偶、全固定秩 Chebyshev 锐渐近、全子集秩 5/14 精确值、锐单纯形稳定指数、递归投影体层级及首个嵌套维数、有限筛 minimax 与最优界等专题结果。全部入口按领域列在 [已证明专题清单](SOLVED_PROBLEMS.md)。一般 PSD Chollet、正相关高斯噪声稳定性、完整 Erdős 相似性猜想、Ryser rank-six 等未解决目标仍单独标明。

## 证明与复现

各项目的定理、证明范围、外部输入和复现命令均放在对应项目页面。完整 Lean 工程、形式化标准和机器审计记录集中在以下入口：

[形式化与验证记录](formalizations/) · [全部验证材料](verification/) · [分类研究目录](RESEARCH.md) · [五篇整合稿](manuscripts/README.md)

“完整 Lean”只适用于项目明确列出的具体定理；有限证书或成功构建不自动覆盖整篇论文。公开预印本的数学范围和未解决部分以各自 README 为准。

## 引用、版本与许可

引用时使用对应版本 DOI 及冻结源提交。后续修正或加强形成新版本并保留原记录。

[DOI 与 BibTeX](preprints/lean-certified-2026-10/README.md#本轮公开-doi) · [Release DOI 档案](releases/ZENODO_RECORDS.md) · [GitHub Releases](https://github.com/mxym/math/releases) · [不可变 Release 工作流](releases/README.md) · [变更记录](CHANGELOG.md) · [历史进展](RESEARCH_HISTORY.md)

[来源与权利声明](NOTICE.md) · [OpenAI/math 原许可证](third_party_licenses/openai_math_LICENSE.txt) · [文献比较](comparisons/)

公开稿件与 DOI 不等于期刊同行评审，也不自动认证原创性或历史优先权。各稿件注明借鉴的公开工作和自身贡献。保留已有许可证及第三方声明；未另行授权的原创材料保留全部权利。
