# 数学研究 · mxym/math

[English README](README.en.md)

数学研究论文、完整证明、Lean 形式化与可复现的计算证书。

**张永贤（Yongxian Zhang）** · 华南理工大学计算机科学与工程学院，大二本科生（2026 年 10 月）。

通讯邮箱：[mxymmxym1@gmail.com](mailto:mxymmxym1@gmail.com) · 备用邮箱：[3645500659@qq.com](mailto:3645500659@qq.com)

ORCID：[0009-0000-3864-3536](https://orcid.org/0009-0000-3864-3536) · [完整作者资料与署名模板](AUTHOR.md)

个人独立开展研究，无外部研究经费。使用AI进行辅助研究；各项目公开证明来源、验证范围和复现材料。

[预印本](#预印本) · [已书面证明的问题](#已书面证明的问题) · [尝试过的问题](#尝试过的问题) · [全部专题成果](SOLVED_PROBLEMS.md) · [分类研究目录](RESEARCH.md) · [证明与复现](#证明与复现)

## 预印本

公开论文与研究稿的阅读入口如下。证明状态针对各稿件明确陈述的主结论；具体定理、外部输入和复现方法见对应页面。

| 预印本／研究稿 | 主结论范围 | 证明状态 | 版本 DOI |
| --- | --- | --- | --- |
| [有限树模型的全实 Jacobian 与精确实解纤维](preprints/finite-tree-jacobian-2026-10/README.md) · [PDF](preprints/finite-tree-jacobian-2026-10/paper.pdf) | 任意泄漏位置的全实分解、精确重数、完整正目标的全部实解及计数 | 主定理对应既有固定 Lean；235 输入／原归档独立核对，论文为公开准备稿 | — |
| [qutrit–qudit APPT 最大纯度](preprints/appt-qutrit-purity-2026-10/README.md) · [PDF](preprints/appt-qutrit-purity-2026-10/main.pdf) | 所有 n≥3 的绝对 PPT qutrit–qudit 态纯度精确最大值，并证明实际取到 | 主 APPT 定理完整 Lean；绝对可分态推论为独立书面证明 | [23269470](https://doi.org/10.5281/zenodo.23269470) |
| [APPT 纯度：qutrit 精确定理与高维渐近律](preprints/appt-purity-unified-2026-10/README.md) · [PDF](preprints/appt-purity-unified-2026-10/main.pdf) | 合并 qutrit–qudit 精确最大值、一般维数反例、全域渐近律及充分长方形区间的精确最大值与极值谱分类 | qutrit、10×38 反例、充分长方形区域精确最大值及全部极值态分类、所有维数增长方式的统一首阶纯度渐近律均已完整 Lean；完整熵极值及渐近谱刚性仍按覆盖表区分 | — |
| [四个等质量高斯单元：协方差变形与四面体刚性](preprints/gaussian-four-cell-global-2026-10/README.md) · [PDF](preprints/gaussian-four-cell-global-2026-10/paper.pdf) | 所有 d≥3 的全局锐界与正四面体等号分类；包括 Heilman 2014 Conjecture 3 的三维命题 | 完整数学证明，使用已发表 Gaussian multi-bubble 与 Gaussian 等周定理；Lean 验证除外部 Gaussian 多泡定理及部分 Gaussian 积分外的内部证明链 | [23272806](https://doi.org/10.5281/zenodo.23272806) |
| [Erdős 相似性的增长对数间隙扩展](preprints/erdos-similarity-growing-gaps-2026-10/README.md) · [PDF](preprints/erdos-similarity-growing-gaps-2026-10/paper.pdf) | 对满足晚期环带填充条件的一类序列证明正测度仿射非普适性，含相邻比值趋零与间歇环带例子；完整 Erdős 猜想仍开放 | 完整书面证明；题目所述 Theorem 2 及其连续间隙特例已完整 Lean 内核复核；完整 Erdős 猜想仍开放 | [23305280](https://doi.org/10.5281/zenodo.23305280) |
| [图态 MMI 禁止子图定理](preprints/graph-state-mmi-forbidden-subgraph-2026-10/README.md) · [PDF](preprints/graph-state-mmi-forbidden-subgraph-2026-10/paper.pdf) | Fuentes–Keeler–Munizzi–Pollack Conjecture 1：正三重信息蕴含局部等价图有诱导 claw；另给无爪 vertex-minor 分类与七顶点连通阈值 | 完整书面证明与双独立精确 checker；未完整 Lean 化 | [23272728](https://doi.org/10.5281/zenodo.23272728) |
| [全图强 Chollet 不等式](preprints/all-graph-chollet-2026-10/README.md) · [PDF](preprints/all-graph-chollet-2026-10/paper.pdf) | Pant–Singh Section 6 的强／self-Chollet 问题：任意有限简单无权图、全部主子矩阵，保留原图度数 | [完整 Lean 固定源码](https://github.com/mxym/math/tree/4d2eefd40ee930216ccd8fc0f51e4bf694251967/formalizations/laplacian-chollet-all-graphs-progress) | [23252964](https://doi.org/10.5281/zenodo.23252964) |
| [纯态 ECQC：素数维数完整分类](research/ecqc-pure-state-counterexamples/README.md) · [PDF](research/ecqc-pure-state-counterexamples/paper.pdf) | Iqbal Conjecture 3.1 的纯态问题（arXiv:2509.08286v2 §5）：素数维仅 p=2 普遍成立，奇素数均有满 Schmidt 秩反例，p=3 超出一比特；三维、五维比值最优；已有混合态反例另行归属 | 三维真实量子反例[完整 Lean 与空内核重放](formalizations/ecqc-pure-qutrit-counterexample/README.md)；全分类未整体 Lean 化 | [23256948](https://doi.org/10.5281/zenodo.23256948) |
| [高斯等质量单纯形一阶矩：全部 k](preprints/gaussian-equal-cells-2026-10/README.md) · [PDF](preprints/gaussian-equal-cells-2026-10/paper.pdf) | Heilman 2019 Conjecture 1.16 的等质量子情形：所有 k≥2 的上界，d≥k−1 时最优值及全部等号，低维严格上界 | 完整书面证明；全部 k 的 Lean 为部分覆盖 | [23250730](https://doi.org/10.5281/zenodo.23250730) |
| [高斯固定质量正四面体猜想反例](preprints/gaussian-fixed-mass-propeller-counterexample-2026-10/README.md) · [PDF](preprints/gaussian-fixed-mass-propeller-counterexample-2026-10/paper.pdf) | Heilman 2019 Conjecture 1.16 任意质量表述的反例：对每个 0<p<1/4 的指定四胞质量族，所有正四面体模型严格非最优；等质量情形保持原结论 | 完整书面反例；精确 Q(√2) 诊断与部分 Lean，几何端点未完整形式化 | [23272917](https://doi.org/10.5281/zenodo.23272917) |
| [全整数高斯维数阶](preprints/gaussian-quadratic-dimension-all-k-2026-10/README.md) · [PDF](preprints/gaussian-quadratic-dimension-all-k-2026-10/paper.pdf) | 对所有充分大的整数 k 建立匹配的 Θ((log k)^2) 维数阶 | 完整书面证明、Berry–Esseen 外部定理和精确复核；非 Lean 完整化 | [23273190](https://doi.org/10.5281/zenodo.23273190) |
| [ECQC 满秩极值刚性与纯稳定子完整分类](research/ecqc-stabilizer-saturation/README.md) · [PDF](research/ecqc-stabilizer-saturation/paper.pdf) | 所有奇素数满秩等号态；全部双 qudit 纯稳定子分数；p≡1 mod 4 时全纯态最优比值 p/2 | 完整书面证明、两套精确重放；非完整 Lean | [23256934](https://doi.org/10.5281/zenodo.23256934) |
| [高斯维数—精度常数精化](preprints/gaussian-sharp-dimension-rate-2026-10/README.md) · [PDF](preprints/gaussian-sharp-dimension-rate-2026-10/paper.pdf) | 给出误差与 log² k 维数系数的显式权衡及球冠常数精化 | 完整书面证明与精确复核；非 Lean 完整化 | [23273299](https://doi.org/10.5281/zenodo.23273299) |
| [一般互信息连续性拟议界的三元反例](preprints/mutual-information-continuity-2026-10/README.md) · [PDF](preprints/mutual-information-continuity-2026-10/paper.pdf) | Berta–Lami–Tomamichel arXiv:2408.15226v2 Eq. (106) 拟议界的实际 3×3 反例：任意小正距离、两侧边缘均变化；固定一侧边缘版本未解决 | 经典反例完整 Lean；量子嵌入及必要系数下界为书面证明 | [23253944](https://doi.org/10.5281/zenodo.23253944) |
| [单纯形稳定性与锐指数](preprints/lean-certified-2026-10/sharp-simplex-stability/README.md) | 所有 d ≥ 3；上界与指数不可改进 | 完整 Lean，常数不声称最优 | [23253001](https://doi.org/10.5281/zenodo.23253001) |
| [指定质量高斯重心椭球不等式](preprints/article-revisions-2026-10/gaussian-prescribed-mass/README.md) · [PDF](preprints/article-revisions-2026-10/gaussian-prescribed-mass/paper.pdf) | 所有正质量向量的质量依赖矩阵度量锐界 | 完整书面证明；部分 Lean | [23252992](https://doi.org/10.5281/zenodo.23252992) |
| [高斯球冠维数下界](preprints/gaussian-spherical-cap-converse-2026-10/README.md) · [PDF](preprints/gaussian-spherical-cap-converse-2026-10/paper.pdf) | 证明加性 O(1/k) 逼近必须满足 Ω((log k)^2) 维数 | 完整书面证明与有理区间复核；非 Lean 完整化 | [23273187](https://doi.org/10.5281/zenodo.23273187) |
| [指定置换多面体族的 Ehrhart 实根性](preprints/article-revisions-2026-10/ehrhart-real-rootedness/README.md) · [PDF](preprints/article-revisions-2026-10/ehrhart-real-rootedness/paper.pdf) | de Castro Conjecture 10.1（arXiv:2609.06096v1）：(132,213)-避免族全部 d≥3 的实根性，结合既有 d≤1000 定理 | 书面证明与有理证书，引用既有有限范围定理；[书面证明与精确证书](notes/ehrhart-uniform-real-rootedness/README.md) | [23252971](https://doi.org/10.5281/zenodo.23252971) |
| [任意质量高斯质心包络](preprints/gaussian-centroid-mass-envelope-2026-10/README.md) · [PDF](preprints/gaussian-centroid-mass-envelope-2026-10/paper.pdf) | 对所有正质量向量给出 U(p)-2Q(p) ≤ M_d(p) ≤ U(p) 及两对数尺度推论 | 完整书面证明与精确区间复核；非 Lean 完整化 | [23273177](https://doi.org/10.5281/zenodo.23273177) |
| [复三行永久量—行列式全参数精确范数](preprints/lean-certified-2026-10/complex-pencil-norm/README.md) | 实际复 3 × 3 矩阵的全参数最优常数 | 范数主定理完整 Lean | [23249773](https://doi.org/10.5281/zenodo.23249773) |
| [永久量余子式谱的锐渐近](preprints/article-revisions-2026-10/sharp-cofactor-asymptotics/README.md) · [PDF](preprints/article-revisions-2026-10/sharp-cofactor-asymptotics/paper.pdf) | 全大阶对数渐近及秩二 ramp／endpoint limsup 常数 | Theorem 1 完整 Lean；后续 ramp／endpoint 仍为书面证明 | [23255145](https://doi.org/10.5281/zenodo.23255145) |
| [Bapat q-永久量单调性猜想的反例](submissions/arxiv-2026-10/bapat-q-permanent-counterexamples/README.md) · [PDF](submissions/arxiv-2026-10/bapat-q-permanent-counterexamples/paper.pdf) | Bapat 原区间 q-永久量单调性反例：指定复 Hermitian 有理矩阵及实对称整数反例存在定理 | 两项主结论完整 Lean | [23252928](https://doi.org/10.5281/zenodo.23252928) |
| [复四行永久量—行列式锐界与完整等号分类](preprints/four-row-permanent-determinant-2026-10/README.md) · [PDF](preprints/four-row-permanent-determinant-2026-10/paper.pdf) | 所有实际复 4 × 4 矩阵、c ≥ 0；最优常数、临界等号及实参数范数 | 主结论完整 Lean；本轮为独立排版稿，不宣称重新执行旧内核审计 | — |
| [有限群轨道原始—对偶定理](preprints/lean-certified-2026-10/orbital-primal-dual/README.md) | 通用有限作用定理、有理最优证书与锐性 | 主定理完整 Lean | [23249749](https://doi.org/10.5281/zenodo.23249749) |
| [Wakhare 熵多项式根猜想反例](preprints/lean-certified-2026-10/entropy-polynomial-roots/README.md) | Wakhare Conjecture 2 的“两内部根”断言反例：(11,10) 在 (0,1) 至少四个不同实根；另一熵不等式保持原状态 | 完整 Lean；[完整 Lean](formalizations/wakhare-entropy-four-roots-lean/README.md) | [23253028](https://doi.org/10.5281/zenodo.23253028) |
| [归一化永久量余子式谱无界性](preprints/article-revisions-2026-10/cofactor-spectrum-unbounded/README.md) · [PDF](preprints/article-revisions-2026-10/cofactor-spectrum-unbounded/paper.pdf) | 排除任何维数无关的谱比值上界 | 完整书面证明与独立整数证书 | [23252977](https://doi.org/10.5281/zenodo.23252977) |
| [二次整环中的有界步长图](preprints/lean-certified-2026-10/quadratic-order-moats/README.md) | 所有二次整环、固定步长界下的分量一致有界 | 完整 Lean；不声称有效数值界 | [23249743](https://doi.org/10.5281/zenodo.23249743) |
| [连续幂渐近的稳健避让](preprints/lean-certified-2026-10/continuum-power-avoidance/README.md) | 给定可数有界对数间隙族的避让定理 | 主定理完整 Lean | [23249747](https://doi.org/10.5281/zenodo.23249747) |
| [单峰 CGF 素数阶因子猜想反例](preprints/lean-certified-2026-10/cyclotomic-unimodal-counterexample/README.md) | Billey–Swanson Conjecture 48 反例：指定 216 次非恒定基本单峰 CGF 没有任何素数阶圆分因子；不声称次数最小 | 完整 Lean；不声称次数最小；[完整 Lean](formalizations/cyclotomic-prime-factor-counterexample/README.md) | [23249757](https://doi.org/10.5281/zenodo.23249757) |
| [周期图染色系数的无限对数凹性分类](preprints/lean-certified-2026-10/cycle-chromatic-classification/README.md) | Amdeberhan–Moll Conjecture 21／早期 13.1 的一般断言有 C17 反例；全部 C_n、n≥3 的无限对数凹性当且仅当 3≤n≤11 | 完整 Lean；[反例](notes/chromatic-infinite-logconcavity-counterexample/README.md)；[全周期图 Lean 分类](formalizations/chromatic-cycles-all-n-lean/README.md) | [23249722](https://doi.org/10.5281/zenodo.23249722) |
| [q-永久量半轴单调性反例](preprints/lean-certified-2026-10/q-permanent-halfline/README.md) | da Fonseca 半轴扩展的实有理 4×4 反例在 q=49、50 间下降；书面结果另给最小阶为4及每个 t>1 的负导数族 | 指定反例完整 Lean；最小阶和全 t>1 实参族为书面证明；[书面证明](notes/q-permanent-halfline-counterexample/README.md) | [23249758](https://doi.org/10.5281/zenodo.23249758) |
| [恒等补齐与永久量不等式](preprints/article-revisions-2026-10/permanent-padding/README.md) · [PDF](preprints/article-revisions-2026-10/permanent-padding/paper.pdf) | Pan–Skandera–Wang Conjecture 9.3：由原作者 Theorem 8.18 经恒等补齐直接推出 | 既有 Theorem 8.18 的书面推论；[完整书面推导](notes/permanent-inequality-padding/README.md) | [23252976](https://doi.org/10.5281/zenodo.23252976) |
| [未知态纠缠提取：精确指数、可靠性与高斯阈值](research/universal-schur-extraction/README.md) · [PDF](research/universal-schur-extraction/main.pdf) | 全部固定局域维数与任意谱；同一无状态信息协议达到已知态基准，并确定严格直接区间及高斯窗口 | 完整解析论证与精确附属检查；非 Lean、未外部同行评审；含显式全局酉预处理 | — |
| [全局酉预处理后的纠缠提取容量与强逆指数](research/global-unitary-ppt-extraction/README.md) · [PDF](research/global-unitary-ppt-extraction/main.pdf) | 任意固定 m≤n 与任意谱；LO、LOCC、完全 PPT 的容量和全速率指数一致 | 完整书面论证与精确附属检查；非 Lean、未外部同行评审；不声称解决普通固定态蒸馏 | — |
| [全比值仿射几何序列避让](notes/continuum-power-avoidance/README.md) | Burgin–Goldberg–Keleti–MacMahon–Wang Question 1（arXiv:2210.09284v1）的全比值问题给出否定回答；不声称此前仍未解决 | [完整 Lean 几何避让](formalizations/geometric-avoidance/README.md)；限定原版本命题 | — |

[九篇完整 Lean 主定理预印本的详细范围与 BibTeX](preprints/lean-certified-2026-10/README.md) · [全部专题稿件](SOLVED_PROBLEMS.md) · [001–009 及扩展索引](CONTENTS.md)

[17 篇稿件的文章与范围审计](reviews/manuscript-quality-2026-10-08/README.md) · [9 篇修订版 DOI 与公开附件核验](releases/manuscript-revisions-20261008/README.md)

[aiXiv 发布、去重与当前许可证核对](verification/aixiv-publication-20261013/README.md)：9 篇补发，3 条主动重复记录已撤回；高斯四单元按作者单独授权的 CC BY-NC-ND 4.0 发布。

余子式谱 Theorem 1 的[完整 Lean 形式化与范围核对](verification/cofactor-spectral-theorem1-lean-2026-10-09/README.md)单独列出；后续 ramp／endpoint 结论不计入该形式化证书。

新增互信息预印本的[版面、来源与冻结证明核对](verification/mutual-information-index-2026-10-08/README.md)及[独立论文 DOI 归档核验](releases/mutual-information-preprint-20261008/README.md)另列，不混入此前 17 篇审计。

## 已书面证明的问题

本专题收录**已有完整书面证明、所列主结论尚未完整 Lean 形式化**的成果。证明必须覆盖原对象、假设和量词；已发表外部定理须明确引用，未证明的猜想不能作为无条件结论的依据。部分 Lean 和有限计算只计入各自明确的验证范围。探索记录、数值猜测和核心论证未闭合的稿件不列入。

以下是按证明状态整理的主要阅读入口，与预印本表有交叉，不重复计为独立突破。“已书面证明”不表示外部同行评审或历史优先权；本轮重算的是新增的 APPT、四行虚参数和 ECQC 临界亏秩项，其他条目的审查与复核范围以原页面为准。

| 问题／成果 | 书面已证明的精确范围 | 完整证明与输入 | Lean 实际状态 |
| --- | --- | --- | --- |
| APPT 全正阶熵统一首项与阶数转变 | m→∞、任意 n≥m、每个 α>0 的首个非零熵缺口统一等价；有限长宽比全部极限阶数的近极小谱分类；有限 D 下 0<α≤1/(512D) 的精确极小值与全部等号 | [全阶完整证明](research/appt-growing-renyi/ALL_ORDER_VARIATIONAL.md)、[α/m→∞ 的全长宽比相变与谱判据](research/appt-ultralinear-spectrum-20261014/README.md)、[窗口与谱分类](research/appt-growing-renyi/README.md)、[源绑定内部复核](research/appt-growing-renyi/ALL_ORDER_REVIEW.json) | 完整书面证明，未整体 Lean 化；原有限构造审计不扩展至新熵目标与极限；同一 APPT 方向的加强不重复计数 |
| 同一 APPT 方向：有限高阶 Rényi 精确极值 | 实际 2⊗n、n≥4、所有实 α≥2 的精确整数秩公式与全部等号；任意 m⊗n 在 D≥6、α≥D/2+1，及 D=4、α≥24 的唯一 spike 极值；维数截止尺度 Θ(D) | [完整有限维书面证明与受审版本](research/appt-finite-high-order-20261014/README.md)；已有谱顶点／纯度及可分离端点明确归属 | 未整体 Lean 化；有限高阶带的常数不宣称最优；同一方向加强，不新增重大猜想计数 |
| 同一 APPT 方向：实阶扩展与锐截止 | 实际 2⊗n、n≥8、全部实 α>1 的有限精确极值；n≥4 的 pole 最优当且仅当 α≥τ_D，覆盖全部正阶；临界全部等号及锐常数 τ_D/D→log2/2 | [完整书面证明、精确截止方程与源绑定内部复核](research/appt-log-order-phase-20261014/README.md)；一般 m≥3 给充分界与临界唯一性 | 未整体 Lean 化；不声称所有 subcritical 最小值或一般 APPT=ASEP；同一方向加强不另计重大猜想 |
| 同一 APPT 方向：对数阶锐主系数与固定局部相变 | 所有固定ℓ≥3、m≥ℓ，κℓ=1/log[3(ℓ−1)/(ℓ+1)]；任意c>κℓ、充分大D、全部α≥c logD+1的唯一APPT/ASEP pole；实际ℓ⊗n给APPT-only锐下界；固定m、所有α→∞的完整logD相变 | [锐系数与全增长阶证明、240行独立内审](research/appt-sharp-log-cutoff-20261014/README.md)；[D≥9的显式32logD+1带及249行内审](research/appt-nonqubit-log-band-20261014/README.md) | 普通书面稿，未整体Lean；必要界沿ℓ⊗n，未称逐D/ASEP下界、有限临界窗口或增长ℓ统一性；同一方向，不另计重大猜想 |
| 同一 APPT 方向：临界窗口与常数阶精确截止 | 固定ℓ≥3，Xℓ=κℓ[logD−loglogD−log(e(qℓ−1)κℓ)]；任意ε>0、充分大D、所有m≥ℓ/实α≥Xℓ+ε的唯一APPT/ASEP pole；实际ℓ⊗n在Xℓ−ε给APPT-only反向界；固定m最终截止A=Xm+o(1)，有界临界偏移的完整APPT矩与熵包络 | [完整证明及新300行内部核读](research/appt-critical-window-20261014/README.md) | 普通书面稿，未整体Lean；未给ASEP下界、有限临界优化态分类或增长ℓ统一性；同一方向，不另计重大猜想 |
| 同一 APPT 方向：最终截止的定量根与逆对数展开 | 固定m≥3，实际最终截止A=wD+O(D^−β)，wD为唯一显式标量模型根、β>0；完整1/logD、1/(logD)^2修正及所有固定截断阶余项；固定m完整对数带矩包络的幂次相对误差；固定ℓ的所有实际m≥ℓ/更高实阶上界 | [完整证明与新304行及最终四行核读](research/appt-cutoff-root-tracking-20261014/README.md) | 普通书面稿，未整体Lean；下界APPT-only，不给有限维阈值、优化态分类、最优误差率或增长m统一性；同一方向，不另计重大猜想 |
| 同一 APPT 方向：固定局部维数的全正阶熵轴 | 每个固定m≥3，完整实际APPT最小熵缺口在全部扩展阶数0≤α≤∞统一近似max(已知bulk标量模型,精确pole)，误差O(D^−χm)、χm>0；全部有界阶数含趋0/跨1时误差O(1/D)，完整实际vonNeumann渐近律；已知0/∞端点及等号纳入 | [完整证明、新366行内部核读及归属边界](research/appt-all-positive-axis-20261014/README.md) | 普通书面稿，未整体Lean；bulk下界APPT-only，未给有限维优化态全分类或增长m统一性；已知标量/谱族不算新发现，同一方向不增重大猜想 |
| 同一 APPT 方向：最终精确 bulk 熵与全部等号 | 每个固定m≥3，任意正阶紧区间及全部a≤α≤c logD、a>0、c<1/log(m−1)，在充分大D上实际最小熵精确等于两层投影谱；完整等号由相邻两整数秩的精确比较选出；紧区间取整损失给出D^−2首项和O(D^−3)余项 | [完整新稿与独立380行普通核读](research/appt-eventual-bulk-20261014/README.md) | 普通书面证明，未整体Lean；固定m/正阶下界/充分大D必需；1/log(m−1)是单半空间方法的锐系数，不是真实APPT相变；未解全部有限D、ASEP bulk或增长m问题，不增重大猜想 |
| 同一 APPT 方向：精确零阶转变与完整低阶谱 | 固定m≥3、c<1/log(m−1)，充分大D上的全部0≤α≤c logD精确由缺一谱与整数秩两层谱择优，分类全部等号；唯一转变阶tau给出1/D及1/D²项；α=β/D全紧区间O(1/D)律、所有α趋0的一致等价及低/高/临界完整领先谱分类，允许临界两支交替 | [完整新稿与独立488行普通核读](research/appt-zero-order-transition-20261014/README.md) | 普通书面证明，未整体Lean；固定m/eventualD，未解全部有限D、增长m、ASEP bulk或高阶物理临界优化谱；已知谱族归属保持，不增加独立重大猜想数 |
| 同一 APPT 方向：固定局域维数的全阶精确熵与最优谱 | 每固定m≥3，一个充分大D阈值同时覆盖全部0≤α≤∞；实际APPT最小熵由缺一谱、精确整数秩两层谱与单峰谱择优，全部矩阵等号与秩平局分类；缺一/bulk/pole恰好两次谱族转变，高阶交点唯一且eta=X_m(D)+o(1)，内部bulk秩仍可变化 | [完整新稿与独立405行初稿核读及范围/排版两行修订复核](research/appt-all-order-exact-20261014/README.md) | 普通书面证明，未整体Lean；在fixedm/eventualD范围闭合此前高阶优化谱缺口，旧单包限制按其原范围理解；无任意有限D、增长m、最小有效阈值或ASEP bulk结论，不增独立重大猜想数 |
| 同一 APPT 方向：增长维数立方尺度的完整熵次阶 | 每固定 α>0、D/m³→δ>0，实际全局酉 APPT 熵在精确整数 bulk 之外的 D⁻¹ 修正由全正负异常谱的图逆矩阵变分公式给出，含 O(1/L) 有限逼近、准确极限 bulk 门槛和全部近极值谱条件；α≥2 完整归为单正异常，纯度门槛 δ=1/4 | [完整书面稿与独立 479 行初稿核读](research/appt-cubic-entropy-20261014/README.md) | 普通书面证明，未整体 Lean；固定阶数与正立方比，不是有限维 exact bulk 等号，α<2 保留全图公式，不扩大旧审核或独立重大计数 |
| 同一 APPT 方向：完整精确主体谱起效尺度 | 每固定有限正阶 α、充分大 m，所有 n≥δcrit(α)m²+Aαm 的实际 APPT 熵极值精确由整数秩 q 主体谱取得，全部矩阵等号与秩平局保留；最小最终起效门槛 Nα(m)=δcrit(α)m²+Oα(m)，纯度 N₂(m)=m²/4+O(m) | [完整书面稿与独立 395 行初稿及状态差异核读](research/appt-exact-cubic-bulk-20261014/README.md) | 普通书面、未整体 Lean；覆盖任意更大 n 和任意微小异常，未给全部有限维门槛或 O(m) 系数，不扩大审核或独立重大计数 |
| 同一 APPT 方向：最小最终纯度门槛的精确整数公式 | 充分大 m 的 N₂(m)=⌈(m²+5m+7)/4⌉；所有 n≥N₂ 的实际最大纯度、唯一整数秩和全部矩阵等号精确给出，N₂−1 有真实 APPT 胜出态 | [完整书面稿与独立 398 行初稿/状态字节核读](research/appt-exact-purity-onset-20261014/README.md) | 普通书面、未整体 Lean；无有效 M 或全部小 m 公式，不扩大旧审核或重大计数 |
| 同一 APPT 方向：有限临界窗口的全部纯度极值谱 | 每固定 A、充分大 m，完整 abs(n−m²/4)≤Am 窗口上的实际极值等于紧一实参/两整数秩公式；门槛下每个极值恰一个正异常、无负异常、边界 PSD、端点主体，所有真实平局保留 | [完整书面稿与独立 328 行初稿/相对变形核读](research/appt-critical-purity-optimizer-20261014/README.md) | 普通书面、未整体 Lean；精确变分值，不称全部有限维或每个标量参数的闭式解，不新增重大计数 |
| 同一 APPT 方向：临界纯度二阶值与全部极值谱速率 | 每固定 A 的全线性临界窗口，实际 D²(Pmax−PG)=[(5−4a)/m+(16a²−44a+37)/m²]₊+O_A(m⁻³)；所有门槛下极值的 z/p/c/整数秩统一速率，真实平局保留 | [完整书面稿与独立 224 行初稿及最终差异核读](research/appt-critical-purity-expansion-20261014/README.md) | 普通书面、未整体 Lean；非所有维数增长的下一阶定理，无有效 cutoff、不扩审核或重大计数 |
| 同一 APPT 方向：全固定正阶临界熵的全部实际极值谱 | 每固定有限 α>0（含 von Neumann）与 A，足够大 m 的完整 abs(n−dαm²)≤Am 窗口，实际极值精确由整数主体谱与单正/单负异常紧参数族择优，全部矩阵、参数及秩平局保留；半阶最小最终门槛线性项为 (27−11√5)/2 | [完整 H0–H5 稿及独立 681 行全读](research/appt-critical-entropy-20261015/README.md) | 普通书面、未整体 Lean；相对质量变形覆盖任意微尾，无有效 cutoff 或全部有限维结论，不扩旧审核或重大计数 |
| 同一 APPT 方向：全固定正阶最终门槛的紧标量公式 | 最小最终 Nα 夹于 ⌈να,m*±Cαm⁻³⌉；两侧实数参数距离 O(m⁻³)，保留可能相差一的整数取整；显式计算全部临界平局下的线性系数，配合后续非退化定理给 Nα=dαm²+aαm+Oα(1) | [完整 I0–I3 稿与独立 313 行全读](research/appt-entropy-onset-envelope-20261015/README.md) | 普通书面、未整体 Lean；含两种整数秩损失及所有更大 n，不作无条件单个精确 ceil 或增长阶一致性，不增重大计数 |
| 同一 APPT 方向：唯一临界异常与熵阶转变 | 每个固定 α>0 的正、负临界比值各有唯一非退化极大点，最优值 D+ 严格增、D− 严格减；唯一横截交点 α×∈(1/2,1)，dα 在此唯一最小；所有固定正阶门槛余项 Oα(1) | [完整 J0–J3 稿与独立 230 行全读](research/appt-critical-order-transition-20261015/README.md) | 普通书面、未整体 Lean；交点保留两领先分支及真实有限平局，小数仅数值说明；无变阶一致性或新重大计数 |
| 同一 APPT 方向：熵阶与维数共同临界转变 | α=α₀+u/m、n=d₀m²+am，逐固定有界 u,a，对充分大 m 一致有 mD(Eα−Gα)=max{0,L₊,L₋}+O_(U,A)(1/m)；全部实际极值谱与固定正间隙选支，最小最终门槛 d₀m²+max(A₊+σ₊u,A₋+σ₋u)m+O(1) | [完整 K0–K3 稿与独立 336 行全读](research/appt-coupled-order-window-20261015/README.md) | 普通书面、未整体 Lean；单独证明变阶一致性与所有更大 n，保留真实平局及双 ceil；极限图与小数仅说明，不扩重大计数 |
| 同一 APPT 方向：全正熵阶中最早最终门槛及全部最优阶数 | 对充分大 m，min_(α>0) Nα(m)=d₀m²+a_c m+O(1) 且最小值取到；每个最优阶数及固定加法误差近最优阶数均为 α₀+u_c/m+O(m⁻²)，保持原实际 APPT、整数秩与 ALL 更大 n | [完整 L0–L2、M0–M2 稿及各自独立全读](research/appt-optimal-entropy-order-20261015/README.md) | 普通书面、未整体 Lean；用相对误差排除趋零阶及无界增长阶，保留整数平局，不声称唯一有限最优阶、精确有限门槛或任意变阶完整极值公式；不增重大计数 |
| 同一 APPT 方向：全维数增长阶 Rényi 熵的统一公式 | 对所有 2≤m≤n，在 D=mn→∞且 α→∞ 时，一致有实际 Eα=max{log((m+1)/(m−1)),log3−logD/(α−1)}+o(1)；给每个 α≥2 的显式有限上下误差，涵盖固定/增长/振荡 m 与 α>D | [完整 P0–P2 稿及独立全读](research/appt-growing-renyi-order-20261015/README.md) | 普通书面、未整体 Lean；绝对误差而非零主项处相对等价；固定m推论必须D→∞，原量词错误/修订保全，不作精确有限极值或重大计数扩张 |
| 同一 APPT 方向：有限熵误差与超线性阶简式 | 所有3≤m≤n、α≥2有 Eα≤H+log27/(α−1)+4m/(D−m)，可与旧界取min；m→∞且α/m→∞时 Eα~H，H=max{log((m+1)/(m−1)),log3−logD/(α−1)} | [完整 R0–R2 与独立全读](research/appt-finite-entropy-bounds-20261015/README.md) | 普通书面；旧V已完成全阶范围，此处为有限估计/简化，不重复计首次闭合；新总误差不逐点优于旧界，无新重大计数或Lean |
| 同一 APPT 方向：线性阶临界窗口的实际谱刚性 | m→∞、所有整数n≥m、α/m→c>0、3^α/D→r有限时，所有实际近最优谱 iff 完整标量argmax距离、主体端点spread J、实际peak损失P均趋零；r=0给唯一主体两点law，r>0内点给峰高修正，保留全部ties | [完整谱判据与独立全读](research/appt-linear-critical-rigidity-20261015/README.md) | 普通书面未Lean；适用于此全原域窗口，非所有阶/长宽比刚性或精确有限谱；同一主线，无新重大计数 |
| Han Fourier 重叠辅助问题 Q3.1：全坐标反例 | 对任意深度d，构造N=2^d的单调传递read-once函数，每个坐标均essential且Aᵢ/Iᵢ≥3d/8，否定原“存在一个好坐标”的统一常数命题 | [完整稿与独立全读](research/han-fourier-overlap-20261015/README.md) | 普通书面、未Lean；只解完整辅助问题，FEI本身仍未解，不作重大猜想计数/优先权认证 |
| APPT 亚单位 Rényi 熵锐渐近与谱分类 | 每个固定 0<α<1，覆盖固定、增长及振荡的较小局域维数；联合增长有 α=1/2 分界，固定局域维数有精确首项及全部近极小谱分类 | [联合增长](research/appt-multilevel-counterexample/SUBUNIT_RENYI.md)、[全维统一式与固定局域分类](research/appt-multilevel-counterexample/SUBUNIT_ALL_DIMENSIONS.md)、[有限长宽比低阶刚性](research/appt-multilevel-counterexample/SUBUNIT_RIGIDITY.md)、[源绑定内审](research/appt-multilevel-counterexample/ALL_DIMENSIONS_REVIEW.json) | [实际半阶熵头与有限负尖峰](formalizations/appt-subunit-renyi/README.md)已内核复核；全维熵极限及谱分类未整体 Lean 化 |
| 四行虚参数永久量—行列式锐范数及全部等号 | 任意实际复 4×4 矩阵与全部实数 t；锐常数 max{3/2, abs(t)+1/√3}，含零行、flat 与定向 Fourier 块的完整分支分类 | [范数证明](research/four-row-imaginary-pencil/PAPER.md)、[全部等号证明](research/four-row-imaginary-pencil/EQUALITY.md)；精确 256×256 代数身份与正 Gram 证书 | 新方向无 Lean；整个一般复参数平面仍未解决 |
| 任意权环及 cycle/bipartite 块的强 Chollet | 任意非负实 conductance、全部环长 n≥3、原图度数下全部主子矩阵与非负对角增量；正奇环有明确严格缺口 | [完整书面证明](research/weighted-cycle-chollet/PAPER.md)、[定理与验证范围](research/weighted-cycle-chollet/THEOREM_MAP.md)；披露 Lieb 及既有二分图输入 | 无新增 Lean；任意加权非二分块及全部 PSD Z 情形仍未解决 |
| ECQC 临界亏秩全部等号态 | 所有奇素数，r=(p+1)/2；p≡1 mod4 或 p=3 时恰 p⁴ 条指定 Weyl 轨道射线，其余 p≡3 mod4、p≥7 在该秩无等号 | [完整分类证明](research/ecqc-critical-rank-equality/PAPER.md)；引用 Holevo 等号必要条件，逐步证明 MUB／矩阵刚性桥接 | [有限域核心与矩阵引理](formalizations/ecqc-critical-rank-progress/README.md)部分 Lean；量子主定理未整体形式化；更低秩未分类 |
| 图态 MMI 禁止子图定理 | Conjecture 1、无爪 vertex-minor 六类分量分类及七顶点连通阈值 | [完整证明与双独立 checker](preprints/graph-state-mmi-forbidden-subgraph-2026-10/README.md)；全阶归纳与熵证明另行给出 | 未完整 Lean；有限图证书不替代一般定理 |
| ECQC 满秩刚性与纯稳定子分类 | 任意奇素数全部满秩等号态、全部双 qudit 纯稳定子分数，p≡1 mod4 的全纯态最优比值 p/2 | [完整证明与文献范围](research/ecqc-stabilizer-saturation/README.md)；Holevo 定理为已发表外部输入 | 主分类未整体 Lean；不包括所有亏秩等号态 |
| 等质量高斯单元锐界与等号 | 所有 k≥2、足够维数的单纯形最优值与全部等号；四胞锐常数与四面体分类 | [全部 k](preprints/gaussian-equal-cells-2026-10/README.md)与[四胞证明](preprints/gaussian-four-cell-global-2026-10/README.md)；使用已发表 Gaussian multi-bubble 和等周定理 | 内部证明链有部分 Lean；外部多泡输入及部分积分尚未整体形式化 |
| 任意质量正四面体最优性反例 | 对每个 0<p<1/4 的指定四胞质量族严格否定正四面体最优性 | [完整书面反例](preprints/gaussian-fixed-mass-propeller-counterexample-2026-10/README.md)与精确代数诊断；等质量情形不在范围内 | 部分 Lean；最终几何比较未完整形式化 |
| 全整数高斯维数阶 | 对所有充分大的整数 k，O(1/k) 精度对应匹配 Θ((log k)²) 维数阶 | [完整证明](preprints/gaussian-quadratic-dimension-all-k-2026-10/README.md)；明确引用 Berry–Esseen 外部定理 | 未完整 Lean；不是对有限样本的渐近外推 |
| 未知态的全局酉预处理纠缠提取 | 同一不依赖谱／本征基的协议族，达到所列容量、指数、严格直接区间可靠性与非退化高斯阈值 | [完整解析论证](research/universal-schur-extraction/README.md)；Schur–Weyl、维数公式及中央极限定理为明确输入 | 非 Lean；协议允许全局纠缠酉预处理，不是普通固定态 LOCC 蒸馏 |
| 指定避免置换多面体的 Ehrhart 实根性 | (132,213)-避免族全部 d≥3 的负实根性 | [完整解析证明与有理证书](notes/ehrhart-uniform-real-rootedness/README.md)；d≤1000 使用原作者已发表有限定理 | 非 Lean；不泛化到任意置换多面体 |
| 恒等补齐永久量不等式 | Pan–Skandera–Wang Conjecture 9.3 的所述命题 | [完整书面推导](notes/permanent-inequality-padding/README.md)；直接由原作者 Theorem 8.18 推出 | 非 Lean；明确属于既有定理的推论 |

更多已备完整论证的专题及各自限制见[分类研究目录](RESEARCH.md)与[全部专题清单](SOLVED_PROBLEMS.md)。后续先积累书面结果，再按数学价值与依赖成熟度集中形式化；形式化完成后更新对应状态。

既有定理的完整书面推论：[高斯块范数与 PSD 二次型乘积及全部等号](research/written-breadth-20261014/README.md)。覆盖任意有限维、任意 PSD 协方差／二次型与全部正实幂，并明确复高斯的双协方差条件；借用并归属 Ouimet–Greaves 的版本固定定理。已独立内部核读，未 Lean 化，不计为本仓库解决原 GPC 或新增重大猜想。

## 尝试过的问题

按领域记录已有探索与阶段结果；详细目标、阅读范围和保全记录见
[分类尝试目录](research/research-attempts-20261015/README.md)。已完成证明的
精确成果列在上面的预印本与书面证明栏。

| 领域 | 尝试过的问题 | 阶段结果与入口 |
| --- | --- | --- |
| 高斯分析与概率 | Wishart 行列式乘积猜想；一般高斯多项式 U 猜想 | 完整目标未闭合；[阶段记录](research/research-attempts-20261015/README.md#高斯分析与概率) |
| 永久量、矩阵与设计 | 一般复 PSD Chollet；Ryser 设计；Lih–Wang；Minc 第六猜想；Ryser rank-six | 保留有限控制与路线分析；[分类记录](research/research-attempts-20261015/README.md#永久量矩阵不等式与设计) |
| 极值图论与离散几何 | Caccetta–Häggkvist；八维 Borsuk 的平衡切片路线 | 原目标仍开放；[尝试范围](research/research-attempts-20261015/README.md#极值图论与离散几何) |
| 理论计算机科学、学习与布尔分析 | 确定性 log-rank；强有标号样本压缩；完整 FEI | 完整猜想未闭合；Han Q3.1 辅助反例另列已审成果；[阶段记录](research/research-attempts-20261015/README.md#理论计算机科学学习与布尔分析) |
| 量子信息与理论物理 | NPT bound entanglement；全维 SIC；去极化容量阈值；Quantum PCP | NPT／容量／PCP 未闭合；SIC 因已有完整主张而结束该阶段；[状态与实际阅读范围](research/research-attempts-20261015/README.md#量子信息与理论物理) |
| 文献筛查与去重 | Sidorenko；Courtade–Kumar；有限能量 EPnI；Unique Games | 按已有完整主张及实际读限保留筛查记录；[候选筛查](research/research-attempts-20261015/README.md#文献筛查后未继续的候选) |

## 证明与复现

各项目的定理、证明范围、外部输入和复现命令均放在对应项目页面。完整 Lean 工程、形式化标准和机器审计记录集中在以下入口：

[形式化与验证记录](formalizations/) · [全部验证材料](verification/) · [分类研究目录](RESEARCH.md) · [五篇整合稿](manuscripts/README.md)

“完整 Lean”只适用于项目明确列出的具体定理；有限证书或成功构建不自动覆盖整篇论文。公开预印本的数学范围和未解决部分以各自 README 为准。

## 引用、版本与许可

引用时使用对应版本 DOI 及冻结源提交。后续修正或加强形成新版本并保留原记录。

[DOI 与 BibTeX](preprints/lean-certified-2026-10/README.md#本轮公开-doi) · [Release DOI 档案](releases/ZENODO_RECORDS.md) · [GitHub Releases](https://github.com/mxym/math/releases) · [不可变 Release 工作流](releases/README.md) · [变更记录](CHANGELOG.md) · [历史进展](RESEARCH_HISTORY.md)

[来源与权利声明](NOTICE.md) · [OpenAI/math 原许可证](third_party_licenses/openai_math_LICENSE.txt) · [文献比较](comparisons/)

公开稿件与 DOI 不等于期刊同行评审，也不自动认证原创性或历史优先权。各稿件注明借鉴的公开工作和自身贡献。保留已有许可证及第三方声明；未另行授权的原创材料保留全部权利。
