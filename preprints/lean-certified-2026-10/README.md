# 已完整形式化主定理的预印本 / Lean-verified principal-result preprints

作者：张永贤（Yongxian Zhang），华南理工大学计算机科学与工程学院。
ORCID https://orcid.org/0009-0000-3864-3536；通讯邮箱 mxymmxym1@gmail.com。
无外部研究经费；使用 AI 进行辅助研究。

本轮将已有公开研究整理为九份署名清晰、证明可读、主定理与 Lean 入口一一对应的预印本。
“完整”针对下面明确限定的主定理；不表示仓库全部研究、所有附带结论或所有程序都已 Lean 化。
每篇提供 PDF、独立可编译的 TeX ZIP、形式化版本锁和复现入口。DOI 发布信息将记录在本页及 `PUBLICATIONS.json`。
当前 arXiv 仍需 math.CO 背书；Zenodo 预印本公开不等于已向 arXiv 投稿。

| 论文 | 页数 | 完整 Lean 主结论 |
|---|---:|---|
| [周期图染色系数无限对数凹性分类](cycle-chromatic-classification/README.md) | 5 | Every genuine cycle graph C_n, n >= 3; full absolute coefficients, zero extension; infinitely log-concave iff n <= 11. The graph/polynomial correspondence and all positive and negative cases are formalized. |
| [单纯形稳定性与锐指数](sharp-simplex-stability/README.md) | 9 | Actual convex bodies and projection-body deficit in every dimension d >= 3; upper bound for every maximum-volume inscribed simplex, and failure of every larger exponent using specified actual maximum simplices. Constants are explicit, not optimal. |
| [所有二次整环的有界步长图](quadratic-order-moats/README.md) | 17 | All quadratic orders, full planar real-linear embeddings, every fixed finite step bound; uniformly bounded component cardinalities and no injective infinite bounded-step walk. No effective numerical bound or strong prime-ideal PNT is claimed as a formalized result. |
| [连续幂渐近的稳健避让](continuum-power-avoidance/README.md) | 15 | The main robust power-asymptotic avoidance theorem, compact blocker, and geometric endpoint are fully formalized. The manuscript explicitly labels its ancillary method-obstruction proposition as a written proof, not a Lean theorem. |
| [有限群轨道原始—对偶定理](orbital-primal-dual/README.md) | 4 | Only the universal finite-action theorem, rational primal/dual attainment, all-atom sharpness and degenerate zero-optimum case. Separate explicit symmetric-group formulas in the parent note are not certified by this paper. |
| [熵多项式根猜想反例](entropy-polynomial-roots/README.md) | 4 | The k=11, r=10 counterexample with the original real-power parameter, its bridge to the integer equation, exact coefficients, strict signs and four distinct open-interval roots. No claim about the exact root count or the separate entropy inequality. |
| [单峰 CGF 素数阶因子猜想反例](cyclotomic-unimodal-counterexample/README.md) | 4 | The explicit degree-216 polynomial, strict unimodality, basic q-integer quotient, and exclusion of every prime-order cyclotomic factor. No degree-minimality claim. |
| [q-永久量半轴单调性反例](q-permanent-halfline/README.md) | 3 | Only the displayed 4-by-4 real rational positive-definite counterexample and its exact decrease between q=49 and q=50. Minimal dimension and the all-t>1 family from the older research note are outside this paper. |
| [复三行永久量—行列式全参数精确范数](complex-pencil-norm/README.md) | 6 | Exact best constant for every complex coefficient and every actual Mathlib 3-by-3 complex matrix, including zero rows. The coefficient lens is a corollary. The full equality classification and tensorization in the parent manuscript are outside this paper. |

## 已经发表的完整主定理论文

Bapat 指定复数有理反例与实对称整数反例存在定理已合并公开，
[DOI 10.5281/zenodo.23248431](https://doi.org/10.5281/zenodo.23248431)。本轮不重复发表该合并稿。

## 尚不按完整主定理论文发布的项目

- 高斯等质量全部 k、指定质量及固定质量反例：几何主链仍有形式化缺口。已有高斯测度原始—对偶包只是完成的优化组件。
- 任意图 strong Chollet：二分支撑、三角形和若干粘合/风车族已形式化；一般图所需全部依赖仍未闭合，不能用子类代替任意图。
- 复三行完整等号分类：范数主定理完整，等号分类尚未闭合。本文只发布精确范数主定理；完整 tensor norm 在原包有单独 Lean 入口，本稿没有将它并列为新的独立论文。
- 其余传输、覆盖、分数匹配与谱渐近笔记：现有局部 Lean 引理不能自动证明整篇主结论，仍保留原有书面证明/部分形式化标签。

## 本轮实际核验

- 周期图：重新从源文件编译全部 11 个自有证明模块和总入口，13 个根定理标准公理审计，错误 False 证明被拒绝；已核对远端成功 CI 对应 `098827e7de284cb70b1985733d6bc5a3656fdbf1`。
- 其他冻结包：校验公开源码/证明日志与原审计的哈希绑定；先前记录的完整空内核重放不冒充本轮新执行。轨道包仅 README 后续编辑，全部冻结证明及执行证据一致。
- 复三行精确范数：本轮重新编译全部九个主定理依赖模块，实际 Mathlib 矩阵主定理、全参数范数和系数域的三个公理审计仅含标准三公理，错误 False 证明被拒绝；不声称新执行空内核重放。
- 精确算术：周期图、熵多项式、CGF、半轴反例及单纯形证书重新运行；复范数两组各 4096 节点的有理多项式证书与损坏证书拒绝检查通过。
- 九篇在新临时目录编译三遍，最终无未解析引用、缺字或 overfull 警告，PDF 字体嵌入；逐页渲染检查没有发现裁切、重叠或表格出界。
- 本轮核验属于 AI 辅助审查与可重放的机器证据，没有外部专业数学家或人工同行评审。

[主定理对应清单](CATALOG.json) · [排版核验](audit/BUILD_AUDIT.json) · [周期图本轮复核](audit/CYCLE_FRESH_VERIFICATION.json) · [冻结源码完整性](audit/SOURCE_INTEGRITY.json)

可在本目录运行 `python3 build.py` 重新编译所有稿件。数学证明使用各包指定的 Lean 复现命令；`build.py` 只检查排版。

## 许可与公开时间

保留所有已有许可和第三方声明；未获新授权的材料保留全部权利。
冻结源文件不因本文改写而被回填成更早完成的状态。
DOI 提供持久引用和公开档案；不自动认定数学正确性、原创性或世界优先权。
