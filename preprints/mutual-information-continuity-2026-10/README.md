# 一般互信息连续性拟议界的三元反例

Yongxian Zhang（张永贤），华南理工大学计算机科学与工程学院。
ORCID: https://orcid.org/0009-0000-3864-3536；mxymmxym1@gmail.com。

[正式署名 PDF](paper.pdf) · [独立 TeX ZIP](paper-source.zip) · [完整经典 Lean 工程](../../formalizations/mutual-information-continuity-counterexample/README.md)。

独立预印本版本 1.0 DOI：https://doi.org/10.5281/zenodo.23253944；[公开附件与 DOI 核验](../../releases/mutual-information-preprint-20261008/README.md)。

对 Berta–Lami–Tomamichel，arXiv:2408.15226v2，Eq. (106)（v1 Eq. (54)）所提出的一般互信息连续性界，构造实际 3×3 联合概率表。对每个 `0 < ε ≤ 1/16`，总变差距离为 ε，互信息差恰为 `2 h(ε) − ε log 2`，严格大于拟议界 `h(ε) + ε log 8`。因此任意小的正距离邻域中都有反例。

**范围：** 两侧边缘均变化；固定一侧边缘的版本未被解决。经典概率表、熵、实际距离及任意小距离结论有完整 Lean。对角量子嵌入与必要主导系数至少 2 的结论有完整书面证明，尚未 Lean 化；没有求出有限距离的完整最优模量。

**记录：** 固定源码提交 `363224e0f7cf1d7ea7b4ed2546f8ed372da7b04c`。既有独立空内核 trust-level-0 复核覆盖 38 个自有声明及 16,161 个依赖，只准许三项标准 Lean 公理，含错误证明拒绝和实际概率表的独立语义检查。本轮核对这些记录及字节绑定，不冒充新的 Lean 重放。

[v1 书面冻结版](https://github.com/mxym/math/releases/tag/mutual-information-continuity-counterexample-v1) · [v2 完整经典 Lean 冻结版](https://github.com/mxym/math/releases/tag/mutual-information-continuity-counterexample-v2-lean)。两者均不可变。当前署名稿只更新展示与证明状态，不修改冻结正文或 Lean 源码。

Zenodo 自动生成的整仓库软件快照：https://doi.org/10.5281/zenodo.23253152。该记录的概念 DOI 是仓库级系列，不当作这篇论文的独立版本系列。

从仓库根目录重编：`python3 -B preprints/mutual-information-continuity-2026-10/build.py`。Lean 新复核按固定工程的 README 执行。无外部经费；使用AI进行辅助研究，研究与写作披露分别列在文中。

来源与权利：保留已有许可和第三方声明；新稿未另行授权部分保留全部权利。自动归档记录已有 CC BY 4.0 元数据，本轮不声称撤销该许可。未认证世界首次或历史优先权，未声称外部专业同行评审。
