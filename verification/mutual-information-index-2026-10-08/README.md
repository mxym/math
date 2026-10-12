# 互信息连续性反例的索引核验

2026-10-08（客户端时区）。PR #12 已合并；书面 v1 固定 `a179e33532707abe09247d87aad484e9965847b4`，完整经典 Lean v2 固定 `363224e0f7cf1d7ea7b4ed2546f8ed372da7b04c`。两个 Release 不可变；全部 13 个附件已实际下载，逐字节 SHA-256 与平台摘要吻合。本地两个冻结源码清单也通过核对。

实际源码从概率表、非负性、归一化、行列边缘和 Shannon 熵定义出发，严格证明总变差为 ε、互信息差为 `2h(ε)−εlog2`，对所有 `0<ε≤1/16` 违反 `h(ε)+εlog8`，并在任意正距离邻域内存在反例。独立 LiteralSemantics 校验也证明两侧边缘都变化。

既有记录报告 38 个自有声明及 16,161 个依赖的空内核 trust-level-0 重放，只有三个标准公理，错误 False 证明被拒绝。本轮阅读源码、核对声明语义、字节清单和这些既有记录，**没有重跑 Lean 内核**，也没有完成全文献查重。

原始 arXiv v2 Eq. (106) 已实际读取，措辞是一般拟议界，不是已证明定理。固定一侧边缘的版本仍未解决。量子对角嵌入和必要主导系数至少 2 是书面论证，不能算作完整量子 Lean。

Zenodo 自动归档已存在：https://doi.org/10.5281/zenodo.23253152。它是整仓库软件快照，概念 DOI 属于仓库级系列。本轮修正其自动作者列表为 Yongxian Zhang／ORCID／SCUT，AI 披露为辅助工具；保留原软件类型、DOI、文件字节及已有 CC BY 4.0 元数据，不声称撤销既有许可。正式署名的论文版另作预印本归档。

[附件与源码核验](RELEASE_AND_SOURCE_AUDIT.json) · [原命题定位](PRIMARY_SOURCE_CHECK.json) · [自动归档作者修正](AUTOMATIC_ARCHIVE_AUTHOR_CORRECTION.json) · [现行署名论文](../../preprints/mutual-information-continuity-2026-10/README.md)。
