# 研究稿的署名与文章修订版

五份既有数学稿的文章修订版，保持原证明及固定计算输入，补全 PDF 作者信息、复现入口和研究／写作 AI 使用说明。

| 文章 | 阅读 | 数学与证据范围 |
| --- | --- | --- |
| 指定置换多面体族 Ehrhart 实根性 | [正文与 PDF](ehrhart-real-rootedness/README.md) | 全部 d ≥ 3；d ≤ 1000 明确引用既有有限范围定理，余下有完整书面证明与精确证书 |
| 恒等补齐永久量不等式 | [正文与 PDF](permanent-padding/README.md) | 既有平衡定理的完整短推论；不是独立重证原定理 |
| 余子式谱无界性 | [正文与 PDF](cofactor-spectrum-unbounded/README.md) | 排除维数无关常数；有限见证不代替解析证明 |
| 余子式谱的锐渐近 | [正文与 PDF](sharp-cofactor-asymptotics/README.md) | 全大阶对数渐近；实方向仍允许底层矩阵为复数 |
| 指定质量高斯一阶矩 | [正文与 PDF](gaussian-prescribed-mass/README.md) | 质量依赖度量中的锐界，使用已发表多泡定理；Lean 为部分覆盖 |

这五篇均有完整书面证明，未声称完整 Lean。证明正文、引用的输入以及计算程序的作用分别保留。[Chollet 正式重写稿](../all-graph-chollet-2026-10/README.md)有另行完整 Lean 证明。

从仓库根目录运行 `python3 preprints/article-revisions-2026-10/build.py`，在临时目录重编五份修订版和 Chollet 正式稿，生成 PDF、可独立编译的 TeX ZIP 和各稿的排版核验记录。原公开版本保留；新版本 DOI 按发表记录补齐。

作者：Yongxian Zhang（张永贤），华南理工大学计算机科学与工程学院，ORCID https://orcid.org/0009-0000-3864-3536。无外部研究经费，使用AI进行辅助研究。
