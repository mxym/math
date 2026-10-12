# 余子式谱论文 v1.2 DOI 归档

修订版 1.2 DOI：**https://doi.org/10.5281/zenodo.23255145**

[修订论文与 PDF](../../preprints/article-revisions-2026-10/sharp-cofactor-asymptotics/README.md) · [完整 Lean Theorem 1 工程](../../formalizations/cofactor-spectral-asymptotics-progress/README.md) · [不可变 GitHub Release](https://github.com/mxym/math/releases/tag/cofactor-spectral-theorem1-lean-v1) · [范围核对](../../verification/cofactor-spectral-theorem1-lean-2026-10-09/README.md)。

这是既有论文系列 `sharp-cofactor-spectral-asymptotics` 的版本 1.2，前一版本 DOI 为 https://doi.org/10.5281/zenodo.23252986；前一版本及其附件保持不变。新版本加入 Theorem 1（含正定扩展）的完整 Lean 形式化说明和固定复核入口，不把后续 ramp、rank-two endpoint 或 immanant 命题列入形式化证书。

## 公开附件

归档固定源提交 `be36cfdf363c2d2138ec381aad9ba499088e2fc3`，包含十页 PDF、独立 TeX ZIP，以及含修订稿、原书面证明、完整形式化工程和验证范围记录的源码 TAR.GZ。三个附件的字节数和 SHA-256 见 [CATALOG.json](CATALOG.json)。

所有附件均已匿名下载并逐字节核对；DataCite DOI 状态为 `findable`，作者、ORCID、公开权限和自定义权利声明均核验通过。已有许可和第三方声明继续有效，未另行授权的原创材料保留全部权利。

## 证明范围

Theorem 1 的六个对数主项极限已由公开 Lean 工程形式化：三类输入矩阵的复方向极限为 1，实方向极限为 1/2；实方向仍允许复 Hermitian 输入。公开记录报告 78 个模块、745 个自有声明和 55,731 个传递依赖的空内核 trust-level-0 重放。本次归档核对这些公开记录和附件，没有重新运行 Lean 内核。

- [归档清单](CATALOG.json)
- [版本状态](PUBLICATION_STATE.json)
- [本地归档审计](ARCHIVE_AUDIT.json)
- [匿名下载与 DOI 核验](PUBLIC_DOWNLOAD_AUDIT.json)
- [可重跑检查器](verify_downloads.py)：在本目录执行 `python3 verify_downloads.py --fresh`
