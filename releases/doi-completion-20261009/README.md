# 预印本版本 DOI 补齐

| 研究稿 | 版本 DOI | 冻结源码 |
| --- | --- | --- |
| 全图强 Chollet 不等式，2.0 | https://doi.org/10.5281/zenodo.23252138 | `4d2eefd40ee930216ccd8fc0f51e4bf694251967` |
| 恒等补齐与永久量不等式，已有版本 | https://doi.org/10.5281/zenodo.23248369 | `736f74074aec4e0e2fe079835f2cbf7669b4102c` |
| 归一化永久量余子式谱无界性，1.0 | https://doi.org/10.5281/zenodo.23252140 | `d850a08d7f3a2fa6534c85d84d3d976d6e502a64` |

Chollet 的新版本包含早期书面证明、完整 Lean 工程和已有独立核验记录；早期书面版本 DOI https://doi.org/10.5281/zenodo.23248359 保留于同一系列。完整 Lean 工程按上述固定提交归档，PR #10 已合入主分支。两个证明使用不同方法，分别给出阅读和复现入口。范围为任意有限简单无权图及其全部主子矩阵，保留原图度数。

余子式谱无界性档案含四页 PDF、TeX、完整解析证明、文献比较、内部审查和两种整数算法的有限证书。其 DOI 与已有的余子式谱锐渐近论文不同。本稿不声称 Lean 形式化。恒等补齐稿沿用已公开档案；没有重复创建 DOI，其命题内容与所引冻结提交一致。

## 公开归档核验

- [ARCHIVE_AUDIT.json](ARCHIVE_AUDIT.json)：核对两份新档案的全部字节、权限、清单，以及共 161 个原始 Git 文件；保留已有许可证和第三方声明。
- [PUBLIC_DOWNLOAD_AUDIT.json](PUBLIC_DOWNLOAD_AUDIT.json)：匿名读取三条记录，核对作者、ORCID、自定义权利声明、公开访问，以及每个附件的 SHA-256；确认版本 DOI 在 DataCite 为 `findable`。
- [FINITE_CERTIFICATE_RECHECK.json](FINITE_CERTIFICATE_RECHECK.json)：从冻结无界性档案重新运行两种独立整数算法，结果文件字节一致。有限证书不代替一般无界性证明。
- [PUBLICATION_STATE.json](PUBLICATION_STATE.json)：公开记录 ID、版本 DOI、冻结提交与附件清单；不含认证令牌。
- [ARCHIVE_CATALOG.json](ARCHIVE_CATALOG.json)：两份新档案的范围与上传文件哈希；[records/](records/) 保存提交的作者、许可和版本元数据。

本轮检查归档及已记录的证明证据，未重新编译或重放完整 Chollet Lean 工程。数学验证范围遵循冻结源码中的说明；本轮归档不构成新的外部同行评审。

重新做全部匿名下载核验：

```sh
python3 verify_downloads.py --fresh
```

不需要认证。使用标准 Python 3，不能启用 `-O`；核验程序依赖断言。已有许可继续有效，未另行授权原创材料保留全部权利。

作者：Yongxian Zhang（张永贤），华南理工大学计算机科学与工程学院；ORCID https://orcid.org/0009-0000-3864-3536。无外部研究经费，使用AI进行辅助研究。
