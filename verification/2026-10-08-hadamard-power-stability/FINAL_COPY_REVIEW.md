# Hadamard 公开稿最终拷贝限定复核回执

日期：2026-10-08 UTC

**结论：限定一致性复核通过，当前没有待修的拷贝或数学表述问题。** 此结论把下面指定的最终 PDF/LaTeX 版本与已审 revision1 联系起来，并单独确认本轮的两项实质编辑修正和一项书目修正；不是重复完整数学全审，也不等于期刊同行评审、形式化验证、优先权认证或发布许可。

## 最终文件身份

目录：`research_math/hadamard_series_manuscript_20261008/`

- PDF：27 页，491481 字节。
- 最终 PDF SHA-256：`53ed15d469ae89d8735778b411431fe5e8c4b4ce774249478585e6c59da4d334`
- `references.tex` SHA-256：`91b6b8f5119fa3bf9a841632d3787da4351d1d732309b03904610703535a43d3`
- 本次检查时 `RELEASE_MANIFEST.json` SHA-256：`10e428126d6efac861074f52b10053690caca7ea9517b324a63b7e090967a72e`

最初送审 PDF `aa97f34707b2e2f502a475e083009621dfa2399594b76e38fb918944bcd62377` 已由上述书目更正版取代；旧版完整保存在 `hadamard_series_manuscript_20261008_before_bibliography_fix/`，其原 hash 清单仍匹配。

新版本全部 28 个 release manifest 条目及 SHA256SUMS 核验通过。原 revision1、三份外部输入、两份前期审核文件与两个 certificate 副本的身份均与 provenance manifest 一致。

## 拷贝和定理范围

逐节读取了主 LaTeX、十节、两附录及参考文献，并依 SOURCE_MAP 对照已审八篇笔记。以下内容保持：

- 精确单位模、阶数 `n=2m`、全部 `1≤k<m` entrywise powers、未经归一化算子残差及 labelled dephasing。
- `2^-24 m^-3` 全局门槛和 `512 sqrt(epsilon/m)` 距离；奇 m 的实际根舍入、全阶可选兼容矩形以及严格非存在残差间隙。
- Newton、分离多边形重数、公共支持、半整数 trace、全频率 Fourier 整数计数和非根 `512epsilon/s` 的完整依赖链。
- `dim V_G=r-1` 图内核、连通性条件、`2^-34 m^-5` 与 `48H_(m-1)epsilon`；没有扩大为所有奇数图连通。
- quadratic family 的全部参数限制、四块指数、Gauss 去相位、邻接公式、直径七，以及 `2^-34 p^-3` 和 `56H_(p-1)epsilon/p`。
- 二阶 admissibility 的 iff、实系数和共轭幂条件、零/兼容矩形速度、`Y∈V_G`，以及不保证任意指定 acceleration 延拓成 exact curve 的限制。
- 局部最佳指数的 neighborhood/constant 全量词、全部 r/b 分支、nonroot 情形及两个显式局部半径。
- source attribution 的两层来源、ordinary isolation 与 zero ordinary defect 的区别、开放问题和优先权限制。

附录 B 的两个排版指数矩阵已逐整数解析比较，分别与未改动 certificate 脚本中的 E3/E5 完全一致。表内精确秩、行列式、逆范数和正文常数没有丢失。

## 两项新修正的独立确认

### 可选兼容矩形

摘要中的 “and, when needed, a compatible phase rectangle” 与 Theorem 3.2 的 `T=G` 或 compatible-circle point 二择一致。不能无条件声称所有 half-order 都产生兼容矩形，因为奇 m 情形没有这类矩形。现稿已正确修复。

### 外部 order-four 例子的标签

对稿中显示的实种子 G，旧标签 `R_old={2,3}`、`S_old={2,3}` 不兼容：行 2 对行 0 在列 2、3 上的根比为 `(-1,-1)`。把该旧块乘以 alpha 后，行 0 对行 2 的 Gram 项为 `2-2 conjugate(alpha)`，一般不为零。

修订标签 `R={1,3}`、`S={2,3}` 正确，全部跨组根比依次为：

- a=1,b=0：(1,-1)
- a=1,b=2：(-1,1)
- a=3,b=0：(-1,1)
- a=3,b=2：(1,-1)

每半边恰含两个根各一次，所以新矩形满足 compatibility。所得相位族的同组 Gram 项不变、跨组两半和分别为零，全部行范数平方为四；因此对每个单位 alpha 都精确 Hadamard。Appendix A.5 使用的正是这组标签。

此项是对先前审查的补充：上一轮报告没有指出外部边界例的这个标签错误。外部精确分类的一般证明、正文 order-four sharpness 曲线及主稳定性定理均不依赖这个错误放置，因此审核主体结论不受影响。原外部快照未被改写；EDITORIAL_CORRECTIONS 已透明记录原错和修正。

## 本轮发现并解决的书目问题

原 `references.tex` 将 Duygu Özteke 缩写成 O. Özteke。本轮指出后，作者已改为 D. Özteke。该修正与此前查阅的 arXiv 原文作者名一致。

已核验前后所有主文件与 sections 的 `.tex` 字节相同，只有 `references.tex` 中这一字母发生变化。重新渲染最终 PDF 后，27 页中只有第 26 页 PNG 变化；该页已再看，缩写现为 D.，版面正常。

## PDF 层核验与停止条件

原送审 PDF 的 27 页已全部独立渲染查看，最终版的未变 26 页经 PNG hash 一致性复核、变化的第 26 页重新查看。未见截断、漏字、丢公式、缺失矩阵项或重叠。编译 log 没有未定义引用、缺字或 overfull 报告；文件页数为 27。

本轮没有编辑公开稿、运行新的数学参数搜索、进行 Lean 构建或发布。最终 copy check 到此完成。任何后续数学内容修改需要另行复核；单纯将这份回执加入 provenance 会改变 release manifest，但不会改变上述已审 PDF 身份。
