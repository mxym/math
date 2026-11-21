# Conway 99 图的有理特征空间与三角形投影

不假设图有自同构：−4 特征空间的行列式为平方类，Hasse 不变量仅在 2 和 7 为负。三角形投影在模 3、模 7 的秩均为偶数，且模 7 的秩至多 42。已有的 `n₃=708` 索引表只剩 `h=49`、`h=441`；该端点、完整二阶分支以及整图存在性均未排除。

[证明与文献比较](Theorem.md) · [局部算术复核](verify_local.py)。运行 `python3 verify_local.py` 可复核小规模精确计算。证明本身不依赖程序。内部审读，非外部审稿。

**先行结果。** [Wave 23](https://github.com/YesterdaysLemon/conway-99-research/blob/main/agents/2026-07-23-wave23-index-pranks.md) 连接投影秩和 Seidel 秩；[后续 Wave 66](https://github.com/YesterdaysLemon/conway-99-research#readme) 已有更强的模 7 秩范围。本文的两个端点索引候选也可从他们的后续结论推出，不称为新排除；本文给出独立的有理二次型推导与主 Gram 子式限制。

后续的[三角形邻域枚举](../../conway-99/triangle-rank/README.md)在一般情形下排除了模 7 的秩 28 和 30。
