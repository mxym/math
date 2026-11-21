# Conway 99 图：二阶分支的十五维 Hamming 格

假如 Conway 99 图存在，并有一个只固定一个顶点的二阶自同构，它的无符号外层轨道格可放入十五维标准整数格。完成 7 部分的整格扩张后，得到的格必须是**二元 Hamming 码的整数原像**，最小平方范数为 3。由此强制的两两正交稀疏记录从此前的至少七条增加到**十五条**。42 个外层轨道都由五个带符号坐标表示；每对同支撑标签的五点支撑只剩六种选择。

结论覆盖带符号模 7 秩 11 和 13。它把二阶分支限制在一个明确的无符号模型中，但没有证明该模型不可能，也没有解决 Conway 99 图。

- [主定理与归约](Theorem.md)
- [二元格类型与精确筛选](unsigned15/BinaryCharts.md)、[短向量剖面](unsigned15/RootsBridge.md)、[3,580 类图布局的两阶段判定](unsigned15/SingletonSearch.md)
- [复核与近期平行工作](Review.md)
- [完整离线复核包](Conway99_Involution_UnsignedSimplex_Exact.zip)，SHA-256：`f59122cc87e939d76782b7e9108e72af925391c779e4f931ec715a332549d05e`

在解压后的 `singleton-simplex-packet/` 运行 `bash replay.sh quick`；`bash replay.sh full` 再完整重跑第一层。原始完整第一层约 40.9 核分钟，两个互补分片使用同一套程序。
