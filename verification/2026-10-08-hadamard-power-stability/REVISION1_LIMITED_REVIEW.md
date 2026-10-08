# Hadamard 稳定性第一修订版限定复核回执

日期：2026-10-08 UTC

结论：**限定复核通过。上一轮所列必须修正及建议澄清均已正确落实，没有新增修订要求。** 结合此前完整审核，修订版可标记为“通过本轮独立解析审核及限定修订复核”。这不表示形式化验证、期刊同行评审、历史优先权认证或发布。

## 范围及版本

本次仅检查 `research_math/hadamard_stability_revision1_20261008/REVISION_NOTES.md`、`revision1.diff`、六个变更文件的必要上下文，以及版本完整性。没有重做全系列数学审查，没有运行数学检查脚本或 Lean 构建，没有修改冻结目录，也没有发布。

已核验：

- `revision1.diff` SHA-256：`bb4693170b5c70de2b71eb168c103af20c1af2a83bbe67d6cf501658ac1254be`
- 修订 manifest SHA-256：`d4d95197e4e80dbc57c4cab08fde5541caf427dfb35392a61dfe5dd90fc27669`
- 修订版 14 个 manifest/SHA256SUMS 条目全部匹配。
- 原冻结版 12 个文件及其 manifest 保持原样。
- 从原版和修订版重新生成的完整 inherited-file diff 与给定 `revision1.diff` 逐字一致；确实只有声明的六个 inherited 文件发生变化。
- 两份 referee 输入和三份外部精确分类输入均匹配修订 manifest 中的字节数与 hash。

## 改动验收

1. **权重摘要**：INDEX 与 CHECKPOINT 现在明确排除 `c=1`、`c=2` 或 `c≡3 (mod 4)`，不再误排全部余数类 1 和 2。R1 已解决。
2. **ordinary isolation 范围**：修订正确区分 ordinary isolation 和 zero ordinary defect；只声明 zero ordinary defect 蕴含 zero simultaneous defect，并明确未解决 Conjecture 4.5。R2 已解决。
3. **MUB 和 Gauss 去相位桥梁**：新段落中的归一化 `1/sqrt(2)`、转回单位模的 `sqrt(2p)`、两个 completing-square 指数、底行首项除法及常数 `-gamma(-q)/gamma(-1)=-chi(q)=1` 均正确。它恰好导出原来的四块指数，没有扩大为与 Butson 原始构造全族等价的声明。
4. **标量引理适用范围**：新增说明正确地把初始全一行列平凡处理，仅对其余行列使用小矩条件。
5. **兼容性定义**：新增 restricted row-ratio multiset 定义与原证明及外部构造一致。
6. **局部指数定义**：已明确固定 K0、单位模去相位邻域、可依赖 K0 的有限常数及对邻域内所有 K 的量词，并用 supremum 定义最佳指数；与原分类一致。
7. **索引状态**：准确记录本修订待限定复核的形成历史，且没有把先前审核加强为形式化或优先权认证。

主定理、残差门槛、数值常数、图判据、二阶分类、算术证书与例子没有变化。因此本回执解除的是上一轮的小修条件；原完整报告中关于一般奇数图连通性、新 seed 存在、ordinary isolation 猜想及优先权的限制继续有效。
