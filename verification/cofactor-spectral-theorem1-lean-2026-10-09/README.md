# 余子式谱 Theorem 1：公开形式化范围核对

PR #11 已合并到 `main`，合并提交为 `21e1f769e9ac90f161f0be575b4f19adc642ffd3`；形式化工程固定在该提交中的 `formalizations/cofactor-spectral-asymptotics-progress/`。随后以索引提交 `f8343f8e0b6b3638896bd092b9b476e406660a05` 创建了[不可变 GitHub Release `cofactor-spectral-theorem1-lean-v1`](https://github.com/mxym/math/releases/tag/cofactor-spectral-theorem1-lean-v1)，其平台状态为 `immutable=true`。

## 已覆盖命题

固定工程的主入口为 `CofactorSpectral.sharp_cofactor_spectral_asymptotics`。它形式化同一数学来源 `df6d94763c852c3cf69f29c5fa95c51f88378160` 的 Theorem 1：

- 一般复 Hermitian PSD 矩阵（永久量为正）；
- 精确秩二相关矩阵；
- 正定相关矩阵（正定扰动可提高秩）；
- 三类输入的复方向极限均为 1；
- 三类输入的实方向极限均为 1/2。

“实方向”使用余子式复合矩阵的逐项实部，但输入仍允许复 Hermitian 矩阵；它不是“实对称输入矩阵”版本。谱极值与 Rayleigh 变分量的等价、实际永久量和未转置余子式定义均在工程内证明。

## 机械复核记录

工程 README 和固定 `verification/` 材料报告：78 个模块 fresh 编译，745 个自有声明，完整传递闭包 55,731 个声明从空内核以 trust level 0 重放；请求根联合闭包为 55,515。无自定义公理、`sorryAx`、unsafe 或 partial 自有声明；仅出现 `propext`、`Classical.choice`、`Quot.sound`。错误证明负向测试被拒绝，递归审计已将编译器生成的 partial 辅助声明改为显式 `Nat.rec`。

本文件是仓库索引核对：本轮读取主入口、`SEMANTIC_REVIEW.md`、`case.json`、`replay-summary.json`、标准公理记录和提交状态，确认它们的范围描述一致；**本轮没有重新运行 Lean 内核**。实际复现命令、固定编译器和依赖版本见[形式化工程 README](../../formalizations/cofactor-spectral-asymptotics-progress/README.md)。

## 未覆盖范围

同一书面论文后续的 ramp 常数、rank-two endpoint 和 immanant 命题不属于本次 Theorem 1 证书。该工程的完成状态不自动证明整篇论文的所有后续结论，也不构成外部同行评审或历史优先权认定。

[工程 README](../../formalizations/cofactor-spectral-asymptotics-progress/README.md) · [来源对应审查](../../formalizations/cofactor-spectral-asymptotics-progress/SEMANTIC_REVIEW.md) · [主分支合并提交](https://github.com/mxym/math/commit/21e1f769e9ac90f161f0be575b4f19adc642ffd3) · [不可变 Release](https://github.com/mxym/math/releases/tag/cofactor-spectral-theorem1-lean-v1)
