# APPT 共存曲线的方向与全部固定 r 切片

在[原完整标量相图](../appt-linear-phase-diagram-20261015/README.md)的基础上，完整稿证明两条共存曲线 r_B(c)、r_P(c) 在 0<c<c_* 严格递增，端点分别为 0 和 r_*；三相点斜率满足

    0 < r_P′(c_*) < r_0′(c_*) < r_B′(c_*).

因此每个固定 r 的整个正 c 轴上，极值相的先后顺序与全部二相／三相平局均得到分类；0<r<r_* 时只有一个混合相区间，且有明确的水平闭合首项。证明先计算固定 r 的临界值偏导，再沿共存曲线求导。

- [完整作者稿与全部切片表](author-v1/PAPER.md)及[定理对应表](author-v1/THEOREM_MAP.md)
- [独立数学审读](author-v1/INDEPENDENT_REVIEW.md)与[机器可读结论](author-v1/INDEPENDENT_REVIEW.json)
- [原始作者与审读字节绑定](OWNER_SOURCE_BINDINGS.json)

标量结论覆盖全部 c>0、r≥0。转移到实际 APPT 矩阵仍限原窗口 m→∞、α/m→固定正 c、3^α/D→有限 r，并保留完整 argmax 距离、实际主体 spread 和 peak 损失。这里没有扩张到 c 随维数趋零／无穷或有限维精确谱。

作者 Yongxian Zhang（张永贤），华南理工大学。无外部经费；OpenAI AI assistants 协助。原创材料保留全部权利，第三方归属沿用原文。

所列稿件均有覆盖原对象、假设与量词的完整普通数学证明，并分别完成内部独立 AI 数学审读。这不表示完整 Lean 形式化、外部人类同行评审或历史优先权认证，也不增加独立重大猜想计数。最终源码／公开状态绑定见 [FINAL_STATUS_BINDING.json](FINAL_STATUS_BINDING.json)。
