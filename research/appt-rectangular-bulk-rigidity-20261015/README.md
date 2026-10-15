# 有界熵阶下 APPT 主体谱的定量 W₂ 刚性

研究实际复数密度矩阵，APPT 条件量化到每一个全局酉变换。令 D=mn、γ=n/m，固定任意有限 A>0；在 m→∞、0<α≤A、αγ→∞ 时，对全部 n≥m 和实际状态一致成立，允许 α 趋零、跨越 1 和维数振荡。

记 eα 为该状态的熵缺口，Eα 为实际 APPT 最大缺口，dα=1−eα/Eα，ε=1/m+1/(αγ)。设 ν 为实际全谱 m(Dλ−1) 的经验分布，β=(δ₋₁+δ₁)/2。完整稿证明

    eα/Eα→1  iff  W₂(ν,β)→0,
    W₂(ν,β) ≤ C_A (dα+ε)^(1/4).

四分之一次幂由真实整数秩 APPT 投影态达到其锐尺度，不能改成更大的幂次。证明保留主体均值、弦内 spread 和异常部分二阶矩；允许最大归一化特征值持续偏离 1。

- [完整作者稿](author-v1/PAPER.md)与[定理对应表](author-v1/THEOREM_MAP.md)
- [独立数学审读](author-v1/INDEPENDENT_REVIEW.md)与[机器可读结论](author-v1/INDEPENDENT_REVIEW.json)
- [原始作者与审读字节绑定](OWNER_SOURCE_BINDINGS.json)

本结果需要有界阶数及 αγ→∞；不包含固定 m、无界 α、任意有限维精确极值或全阶几何谱分类。

作者 Yongxian Zhang（张永贤），华南理工大学。无外部经费；OpenAI AI assistants 协助。原创材料保留全部权利，第三方归属沿用原文。

所列稿件均有覆盖原对象、假设与量词的完整普通数学证明，并分别完成内部独立 AI 数学审读。这不表示完整 Lean 形式化、外部人类同行评审或历史优先权认证，也不增加独立重大猜想计数。最终源码／公开状态绑定见 [FINAL_STATUS_BINDING.json](FINAL_STATUS_BINDING.json)。
