# 理论研究记录 · 2026-11-20

这批材料收录已完成内部数学审读和相关精确复核的研究稿。每项的判定范围见表；证明、参考文献和复核说明在对应目录及原样保存的 ZIP 中。研究稿为 AI 辅助的内部复核成果，未经外部同行评审；不作全球优先权声明。无版本 DOI。

| 题目 | 结论与范围 |
| --- | --- |
| [21 位二元纠错码](binary-a21/README.md) | 无对称性假设：42 ≤ A₂(21,10)=A₂(20,9) ≤ 46，原上界 47。两套精确证书核验；最优值开放。 |
| [七环强幂](../odd-cycle-shannon-capacity/finite-fourth-power-2026-11/README.md) | 108 ≤ α(C₇⊠⁴) ≤ 113；第五强幂上界 395。只改进有限幂上界，不是香农容量上界。 |
| [反对称态的纠缠成本](antisymmetric-entanglement/README.md) | 所有 d≥2 的归一化反对称态，任意 n 份的形成纠缠为 n ebit，渐近 LOCC 成本恰为 1 ebit。不包含一般 Werner 混合态。 |
| [四、五费米子二体边缘态](fermion-pair-purity/README.md) | 归一化二体边缘态的纯度锐界分别为 1/6、1/10；等号为 Slater 态。 |
| [Yang 的四形式外积界](yang-four-forms/README.md) | 4+4 外积范数平方的维数无关锐界为 6；有限维精确公式仅断言于已证明的大维数范围。 |
| [带噪 Strange 态的渐近魔性](strange-relative-entropy/README.md) | 给出归一化稳定子集合上的渐近相对熵及严格非可加区间。这不是蒸馏速率。 |
| [二量子比特与三量子比特魔性](qubit-magic-alignment/README.md) | 混合稳定子对齐的张量封闭性、双量子比特的边界 Rényi 可加性，以及固定三量子比特反例的任意副本数精确值。 |
| [Strange 态的无限二次剩余蒸馏码族](qutrit-qr-strange/README.md) | 所有素数 p≡11 (mod 12) 给出三能级码，每个码的阈值严格正且低噪声下至多三次方误差；不主张统一阈值或打破阈值纪录。 |
| [Bell 统计证据与上下文秩](bell-contextuality/README.md) | 一般双边设置图的渐近证据上限、任意整数的量子上下文秩，以及分数覆盖的正则化公式。双边各两设置的特例已有先行结果。 |
| [量子策略的几何 Rényi 散度](geometric-renyi-combs/README.md) | 任意有限轮量子策略的测试者公式，并证明 Hirche 的嵌套摊销等式；不涉及不同的全摊销式或 Stein 指数。 |
| [零误差通信与延迟可加性](delayed-zero-error/README.md) | Shirokov 的 S_*(k)=∞ 猜想；固定输入输出维数的最小输出 Rényi 熵可加性可任意晚才破裂。固定维数不主张能指定首次长度。 |
| [量子信道组合的零误差可达性](zero-error-coalitions/README.md) | 任意不含空集的向上封闭集合族均可实现：允许的组合一次即可传输量子系统，其余组合任意多次也无法零误差传输一个比特。 |
| [纯态的投影测量排除](pure-state-projective-exclusion/README.md) | 状态数不超过维数时，一般 POVM 能完美排除则投影测量也能；平方情形每个已指定标签一个秩一投影。不是任意混态结论。 |
| [Conway 99 图：奇 Leech 补格](../conway-99-involution/odd-leech-frame/README.md) | 在单固定点二阶分支的秩 13 情形排除 32 类带标记奇 Leech 补格；不排除其他补格。 |
| [Conway 99 图：两类有根补格](../conway-99-involution/rootful-frame-pair/README.md) | 秩 13 分支排除 4D6 与 2A7+2D5 两类；不排除整个二阶分支。 |
| [Conway 99 图：反不变能量下界](../conway-99-involution/dual-minimum-ten/README.md) | 在单固定点二阶分支，非零整数反不变 −4 特征向量的折叠能量至少 10。这里收录数学归约和证书摘要；约 572 MB 的全量重放材料未随本提交上传。 |
| [Conway 99 图：6D4 与 8A3](../conway-99-involution/frames-6d4-8a3/README.md) | 秩 13 分支另排除 6D4 和 8A3；这一证书使用反不变整数最小特征向量的能量下界 E≥10。 依赖的能量定理请先读上一条；此包不是全量自包含重放。 |

## 补充收录

下表包含此前已复核、这次补入仓库的材料，以及纯态排除结果的后续定理。

| 题目 | 结论与范围 |
| --- | --- |
| [固定维数的精确 PPT 纠缠成本](ppt-state-fixed/README.md) | 总维数 D 的下 SDP 层级至迟在 D²+2D 层稳定，给出任意固定维数态的零误差 PPT 操作成本。不主张层级界最优。 |
| [双 qutrit 精确 PPT 成本的第二上层](ppt-qutrit-upper/README.md) | 所有双 qutrit 态 κ₂=χ₂；χ₂ 等于精确成本的指数是 Song–Zong–Yang 既有结论。重放须另取已固定版本的原始证书。 |
| [点对点信道的精确并行 PPT 模拟](ppt-parallel-channel/README.md) | 给出完全 PPT 保持辅助下的并行精确模拟成本与强可加性。不是自适应、顺序、近似、LOCC 或双向信道结果。 |
| [同基 DOC 的 PPT 映射三重复合](ppt-doc-three/README.md) | 共同基底中的三个 DOC PPT 映射合成后为纠缠破坏；不解决不受限制的 PPT 三次猜想。 |
| [不可分解的 k-纠缠破坏正映射](keb-indecomposable/README.md) | 每个固定 k 都存在有限维有理不可分解 k-EB 正映射，且可同时使伴随映射 k-EB；证明为存在性，不是给出所有参数的显式系数。 |
| [五维显式 2-纠缠破坏正映射](keb-explicit-m5/README.md) | 给出 M₅ 上不可分解的显式 2-EB 正映射，保单位、保迹；不是物理完全正信道。 |
| [Krebs–Gachechiladze 方格族的 Schmidt 数](kg-schmidt-square/README.md) | 把指定构造的精确 Schmidt 数证明推广到全 k；不主张任意 PPT 态的最大 Schmidt 数。 |
| [七维三元仿射帽集](affine-cap-seven/README.md) | 无对称性限制的上界 281；已知下界仍为 236，最优值开放。 |
| [PG(6,3) 射影帽集](projective-cap-six/README.md) | 无对称性限制的上界 135；已知 112 可构造，最优值开放。 |
| [循环称重矩阵 CW(155,100)](cw155/README.md) | 在指定阶与权重下的循环称重矩阵不存在；不是所有称重矩阵或其他参数的结论。 |
| [循环称重矩阵 CW(182,144)](cw182/README.md) | 在指定阶与权重下排除全部循环候选，包括非本原情形。 |
| [18 维等角线：部分拉丁锚](eql-latin-anchor/README.md) | 任何这类 34 格拉丁锚均不能扩成 58 条；无锚的一般问题仍开放。 |
| [18 维等角线：K₁₀ 锚](eql-k10-anchor/README.md) | 所述正确着色的 K₁₀ 的 45 线锚精确最多扩到 57 条；不主张 N(18)=57。 |
| [18 维等角线：假想 58/59 条的对称群](eql-solvable/README.md) | 排除素数 p≥5 的对称，故相关对称群可解；不排除 58/59 条等角线本身。 |
| [纯态排除的锐扩维界与条件误差](pure-state-projective-exclusion/companion/README.md) | 最小扩维与稀疏 Gram 秩公式、候选列表大小的投影测量分类、一个确定性投影测量逐状态不劣于任意给定 POVM，以及 Bures–Wasserstein 最优误差公式。 |
