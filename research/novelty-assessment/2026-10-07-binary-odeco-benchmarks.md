# 二元全阶 ODeCo 定量基准：文献初筛

检查日期：2026-10-07。本文仅比较下列二元完全对称张量公式是否见于已核对的公开先例，不复核仓库证明，也不作 priority 判断。这里固定 Frobenius 张量范数、实正交分解，并将所有有序的长度 \((p-2)\) 收缩指标计入
\[
R(T)^2=\sum_{\alpha,\beta}\|[X_\alpha,X_\beta]\|_F^2,
\qquad X_\alpha=T_{\alpha_1,\ldots,\alpha_{p-2},\cdot,\cdot}.
\]
因此指标是否有序、交换子是否按有序对求和、张量坐标范数是否含排列重数，都会影响常数。以下以这些约定下的目标式为准。

## 待比对的三个精确主张

1. 对每个二元实对称 \(p\)-张量，\(p\ge3\)，
   \[
   \operatorname{dist}_F(T,\mathrm{ODeCo}_{2,p})\le \frac{\sqrt p}{2}\sqrt{R(T)}.
   \]
2. 当 \(p=4\)，最优常数为 \(3^{1/4}/\sqrt2\)。等号张量可取对称坐标系数 \(t_0=t_4=4,\ t_1=t_3=\sqrt3,\ t_2=0\)，允许正交变换和整体缩放；其距离平方为 24、\(R^2=768\)。
3. 对每个 \(p\ge5\)，系数 \(t_0=t_p=1,\ t_1=t_{p-1}=1/\sqrt p\)，其余为零，给出距离平方 2、\(R=4\sqrt{2(p-1)}/p\)。故上述统一常数至少为 \(\sqrt{2/R}=\Omega(p^{1/4})\)。

这些公式是本轮收到的比较目标；本报告不独立验算其代数或证明。

## 二元全阶常数的匹配量级更新

后续证明补上了维数固定为 2 时的全阶上界。记最优常数为
\[
C_p^{(2)}=\inf\{C:\operatorname{dist}_F(T,\mathrm{ODeCo}_{2,p})\le C\sqrt{R(T)}\ \text{对所有实对称 }T\}.
\]
所给 trace-defect 估计为 \(G_{\rm trace}=2\|T\|_F^2-\|\operatorname{Tr}T\|_F^2\)，且二元对称三阶 trace bound 为 \(\|\operatorname{Tr}T\|_F^2\le\frac43\|T\|_F^2\)。逐个固定余下的 \((p-3)\) 个有序指标后对该三阶界求和，给出所有 \(p\ge3\) 的 \(\|T\|_F^2\le\frac32G_{\rm trace}\)。再与 \(d^2\le\frac p4\lambda_{\min}(G)\) 合并，得到
\[
d^4\le\frac{3p}{4}\det G,
\qquad C_p^{(2)}\le\left(\frac{3p}{4}\right)^{1/4}.
\]
更精细地，在复数 \(e_\pm\) 正交对称基下可计算 \(\|\operatorname{Tr}\|_{op}^2=\sigma_p=4\lfloor p^2/4\rfloor/[p(p-1)]\)。令 \(c_p=(2-\sigma_p)^{-1}\)，则对 \(p\ge9\) 另有
\[
(C_p^{(2)})^2\le\frac{p}{4\sqrt{p/(4c_p)-1}}.
\]
结合上面的系数族下界 \(C_p^{(2)}\ge\sqrt{2/R}=\Omega(p^{1/4})\)（对 \(p\ge5\)），这给出
\[
C_p^{(2)}=\Theta(p^{1/4})\quad(p\to\infty).
\]
此量级匹配关闭了先前报告中“二元全阶常数的上下界阶数未匹配”的缺口；它仍只确定渐近阶，不宣称确定每个 \(p\) 的最优常数。等号张量给出的 \(p=4\) 精确常数仍是前节单独记录的加强。

这段新上界是本轮收到的主证明更新，不是已发表文献的归属判断。其 trace/Hessian 组合是否已经以等价记号出现，需与下列检索边界一起看。

## 查阅来源及定理级比较

**Boralevi–Draisma–Horobeț–Robeva, “Orthogonal and unitary tensor decomposition from an algebraic perspective,” arXiv:1512.08031 (2015), DOI [10.1007/s11856-017-1588-6](https://doi.org/10.1007/s11856-017-1588-6).** 已读主文相关部分：§3.1、Lemma 11、Proposition 12，以及高阶对称情形 §4.2。该文刻画 ODeCo 的精确代数零集，并给实对称三阶张量对应的代数结构解释；其陈述在 \(R=0\) 的精确识别层面与当前残差相邻。所读部分没有二元任意阶的距离—残差不等式、上述二元 quartic 最优常数/等号例，或给出 \(\Omega(p^{1/4})\) 常数下界的这个系数族。该结论仅限所读主文部分，不能推出整个文献不存在等价命题。

**Robeva, “Orthogonal Decomposition of Symmetric Tensors,” arXiv:1409.6685 (2014).** 本轮核对 arXiv 条目与摘要，未逐条读主文。其摘要说明研究对称张量的正交分解及相应代数方程，属于精确可分解性的代数背景；未据摘要判断任何上述定量式是否在全文出现。

**Auddy–Yuan, “Perturbation Bounds for (Nearly) Orthogonally Decomposable Tensors,” arXiv:2007.09024 (2020), DOI [10.1093/imaiai/iaac033](https://doi.org/10.1093/imaiai/iaac033).** 已读主文中一般扰动定理。文中控制已给 ODeCo 分解或近 ODeCo 张量在 spectral-norm 扰动下的分量恢复；其对象是恢复分量/比较给定基准，不是对全部收缩交换子的 Frobenius 残差给出二元距离界。所读定理没有列出以上常数、quartic 等号系数或高阶下界例。

**Mu–Hsu–Goldfarb, “Successive Rank-One Approximations for Nearly Orthogonally Decomposable Symmetric Tensors,” arXiv:1705.10404 (2017), DOI [10.1137/15M1010890](https://doi.org/10.1137/15M1010890).** 已读主文定理 2.2、3.1。其为正权重 SOD 基准加小 spectral-norm 噪声的逐项恢复定理，要求噪声相对分量权重受控；没有给出当前二元全收缩 commutator residual 的显式全局距离式。所读定理未出现本报告三条公式。

**Friedland–Wang, “Spectral norm of a symmetric tensor and its computation,” arXiv:1808.03864v3 (2018), DOI [10.1090/mcom/3525](https://doi.org/10.1090/mcom/3525).** 已读主文，特别是二元情形 Theorems 18–19。它将二元对称张量的单次谱范数计算化为一元多项式求根；这是计算 \(\max_{\|x\|=1}|T(x,\ldots,x)|\)，不是计算对所有正交方向的投影能量最大值，更不是到二元 ODeCo 集的最近距离或其交换子残差。故该定理不等价于二元 quartic 的最优常数/等号结论。

**Mu–Hsu–Goldfarb, “Greedy Approaches to Symmetric Orthogonal Tensor Decomposition,” SIAM Journal on Matrix Analysis and Applications 38(4), 1210–1226 (2017), arXiv:1706.01169, DOI [10.1137/16M1087734](https://doi.org/10.1137/16M1087734).** 本轮已读主文。Theorem 4.1 分析已知正权重 SOD 张量 \(T=\sum_i\lambda_i v_i^{\otimes p}\) 加 spectral-norm 扰动 \(E\) 时的一种迭代恢复方法；假设 \(\varepsilon\le\theta^2\lambda_{\min}/12.5\)，结论控制恢复的权重和向量误差。它不是由全部收缩交换子 residual 到 ODeCo 集的 Frobenius 距离估计，也未陈述 trace-defect 参数 \(G_{\rm trace}\)、本节的 \(p^{1/4}\) 常数阶或二元等号族。它是可比的近 ODeCo 稳定性来源，但问题目标与误差指标不同。

## 定向检索结果与边界

本轮以 OpenAlex 和 Crossref 进行短查询，词组包括 “binary symmetric tensor odeco distance commutator residual”、 “orthogonally decomposable tensor commutator distance”、 “near orthogonally decomposable binary quartic distance” 和 “symmetric tensor trace defect orthogonal decomposition stability”；并核对上述 arXiv 主文/条目。检索显出若干 ODeCo 扰动恢复论文，包括 Mu–Hsu–Goldfarb 的两篇工作，但没有在搜索结果及已读来源中发现与三条二元公式或新给出的 trace-defect 匹配阶上界完全等价的定理。该表述是**未发现**，不是“不存在”：检索不穷尽可能使用不同术语发表的二元实代数几何、最佳逼近或张量分解结果。

当前可作的初筛判断是：精确零集与扰动恢复已有直接相关先例；但在本轮实际核对的主文范围中，三条指定的二元定量式、quartic 精确最优常数、特定 \(p\)-依赖下界族，以及新得到的 \(C_p^{(2)}=\Theta(p^{1/4})\) 匹配阶均未见直接陈述。没有据此作原创性、优先权或奖项级别结论。后续若出现候选文献，应按张量系数归一、收缩指标的排序重数、残差平方和是否覆盖有序对、以及实/复 ODeCo 定义逐项换算后再判等价。
