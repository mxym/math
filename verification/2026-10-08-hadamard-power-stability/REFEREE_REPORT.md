# Hadamard 稳定性冻结系列审核报告

审核日期：2026-10-08 UTC

审核对象：`research_math/hadamard_stability_20261008/`，2026-10-08 04:21 UTC 冻结的 12 个研究文件，以及 manifest 指定的三份外部精确分类输入。本报告单独存放，没有修改冻结原稿，没有 Lean 构建，也没有发布。

## 结论

**建议：数学主体通过本次独立解析复核，需小修后再称为通过审核的版本。**

没有发现使全阶/奇阶稳定性定理、矩形图内核定理、二阶可提升性定理或逐点局部指数分类失效的核心缺口。各项主常数、残差门槛与 Fourier 整数舍入均可由现有证明推出。这里的“通过”只指本报告记录的独立数学与有限算术复核，不等于形式化证明、期刊同行评审或历史优先权认证。

有一项必须修正的摘要错误，出现于两处：分量权重排除应是 `c=1`、`c=2` 或 `c≡3 (mod 4)`，不能写成排除三个余数类 `1,2,3 (mod 4)`。正文证明是正确的；字面上的摘要版本甚至会错误地排除整个图的指标矩阵 `J`，其行权重 `2m≡2 (mod 4)`。

另建议澄清 ordinary isolation 与 zero ordinary defect 的区别，并给出一段显式 MUB 去相位计算作为归属桥梁。这两项不改变已证数学定理。

## 一 冻结完整性和审核方法

1. `SHA256SUMS` 中 12 个文件全部匹配。
2. `freeze_manifest.json` 记录的三份外部输入的字节数和 SHA-256 全部匹配：`paper.md`、`general-patterns.md`、`phase-geometry.md`。
3. 完整读审了八篇数学笔记、索引、checkpoint、脚本和 JSON；完整读审了三份外部分类证明，而不是把它们的结论当作未经检查的公理。
4. 在独立审核目录复制运行原算术证书脚本，输出与冻结 `tangent_rank_results.json` 逐字一致。没有运行会写入原目录的脚本。
5. 新写独立有限检查程序，验证两例图、45 个 quadratic 参数的精确模计数和全部邻接公式，以及 order-four 的二阶分支方程。有限检查仅补充解析证明，不能替代全体参数的证明。
6. 阅读了 McNulty–Weigert 原文 Appendix A、相关 MUB block construction，以及 Banica–Özteke–Pittau 原文 §4。更全面的文献优先权比较，特别是 Craigen–Woodford 全文，仍未完成；本系列没有作这样的优先权断言。

## 二 全阶和奇阶残差到精确解

对应：`odd_hadamard_stability.md`、`all_half_orders_extension.md`。

### 量词和范数

定理要求的是每个条目**精确单位模**，并且同时控制全部 `1≤k<m` 的未经归一化算子范数残差。证明没有把仅控制 `k=1`、仅控制一部分幂或近似单位模错误地当作相同假设。

去相位对每一个 entrywise power 都只产生左右对角酉乘，因而保持相应算子残差。对方阵，`MM*` 与 `M*M` 的谱一致，故行、列 Gram 算子残差相同。后文确实只由这一事实取得每项列相关的上界，没有使用一般情况下错误的“行列最大条目残差相同”。

归一化换算也正确：`epsilon=2m rho`，故门槛为 `rho≤2^-25 m^-4`，误差为 `512 sqrt(2 rho)`。仅有行非对角相关上界 `eta` 时使用 `epsilon≤(2m-1)eta` 是合法的 Hermitian 行和界。

### Newton 到两个多边形

原稿第 70—78 行的 Newton 归纳成立。对于 `ell<m`，已知前面所有 `|e_j|≤epsilon` 后，

`ell |e_ell|≤epsilon[1+(ell-1)epsilon]≤ell epsilon`。

单位模补集恒等式补齐高阶系数，`P(1)=0` 给出中间系数，最终系数 l1 误差不超过 `4(m-1)epsilon`。这里保留实际乘积 `d=prod v_j` 至关重要，后面的支持比较确实使用它。

分离引理中的 `r=64epsilon/t` 满足比文中更强的 `r≤t/(16m)`。圆周上的主项下界为 `24m epsilon`，误差上界小于 `8(m-1)epsilon`，Rouché 可分别给每个圆盘一个根，含重数。跨两个因子的根距至少 `t/m`，同因子的根距至少 `4/m`；圆盘确实不交。因而“每个半边包含每个根一次”具有真正的多重度依据，不是仅从逐项接近两种相位推断出来。

### 公共支持和大相位矩形

两个不同活跃支持若在 `S\U` 有一个位置，实际行商乘积是 `x/y`。该位置的 `m` 次幂距 `x` 至多 `delta/8`，而其距 `1` 和 `x/y` 均至少 `7delta/8`；与乘积误差至多 `delta²/256` 矛盾。这个论证对所有 `m≥2` 成立，没有偷偷使用奇性。

大相位假设 `s>8delta` 后，行列活跃集合确实分别恰有 `m` 个元素，并给出同一 `m×m` 矩形。跨组商的分离量分别至少 `s-9delta/8` 或 `s-5delta/4`，均大于 `s/2`。顶半边的幂相位靠近 1，不能归到另一多边形，因此受限半和估计包含了正确的 bijective matching。

唯一应补的微小行文说明是：初始全一行和全一列的结论直接成立；标量矩估计对其余行/列通过与初始行/列比较使用。初始行本身不满足“非平凡幂和小”的标量引理假设，但证明无需对它应用该引理。

### 奇性只在 trace 障碍使用

`P=AA*/(2m)` 是正半定，且 `tr P=m/2` 精确成立。恒等式

`P²-P=[AA*E-A(A*B)B*]/(2m)²`

无缺项。非负特征值到 `{0,1}` 的距离不超过 `2|lambda(lambda-1)|`，故奇数 `m` 强制 `||P²-P||op≥1/(4m)`。在所列小残差条件下得到 `s≤768m²epsilon`，再由 `epsilon≤1/(9m³)` 与大相位假设矛盾。最终 `||K^(o m)-J||max≤258 sqrt(m epsilon)` 和根误差 `q≤129pi sqrt(epsilon/m)<512 sqrt(epsilon/m)` 正确。

### Fourier 整数舍入

门槛 `epsilon≤2^-24 m^-3` 给出 `q≤1/(8m²)`。任一非初始频率的根矩阵行商和满足

`|sum_j (G_aj conj G_bj)^k|≤epsilon+4mkq<1`。

以全部 `m-1` 个非零频率 Fourier 反演，`N_r-2` 是绝对值严格小于 1 的整数，所以它为 0。这里不需要 `m` 为素数，也没有把一般复数残差直接“取整”为零。最近根唯一性亦由远小于根间距的误差保证。

全阶大相位分支中，先剥离矩形相位，舍入误差 `q≤17pi sqrt(epsilon/m)<64 sqrt(epsilon/m)`。同组行商的每根计数为二，跨组的每一半有零频率 `m`，其余频率上界小于 `129/4096<1`，分别给出每根计数为一。这不但构造了 root seed，也真的证明了兼容性，故产生实际精确 circle point。没有停留在必要模式或空集合距离上。

`epsilon=0` 的处理由完整核过的外部分类支持；也可以单列零误差版本。非存在残差下界是上述实际构造的严格逆否命题，其量词正确。

### 非根线性界和 order-four sharpness

重新匹配后的 `h0=64m epsilon/s` 给出完整模式误差不超过 `5h0`。于是距离至多 `160pi epsilon/s<512epsilon/s`。活跃支持在重新匹配时不能切换，因为两相位间距和粗误差已分离；top-left 的行商仍在 1-polygon。原种子及矩形证书可以沿用。

order-four 曲线的 Gram 谱计算正确：置换后矩阵为 `A+(e^(it)-1)I`，`A` 谱为 `2,2,2,-2`，故残差恰为 `6(1-cos t)`。去相位得到原文写出的正 `t`、`2t` 相位，没有符号错误。入射 circle 只能改变一个 2×2 矩形；非入射 circle 距根至少 `sqrt(2)`，因此原文给出的 `2t/pi` 距离下界成立。它只证明包含偶 half-order 的类需要指数 1/2，不能用作奇数 half-order 的 sharpness 证据；稿件已守住这一区分。

## 三 整数内核与矩形图

对应：`local_exponent_criterion.md`、`rectangle_graph_criterion.md`。

整数矩阵 `L_G` 把各二元素 residue class 的差分和与第零类比较。全体非平凡 Fourier 系数为零当且仅当这些差分和相等，所以其内核恰为 simultaneous all-power dephased tangent kernel。对复合 `m` 同样成立；第一篇局部笔记只需要奇 `m`，图笔记正确地放宽了这一点。

双中心化后，每个 class 的行差分和为零；列 Gram 微分也为零。在一个相等根比矩形上，行、列方程相加相减分别使两条对角线的值相等。反向也成立。因此内核恰为图分量上的常值矩阵。每个分量每行、每列的单元数都是同一个 `c_C`，双中心化只加一条独立关系 `sum c_C u_C=0`，维数就是 `r-1`。这里没有把有限解集的离散性当作微分内核为零。

Taylor/Fourier 的边差常数为

`(H_(m-1)/m)epsilon+n(m-1)y²`。

沿图直径 `D` 累加，在 `y≤1/[2Dn(m-1)]` 内吸收二次项，去相位的四倍损失得到 `8D H_(m-1)epsilon/m`。最短路每隔三点的闭邻域不交，给出 `D≤3n-1<6m`；单个分量相同论证给出 `D_C≤3c_C-1`。

由全局误差进入局部半径的门槛

`epsilon≤1/[2^28 D² m(m-1)²]`

正确，`2^-34 m^-5` 是充分的更保守门槛。结论 `48H_(m-1)epsilon` 保留“舍入所得 seed 的图连通”这一条件，没有证明所有奇数图连通。

逆子式估计 `C≤D 8^((D-1)/2)`、半径 `1/[8Cm(m-1)]`、局部线性常数 `4CH_(m-1)/m` 和入口门槛 `2^-26/[C²m(m-1)²]` 均正确。

精确重算结果：

- `m=3`：形状 30×25，秩 25，选定子式行列式 34992，逆 infinity 范数 18，图一个分量，直径 3。
- `m=5`：形状 180×81，秩 81，选定子式行列式 19531250，逆 infinity 范数 503/5，图一个分量，直径 4。

对应半径 `1/864`、`1/16096`，常数 `36`、`503/3`；图常数分别 `12`、`40/3`，算术无误。

## 四 分量权重障碍

对应：`component_obstructions.md`。

任意图分量并集的不同支撑行交集由 equal-ratio pairing 两两配对，因此交集为偶数。其二进制关系 `WW^T=(c mod 2)I` 成立。

设 `A=G∘W`。配对给 `AG*=GA*`，于是 `P=AG*/sqrt(n)` 为 Hermitian，并有 `P²=AA*`、`tr P=c sqrt(n)`。当 `c=1` 时谱在 `{±1}`；当 `c=2` 时支撑化为 2×2 全一块，其对应 G 块秩一，故 P 的谱在 `{0,±2}`。这两种情形均强制 `sqrt(n)` 为整数，与奇数 `m` 的 `n≡2 mod4` 矛盾。

当 `c` 奇数时，W 在 F2 可逆，偶数双交集使 XOR 权重同余 `wt(xW)≡c wt(x) mod4`。求和得到 `(1+i)^n=(1+i^c)^n`，若 `c≡3 mod4` 则强制 `4|n`，矛盾。因此正确排除集是

`{1,2} union {c:c≡3 mod4}`。

这足以推出每个分量权重至少四、`m=3` 必连通；`4+6`、`5+5` 在 `m=5` 仍未排除。正文最后的分量余数分类也正确。摘要误写应按后面的 R1 立即修补。

## 五 Quadratic MUB 无穷族

对应：`quadratic_family_linear_stability.md`。

四块指数公式独立代数复核通过。cross-row 左、右块分别为

`C-(u-(2x+y))²/4` 和 `C-(v-(2qx+y))²/(4q)`，

其中 `C=(2x+y)²/4`。`chi(q)=-1` 使两个非中心二次值集合不相交，而中心值各出现一次，每个 residue 的总计数确为二。

同组图为 `K_(p,p)` 去掉 perfect matching；`r≠0`、`q≠0` 使每侧都有 p 个不同顶点，且 `p≥3` 时连通、直径至多三。

四条跨组邻接标签公式全部代数正确。中心值虽跨列块配对，标签仍与一般反射公式一致。两类正向斜率之差是 `r≠0`，反向斜率之差是 `2r≠0`；因此每种方向至少有一类列可以访问全部对方分量。另一列型先走一步即可。`2+3+2=7` 的直径界和 opposite-group 的五步界成立。

将 `D≤7` 放入图入口条件，`49<64` 给出 `epsilon≤2^-34 p^-3` 足够，线性常数为 `56H_(p-1)/p`。这里仅对本明确给出的参数族或其相位/置换等价 seed，不能推广为任意 cyclic GH。

独立模整数检查覆盖 `p=3,5,7,11,13,17,19,23` 的全部 45 个 admissible r，验证了 GH 计数、连通性、同组标签和全部四种跨组邻接标签；其中 `p≤7` 还遍历所有源点求精确图直径。一般证明不依赖这些例子。

### 构造归属的显式核对

可用以下短计算强化原稿第 30 行，避免只笼统写“来自经典 MUB”。设 `F_xu=p^-1/2 zeta^(xu)`，`D_a=diag(zeta^(a x²))`，`U_a=D_a F`。标准块构造取

`(1/sqrt(2)) [[F,U_r],[U_1*F,-U_1*U_r]]`。

去掉归一化后，底部左块由二次 Gauss 和给出常数 `gamma(-1)` 乘 `zeta^((u-y)²/4)`，右块为 `-gamma(-q)` 乘 `zeta^((v-y)²/(4q))`。各底行除以其首项后，右块剩余常数是 `-gamma(-q)/gamma(-1)=-chi(q)=1`，恰得原稿四块指数。这直接说明是哪一个 MUB 构造及何种去相位，并未证明该族所有参数都与 Butson 原始构造相等价，也无需该等价。

McNulty–Weigert 的 Appendix A 式 (38) 与脚本 E5 逐项一致，并明记零 ordinary defect。该原文把其 Butson construction 与一般 MUB construction 作了区分；当前稿不应加强为未经证明的全族等价。参考：[McNulty–Weigert 原文](https://arxiv.org/pdf/1208.1057)。

Banica–Özteke–Pittau §4 讨论 MUB/Gauss-sum 构造，Conjecture 4.5 是指定参数选择下的 ordinary isolation 猜想。当前 simultaneous-kernel 结论不能解决它。尤其不能对任意实 tangent 系数施加 cyclotomic Galois 自同构并假定它们固定。原稿已经明确拒绝这个不合法步骤。参考：[Banica–Özteke–Pittau 原文第 4 节](https://arxiv.org/html/1706.00986v2)。

## 六 二阶可提升性和精确 tangent cone

对应：`second_order_tangent_cone_20261008.md`。

设二阶相位系数为 Y，故通常意义的相位二阶导数为 2Y。每对行的二阶条件是 `ik S_k-(k²/2)Q_k=0`。由于相位系数实且 seed 为 m 次根，`S_(m-k)=conj S_k`、`Q_(m-k)=conj Q_k`。相比较强制 `Q_k=0`、`S_k=0`。当 `m` 偶且 `k=m/2`，两者本身为实数，同一个方程的实、虚部分分别为零，完全覆盖 `m=2`。

减掉线性行列 gauge 保持 admissibility。双中心化以后每个二元素 class 的一阶差是 `u,-u`，平方和相等使每对行的逐坐标距离一致；列条件同理。实直线上的带标签等距配置只能相差反射和平移，中心化排除平移，继而行列条件给出平衡 rank-one sign 形式 `a r s^T`。非零 dephased 代表正是一块 `m×m` 矩形的常数指标方向。

该矩形方向的一阶跨组方程通过 Fourier 反演等价于兼容性，因此充分性由实际 exact circle 给出；任何 `Y∈V_G` 不改变二阶系数。原稿对 admissible two-jet 与“能否用该指定 Y 延拓成 exact curve”作了正确区分。

分量 sign assignment 与 balanced rank-one 判别双向成立。正分量集合包含初始分量且总权重 m，是正权重 antichain，Sperner 上界成立。order-four 独立计算得到四个图分量、三个兼容矩形；以三个矩形切向为坐标，二阶消失理想为 `(ab,ac,bc)`，正好是三条直线。

奇 `m` 的排除也可不调用全局分类：同 row sign 的两行在正支撑上的交集大小 m 为奇数，与分量并集偶交性质矛盾。它仅排除非零二阶可提升方向，不推出一阶内核为零。

## 七 每个精确点的最优局部指数

对应：`local_exponents_all_orders_20261008.md`。

审核所用精确定义是：固定精确 dephased 点 K0，存在其邻域及有限常数 C，使邻域中每个单位模 dephased K 满足 `dist(K,X_m)≤C epsilon(K)^alpha`；“最好指数”指所有这种 alpha 的上确界。原文结论按此通常定义成立。

- `r=1`：图微分 coercivity 给指数一。`x≤1/(128m³)` 足以满足吸收半径，常数 `48h` 正确。
- `r=2,b=1`：两个分量都是 row weight m，直径各小于 3m。分量均值投影与 dephasing 给 `X=beta 1_Q+Z`，且 `|beta|≤16x`、`||Z||≤17x`。在各分量均值为零的横截面上，线性常数 `C0=4Dh/m<12h`。`B≤8m^4` 后，`C0 B·33x<3168/8192<1/2`，所以 `x≤1/(8192hm^4)` 下误差至多 `24h epsilon`。所有范数及 gauge 四倍损失都有计入。
- `r=2,b=0` 或 `r≥3`：可选不在任何 incident-circle 切线中的内核方向，其残差 O(t²)、距有限 exact-circle 并集为 Omega(|t|)。全局平方根上界给出最优指数正好 1/2。非入射紧圈与根的正距离是由有限性得到，量词是对固定 seed 的局部结论。
- nonroot：固定相位分离 `|alpha^m-1|>0`，连续性和已证 `512epsilon/s` 给指数一。环境相位空间中取横截方向，距离为 Omega(|t|)、残差 O(|t|)，排除指数大于一。

“二分量至多一个兼容矩形”确实由 sign assignment 给出；没有漏掉 `r=2,b>1` 的情形。所有 even-root 局部半径结果都没有被误写为全局残差可自动选择指定 root neighborhood。

## 八 外部精确分类输入的使用范围

三份冻结外部输入的解析链条完整：Newton 两多边形、实际 row-product 排除不同支持、单矩形模式、奇半阶 trace 障碍、Fourier 完整 GH 计数，以及兼容矩形的构造与穷尽性。有限根数和有限矩形数随后确实给出有限 compact-circle 并集；不同 circle 只能在 root 处交会，每个 nonroot 点仅在一个 circle 上。

当前系列只在零残差端点、奇数精确集离散性、兼容 circle 的 exactness/exhaustiveness 及局部几何处调用这些输入。没有把外部来源当作所有 odd graphs connected、普通 first-power tangent kernel 零、新 seed 存在或 ordinary isolation 猜想的证明。归属同时保留 `mio-qwq/math` 指定 commit 和它声明的 OpenAI order-six antecedent，符合依赖关系。

## 九 可直接执行的修补定位

### R1 必须修订的摘要措辞

位置：`INDEX_FROZEN.md:28` 和 `CHECKPOINT.md:11`。

将“row weight 1, 2, or 3 modulo 4”或“row weight 1, 2, or 3 mod4”替换为：

> row weight c=1 or c=2, or row weight c congruent to 3 modulo 4.

等价简洁写法：

> row weight in {1,2} or congruent to 3 modulo 4.

理由：现有证明不排除 5、6、9、10 等一般权重。whole graph 的 row weight 2m 已经是原字面版的反例。正文 `component_obstructions.md` 无需因此改变。

### R2 建议澄清 ordinary isolation 和 ordinary defect

位置：`quadratic_family_linear_stability.md:114`，涉及“ordinary first-power defect/isolation question is stronger”的句子。

建议替换相关句子为：

> Conjecture 4.5 concerns isolation for the ordinary first-power Hadamard equations. The simultaneous all-power tangent theorem proved here does not establish that conjecture. Zero ordinary first-power defect would imply zero simultaneous defect, but ordinary isolation and zero ordinary defect are distinct statements.

这只是把正确的范围警告写得逻辑精确，不应把“isolated”自动当成“Jacobian injective”。

### R3 建议补充而非修错

- `quadratic_family_linear_stability.md:30` 后可加入本报告第五节的显式 block/Gauss-sum 去相位计算，明确经典构造到当前指数公式的桥梁。
- `odd_hadamard_stability.md:132-134` 后加一句：初始行列的界平凡成立，标量引理用于其余行列。避免读者对全一行套用不满足的矩条件。
- `all_half_orders_extension.md:12` 可就地定义“compatible”：跨 R 与 R 补集的行商，在 S 上每个 m 次根恰一次。现有外部引用已足够支撑证明，此举提升独立可读性。
- `local_exponents_all_orders_20261008.md:11` 可加入本报告第七节的局部指数定义，使 seed-dependent neighborhood/constant 的量词完全显式。

以上修订应放入一个新的 revision，不应静默覆盖当前 frozen hash。

## 十 审核后的断言边界

可保留：明确给出的 polynomial threshold、实际 root/circle 舍入证书、图内核等式、二阶可提升性分类、逐点最佳指数和所列 classical quadratic family 的统一图连通性。

不得加强：一般奇 m 图连通、某个新的 odd disconnected seed 的存在、任意新阶 seed 存在、ordinary first-power 零 defect/isolatedness 猜想已解决、或历史优先权。

本轮最有价值的可用成果是全阶可构造稳定性与图/二阶机制形成了互相独立而兼容的证据链；有限脚本只是对经典例子的附加证书，不承担无穷阶证明。
