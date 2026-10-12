# 实际有限金字塔几何：独立源级语义审查

审查日期：2026-10-07。审查对象为冻结快照 `source/entry005-actual-pyramid-20261007/formal`。本文所有源引用相对于该目录。

## 结论与核验边界

**在下列实际声明的条件下，未发现所审七个 Pyramid 模块把体积、侧面积、Cauchy 或 extrusion 公式作为未证明前提冒充结论的语义缺口。** 它们把 literal pyramid convex hull 与实际 finite-halfspace set、内禀 Haar 面积、实际 symmetric-segment zonotope 连接起来。最关键的常数与维数均相符：

- 金字塔高度固定为 1，体积为 `V/(d+1)`。
- 底面面积为 `V`，第 i 个侧截面面积为 `Ai*sqrt(1+h_i²)/d`。
- 投影体生成元为 `g_none=(V/2)*(0,-1)`、`g_some_i=Ai/(2d)*(n_i,h_i)`。
- 在实际投影体体积中，底面生成元带来的 extrusion 项为 `V*d^(-d)*vol(ΠK)`。

这是**静态语义审查**，不是一次新的 Lean 编译或内核审计。审查中未修改冻结源，未下载 cache，未运行编译。没有把随包日志视作本次独立核验。以下判断依据定义、声明的真实参数、证明正文以及所列 owner 源；完整 axiom closure、构建环境与日志可信度应由独立构建审计负责。

## 1. 对象身份与计量语义

设 `d=Module.finrank ℝ E`，`K=finiteHalfspaceSet n h`。

1. `Targets.lean:26–40`：
   - `projectionVolumeSet K u` 是真实正交投影到 `(ℝ ∙ u)ᗮ` 后的 `volume.toReal`。
   - `projectionBodySet K` 是所有单位方向的真实投影体积半空间之交。
   - `pyramidSet K` 是 `K×{0}` 与 apex `(0,1)` 的真实 `convexHull`，不是定义成一个体积数值或公式满足者。
2. `FiniteHalfspaceFacets.lean:14–18,152–178`：底集是 `∀i, inner (n i) x ≤ h i`；标记为 facet 的集合是该底集与等式超平面的交。这个定义**不要求**它非空或恰为余维一 face。单位法向条件下，chart 到该集合的仿射等距坐标确实被证明。
3. `FiniteHalfspaceCauchy.lean:53–54`：`finiteHalfspaceFacetArea` 是 chart 上实际 canonical Haar `volume` 的 `toReal`。它不是额外赋予每个 index 的自由权重。
4. `ConeLawGeometry.lean:20–25`：`finiteZonotope g` 是系数属于 `[-1,1]` 的实际向量和集合。因此每个 generator 对应的线段长度是 `2*‖g i‖`；这与以下两个 `1/2` 因子完全一致。
5. 涉及实际有限维体积的主结果拥有 `[FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]`。所用体积是 canonical Euclidean/Haar volume，不是一个可由调用者任意给定的 measure 字段。

`toReal` 的一般定义会把 `∞` 送到 0，但这里主桥的底集、金字塔、facet chart、zonotope 和相关投影均由 compactness 证明有限。故主结论不是利用 `∞.toReal=0` 得到的虚假“体积”恒等式。单独的 `pyramid_base_facet_area` 不假设 compactness，故脱离主桥时它只是一条 `toReal` 等式，并不自行保证面积有限。

## 2. 主定理的条件，不能省略

通常隐含的基础条件是实内积赋范加法群；下表只突出额外条件。

| 声明 | 实際額外條件 | 结论范围 |
|---|---|---|
| `pyramidSet_volume` (`PyramidVolume:136`) | E 有限维且 Borel；K compact、convex | 任意实际 K 的单位高度 pyramid 体积 `vol(K)/(d+1)`；允许空 K 与零体积 K；无需 `Nontrivial E` |
| `pyramidSet_finite_halfspace` (`PyramidHalfspaces:174`) | `Nontrivial E`；全部 `h_i>0`；K compact | 与提升半空间集合的实际集合等式；**不需** normals 单位、注入；声明省略了 Fintype |
| `pyramid_base_facet_area` (`PyramidFacetAreas:69`) | E 有限维且 Borel | 提升半空间集合的底面 chart 面积 = `vol(K).toReal`；无需 compact、正高度或 normals 单位/注入 |
| `pyramid_side_facet_chart` (`PyramidSideArea:43`) | `Nontrivial E`；指定 `‖n_i‖=1`；全部 `h_j>0`；K compact | 指定提升侧 chart = 原 chart 的径向锥经真实等距映射和平移后的像，再并上 apex chart |
| `pyramid_side_facet_area` (`PyramidSideArea:143`) | 上一行条件；E 有限维且 Borel | `Ai*sqrt(1+h_i²)/d`；无需 normals 注入，也无需原 facet 非空 |
| `pyramid_projection_body_eq_zonotope` (`PyramidProjectionBody:34`) | ι 有限；E 有限维、Borel、非平凡；全部 normals 单位且 `Function.Injective n`；全部 `h_i>0`；K compact | 实际 pyramid 投影体 = 所列实际 zonotope |
| `pyramid_side_horizontal_image/volume` (`PyramidProjectionVolume:23,53`) | ι 有限；E 有限维、Borel；全部 normals 单位且注入；K compact | side zonotope 的水平投影 = `(1/d)ΠK` 的等距像及其体积；无正高度条件，无 `Nontrivial E` |
| `pyramid_projection_body_volume_decomposition` (`PyramidProjectionVolume:67`) | 与主投影体集合等式相同 | side zonotope 体积加底面 extrusion 项 |

**范围解释：** `h_i` 是底集相对单位法向的支撑数；它不是金字塔的高度。主几何桥处理的是原点严格位于全部有限半空间内部、且整体 compact 的底集。单位法向与有限性给出原点附近的正半径球，因此主桥底集有内部且 `V>0`（`FacetRadialMass.lean:268–288`）。这不是一个涵盖所有退化有限半空间底集的主投影体公式声明。

## 3. 体积 `V/(d+1)` 是怎样证明的

证明链：

`RadialConeVolume.radialCone` → literal horizontal slices → Haar scalar-image law → product Fubini → `radial_power_integral` → volume-preserving `WithLp` conversion → 反射/平移 → `pyramidSet_volume`。

- `RadialConeVolume.lean:21,38–62` 定义并证明径向锥的真实水平截面为 `(s/H) • F`（`0≤s≤H`），区间外截面为空。
- `RadialConeVolume.lean:93–121` 对 compact F、`H>0` 使用可测截面与 Fubini，得实际体积 `H*vol(F)/(dim(F-ambient)+1)`；不需要 F convex。
- `RadialPowerIntegral.lean:16–24` 从实际幂函数积分推出 `∫₀ᴴ(s/H)^k ds = H/(k+1)`，不是将该标量公式作为输入参数。
- `PyramidVolume.lean:54–104` 从真实 convex hull 证明 pyramid = 翻转径向锥并上 apex。专门保留 apex 分支以处理空 K；没有错误地把空底 pyramid 识别为空集。
- `PyramidVolume.lean:123–149` 使用实际等距与平移的 Haar 体积不变性，再消去零测 apex。提升空间含一个 ℝ 因子，因而即使 E 零维，apex 的环境体积仍为 0。
- 原点属于 K、K full dimensional、facet 公式等均不是此体积定理的前提。

此处 convexity 不可忽略：若 K 非凸，真实 pyramid 用的是 `convexHull K`，一般不能以原 K 的 volume 代入。

## 4. 半空间等式与隐藏的顶高约束

`PyramidHalfspaces.lean:19–30,63–86` 的提升不等式恰好为：

`t≥0` 且 `inner(n_i,x)+h_i*t≤h_i`。

没有把 `t≤1` 直接塞进定义。它在 `:174–227` 中从 compactness、严格正 `h_i` 与非平凡 E 推出：

1. compact 且包含原点的底集不可能存在非零 homogeneous recession direction（`:100–119`）。
2. 非平凡 E 加 compactness 保证 index 非空（`:162–168`）。
3. 若 `t>1`，所有 `inner(n_i,x)` 都非正，故 x=0；再用至少一个严格正 `h_i` 矛盾。
4. `t=1` 时同一 recession 论证给 x=0，即只有 apex。
5. `t<1` 时使用 `(1-t)⁻¹ • x` 恢复真实底点。

以下纸面反例说明限制是实质性的，而不是多余装饰；这些是本次语义检查中的数学例子，并非另行执行的 Lean tests：

- 若去掉非平凡条件，取 E 零维、ι 为空，底集是 compact singleton。提升不等式仅剩 `t≥0`，而真实 pyramid 是 `[0,1]`。
- 若把所有 `h_i>0` 放宽成 `h_i≥0`，取 E=ℝ、normals ±1、heights 0，底集为 `{0}`；提升集合仍是竖直半射线，真实 pyramid 是闭线段。
- 若去掉 compactness，取 E=ℝ、单个不等式 `x≤1`，提升集合 `x+t≤1,t≥0` 允许 t>1，而真实 convex hull 的高度不超过 1。

## 5. 底面、侧面与空 facet

### 底面

`PyramidFacetAreas.lean:10–41` 直接构造 `E ≃ₗᵢ (span(0,-1))ᗮ`；`:47–76` 在高度 0 处证明 chart 恰好是 K 的像，再使用实际 isometry 的 measure preservation。没有假设底面积=V。

### 侧面

`PyramidSideFrame.lean:9–99` 构造并验证线性等距满射：

`(q,w) ↦ (q + (w/s)*h*n, -w/s)`，其中 `q⊥n`、`s=sqrt(1+h²)`。

它不是未经证明的“Jacobian=1”接口：正文分别证明落在目标正交超平面、线性、范数不变、满射，并组装为 `LinearIsometryEquiv`。

`PyramidSideArea.lean:25–37` 验证真实坐标恒等式：

`apex + J(r*q,r*s) = (r*(h*n+q),1-r)`。

`:43–115` 由 pyramid 真实 membership 和侧超平面等式，证明侧 chart 是原 facet chart 的径向锥之等距平移像，另加 apex chart。`:143–177` 对此实际集合运用径向锥体积：原 chart 环境维数为 d−1，径向锥高度为 s，因此分母为 `(d−1)+1=d`。维数等式由 `n_i≠0` 和 `finrank_add_finrank_orthogonal` 在证明中得出。

### 冗余与零面积

- 原等式截面为空时，提升侧截面**不是空集**，而是 `{pyramidApex}`；这由 `pyramid_side_facet_of_empty` (`PyramidSideArea.lean:119–136`) 明确证明。
- apex 在 d 维侧 chart 中零测，d≥1 由非平凡有限维 E 保证。`pyramid_side_facet_area_of_empty` (`PyramidProjectionBody.lean:63–68`) 正确给零。
- 原等式截面也可以非空但低于 d−1 维。例如二维 square 的一个额外支撑不等式只碰到一个顶点。这里的 `Facet` 名字不意味着实际 codimension-one；面积公式不要求非空性或 facet 满维，因而没有强行给这些退化截面正面积。
- normals 不重复时，冗余不等式可保留，包括空截面与低维截面。**主投影体结果不接受同一 normal 被重复索引**，即使重复中有些更弱约束理论上可删除；没有在本模块内部证明通用 duplicate-normal 去重步骤。
- 此注入限制不能整体删除：在 ℝ 的 `[-1,1]` 描述中将 `+1` normal 同高度重复一次，三个 0 维 facet chart 的面积都为 1。Cauchy 右端变为 3/2，而实际单位方向投影的 0 维体积为 1。

## 6. 实际 Cauchy owner，未偷渡面积公式

`FiniteHalfspaceCauchy.lean:156–164` 的输入仅为 normals 单位、注入、底集 compact、u 单位（及基础有限维/Borel/有限 index）。**没有** Cauchy、surface measure、normal balance 或 facet coverage 结论作为前提。

已检查的 owner 证明：

1. `FiniteHalfspaceFacets.lean:40–109,120–148`：有限性给出统一小位移；compact projection fiber 上取实际极值，产出朝上/朝下 active facet，证明实际投影覆盖。
2. `FiniteHalfspaceFacets.lean:199–237`：同向 facet 在共同 fiber 的实际端点相同。
3. `FiniteHalfspaceFacets.lean:267–375`：单位且不同的同向 normals 给目标投影超平面内的非零线性泛函，重叠包含在其零测 level set 内。因此实际 facet 投影几乎不交；冗余或空截面无需另加假设。
4. `HyperplaneProjectionJacobian.lean:98–118,150–220`：正交超平面投影的真实 determinant 绝对值为 `|inner u n|`，结合 canonical Haar 的 linear-image theorem 得投影体积。singular case 包含在真实线性像体积定理中；未把非零 determinant 假设加进每个 facet。
5. `FiniteHalfspaceCauchy.lean:76–154`：上下各自的有限 union 体积相加，再取平均得 1/2 Cauchy 公式。
6. `ConeLawGeometry.lean:77–119` 的通用 reduction 确实以 brightness identity 为参数，但 `FiniteHalfspaceCauchy.lean:209–223` 已用刚证明的实际 Cauchy 恒等式提供此参数。因此不能因通用 reduction 是条件式就误判主桥仍假设 Cauchy；也不能仅引用该 reduction 就宣称已证明 Cauchy。

## 7. Zonotope 与 extrusion 的实际闭合

### 生成元

`PyramidProjectionBody.lean:17–44` 把实际提升 facet 面积乘单位 normal 再除 2：

- 底面：`V/2*(0,-1)`。
- 侧面：`(Ai*s/d)/2 * ((n_i,h_i)/s) = Ai/(2d)*(n_i,h_i)`。

这里 `s>0` 被证明，约分合法。注入底 normals 可推得提升 normals 注入；base normal 与任意侧 normal 也不相同（`PyramidHalfspaces.lean:129–156`）。随后主集合等式真正调用 finite-halfspace Cauchy owner，而非从投影体名称直接断言。

### extrusion

`PyramidZonotopeAlgebra.lean:9–43` 把 Option-index segment sum 精确分成 side zonotope 与一个 symmetric segment sum，然后调用 `ZonotopeVolume.compact_convex_extrusion_volume`。

该 owner 的已检查证明链（`ZonotopeVolume.lean:26–125,139–280`）是：

- compact convex set 的每个非空竖直 fiber 是真实闭区间 `[a,b]`。
- extrusion 把该 fiber 变成 `[a,b+τ]`；空 fiber 仍为空。
- 对真实 fiber 长度做 Fubini，不需要全局端点函数可测性的额外假设。
- orthogonal coordinates 的 canonical volume preservation 被证明。
- 任意 v 通过 normalize/rescale 转成单位方向；v=0 单独处理。

因此 owner 包括低维 compact convex set 与零 generator，未要求 side zonotope 满维，也没有先假设 extrusion-volume identity。

### 最终系数与有限性

`PyramidProjectionVolume.lean:23–62` 证明 side zonotope 的水平投影为底投影体的 `(1/d)` 缩放，再由 Haar 缩放得到因子 `(1/d)^d`。`:67–101` 中：

- V>0 从实际底集内部非空和 compactness 得到。
- `‖g_none‖=V/2`，故 symmetric extrusion 的实际长度 `2*‖g_none‖=V`。
- side zonotope 与投影 compact，明确提供 `measure_ne_top` 后才能将 ENNReal 加法转成实数加法。
- 最终确实为 `vol(Π(pyramid K)) = vol(Z_side) + V*(1/d)^d*vol(ΠK)`。

没有漏 2，没有把 `(d+1)` 错用为 side chart 的维数，也没有把 side zonotope 的体积定义成所需余项。

## 8. 退化情况与可安全陈述的范围

- **空 K：**通用 `pyramidSet_volume` 正确保留 apex，且所得环境体积为 0；主有限-halfspace projection bridge 因 `h_i>0` 不会出现空 K。
- **底 K 零体积/低维：**通用 compact convex volume formula 允许；主正高度 finite-halfspace bridge 排除这类底集。
- **d=0：**通用 pyramid volume 允许；主集合表示、side-area 与最终 projection-body decomposition 要求非平凡 E，故不可宣称覆盖 d=0。部分 horizontal auxiliary statements 的确省略了 Nontrivial，但不能借它们消除主定理的限制。
- **d=1：**主桥可用；原 facet chart 维数为 0，非空 singleton 的 canonical 0 维 volume 为 1；提升侧 chart 维数为 1，apex 的 volume 为 0。这两者不可混淆。侧面公式成为真实线段长 `sqrt(1+h_i²)`。
- **h_i=0 或负数：**若只看 normal/frame 的代数式可以定义，但主几何识别和 decomposition 的声明不接受它们。不能由局部 algebra 的更宽定义推出全局几何更宽。
- **facet redundancy：**允许 unique-normal 冗余，包含空与低维 supporting sections；不等于允许重复 normal 全部保留。
- **高度 H≠1：**本次所审 `pyramidSet` 始终 apex=(0,1)。通用 radial-cone owner 支持 H>0，不代表名为 pyramid 的最终声明已推广到任意 H。
- **总体 sharp/stability endpoint：**本审查确认的是指定 finite geometry 层，不能单独作为最终 sharp target、任意 convex-body approximation 或所有下游 endpoint 已完成的证据。

## 9. 静态检查记录

完整读取了七个指定模块，并追读 `PyramidZonotopeAlgebra`、`PyramidLiftCoordinates`、`RadialConeVolume`、`RadialPowerIntegral`、`FiniteHalfspaceFacets`、`FiniteHalfspaceCauchy`、`HyperplaneProjectionJacobian`、`ZonotopeVolume`、`ConeLawGeometry`、`IntrinsicLinearImageReuse` 的相关定义/正文；检查了 `Targets`、`FacetRadialMass` 与 `ZonotopeDeterminant` 的相关 owner 段落。

对七个模块及上述主要直接 owner 的源级文本扫描未发现 `sorry`、`admit`、`axiom`、`implemented_by`、`opaque`、`unsafe`。此扫描只作为静态辅助证据，不等价于内核 axiom closure 检查或重新编译通过。

**建议汇总措辞：**“单位高度实际有限金字塔的体积、实际底/侧面积、投影体 zonotope 等式与 extrusion 分解，在明确的单位/注入 normals、严格正支撑数、compact 与非平凡有限维条件下，源级语义检查闭合；新编译/内核验收状态需另列。”
