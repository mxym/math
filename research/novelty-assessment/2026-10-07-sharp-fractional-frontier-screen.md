# 有限分数覆盖前沿：文献初筛

**日期：2026-10-07。** 本文只记录来源比较与有限检索范围，不审查仓库中的证明，也不作原创性或优先权结论。

## 比较对象与结论

待比较的候选上界是：对有限简单相交 `r`-均匀超图 `H`，边数为 `m`，分数顶点覆盖数（等于分数匹配数）满足对每个整数 `k≥2`

\[
\tau^*(H)\le \max\left\{\frac{(k-1)r+1}{k},\frac{m}{k+1}\right\}.
\]

由此候选的渐近曲线为 `c=m/r≤1` 时 `ψ(c)=c/2`；在整数区间 `[a,a+1]` 上为
\[
\psi(c)=\max\left\{\frac{a}{a+1},\frac{c}{a+2}\right\}.
\]

本轮以公式片段和相交超图分数匹配、覆盖、设计等关键词检索了 Crossref 与 DuckDuckGo，并核读下列三篇论文全文。当前检索未找到相同的有限 max 公式或该渐近曲线。以下来源有相近的分数匹配、项目几何设计或点数约束，但陈述参数和结论不同。未命中仅限本次检索，不能推出不存在先例。

## 核读文献

1. **Zoltán Füredi, “Covering pairs by \(q^2+q+1\) sets,” Journal of Combinatorial Theory, Series A 54(2) (1990), 248–271, DOI [10.1016/0097-3165(90)90034-T](https://doi.org/10.1016/0097-3165(90)90034-T).** 已读全文，副本：`/tmp/furedi_084_covering_pairs_JCTA_1990.txt`。§2 的 Theorem 2.1–2.2 给出依赖边大小/秩的相交超图分数覆盖与有限几何分类；Theorem 2.5 额外固定底层顶点数为 \(q^2+q+1\)。§3 的 Theorem 3.1 研究用给定数目的 \(k\)-集覆盖点对，其对偶形式转为给定顶点数、最大度约束下相交多重超图的边数问题。这里的参数组织围绕秩、底层顶点数或点对覆盖；未见待比较的 \(m/r\) 分数覆盖 max 公式。

2. **Z. Füredi, J. Kahn and P. D. Seymour, “On the fractional matching polytope of a hypergraph,” Combinatorica 13(2) (1993), 167–180, DOI [10.1007/BF01303202](https://doi.org/10.1007/BF01303202).** 已读全文，副本：`/tmp/furedi_121_kahn_seymour_fractional_matching_polytope.txt`。§1 的 Theorem 1.4 给出相交超图分数匹配的按边大小加权约束；Theorem 1.5 给出固定均匀度、相交条件下总两两交数的极值下界及射影平面等号情形。定理不以边数/均匀度比 \(m/r\) 为参数，因此不是候选 max 公式的直接陈述。

3. **Zoltán Füredi, “Intersecting designs from linear programming and graphs of diameter two,” Discrete Mathematics 127(1–3) (1994), 187–207, DOI [10.1016/0012-365X(92)00478-A](https://doi.org/10.1016/0012-365X(92)00478-A).** 已读全文，副本：`/tmp/furedi_122_intersecting_designs.txt`。§4 Theorem 4.1 汇总相交秩 \(r\) 超图的分数匹配数上界与极值结构；Problem 4.8 则按底层顶点数 \(p\) 询问相交超图分数匹配数的最大值。这里主要控制秩或顶点数，没有待比较的按 \(m/r\) 分层曲线。

## 构造中使用的已知结果

- **R. M. Wilson, “An existence theory for pairwise balanced designs, III: Proof of the existence conjectures,” Journal of Combinatorial Theory, Series A 18(1) (1975), 71–79, DOI [10.1016/0097-3165(75)90067-9](https://doi.org/10.1016/0097-3165(75)90067-9).** 仅核对了出版方 primary abstract 与 Crossref 元数据，未读全文。摘要给出固定区组大小 \(k\)、指数 \(\lambda\) 的 BIBD 对所有充分大且满足相应整除同余条件的 \(v\) 存在。取 \(\lambda=1\)，即 Steiner \(2\text{-}(v,k,1)\) 设计的条件
  \[
  v-1\equiv0\pmod{k-1},\qquad v(v-1)\equiv0\pmod{k(k-1)}.
  \]
  该存在定理用于主稿下界构造中的设计族，不是候选有限上界的证明输入。
- **Jeff Kahn, “On a Problem of Erdős and Lovász. II: \(n(r)=O(r)\),” Journal of the American Mathematical Society 7(1) (1994), 125–143, DOI [10.1090/S0894-0347-1994-1224593-5](https://doi.org/10.1090/S0894-0347-1994-1224593-5).** 已核读其 §5 Corollary 5.4（p. 140）：其整数覆盖结论有固定 \(m\le cr\) 及最大两边交集为 \(o(r)\) 的假设。按主稿所述，该推论只用于设计族下界构造中取得大小小于 \(r\) 的整数覆盖，再据此构造平台族；它不是候选有限分数上界的输入。Wilson 与 Kahn 两项结果在此承担构造侧作用，与有限上界的推导分开。

## 等号与删边稳定性的候选比较

另一个待比较候选针对上述有限上界的严格线性区
`km > (k+1)((k−1)r+1)`。候选称在该区间内，`τ*(H)=m/(k+1)` 当且仅当每个顶点度至多 `k+1`。它还给出删边稳定版：令 `A=km−(k+1)((k−1)r+1)>0`、`d=m/(k+1)−τ*(H)`；若 `d<A/[k(k+1)]`，删去至多

`(k+1)(k+2)(1+m/A)d`

条边后可得到最大度至多 `k+1` 的核心。相应渐近候选为：固定 `k≥2`、`c∈(k−1/k,k]`、`m/r→c` 时，`τ*(H)/r→c/(k+1)` 当且仅当可删去 `o(r)` 条边使剩余核心最大度至多 `k+1`。此处只记录候选定理的表述，不审核证明。

本轮复查的近邻结果没有给出同一等号或删边结论：

- Z. Füredi 1981 的 “Maximum degree and fractional matchings in uniform hypergraphs,” *Combinatorica* 1(2) (1981), 155–162, DOI [10.1007/BF02579271](https://doi.org/10.1007/BF02579271)，Corollary 3 给相交均匀超图的最大度二择界：要么是阶 `r−1` 的射影平面，要么 `Δ≥m/(r−1)`。这是 `m`、最大度与均匀度的关系，不是上述按任意整数 `k` 的分数覆盖等号刻画或缺损删边稳定性。
- FKS 1993 的 Theorem 1.5 等号条件是特定的总两两交数极值取等时，超图为射影平面线集（允许各边相同重数）。这与“`τ*` 恰好达到当前有限公式的线性项，当且仅当最大度不超过 `k+1`”所刻画的族不同；定理中也没有从分数缺损控制需删除边数的结论。
- Füredi 1990 的 Theorem 2.5 固定底层顶点数并给出射影平面相关的分数覆盖界；Theorem 3.1 则关联点对覆盖与最大度约束。Füredi 1994 的 Theorem 4.1 及 Problem 4.8 分别聚焦秩界、顶点数参数。这些已读条目没有直接给出候选中的有限阈值等号条件或显式删边数。

在以上已读全文与本轮有限关键词搜索中，未找到相同的等号刻画或稳定性估计。此为有限范围未命中，不表示不存在其他等价结果；亦不作原创性或优先权判断。

## 仿射空间 partial-pencil 构造的术语查重

另一个候选下界构造取固定素数幂 `q`、`N≥3`，在 `AG(N,q)` 的点—仿射线关联对偶中，将方向视为部；从每个方向选一条线，并通过修改一个点铅笔中的部分方向线得到覆盖所有点的超边。不同二维子空间产生大量不同超边。主稿据此构造 partite 族达到候选分数前沿的平台段，并再以 padding 得到斜坡段。这里仅记录用户提供的构造描述，不审核其覆盖、计数或最优性证明。

本轮用 DuckDuckGo 搜索了 “partial pencil affine space”, “one line in each direction”, “line cover finite affine space”, “affine line transversal” 及 parallel-class/point-cover 组合词，并用 Crossref 检索 affine line-cover 与 partial-pencil 词组。没有找到直接陈述“每个方向选一条仿射线且这些线覆盖所有点”或该点铅笔改线构造的来源。Crossref 的近似标题结果包括 J. A. Thas, “Partial geometries in finite affine spaces,” *Mathematische Zeitschrift* 158 (1978), 1–13, DOI [10.1007/BF01214560](https://doi.org/10.1007/BF01214560)，以及有关 affine line-transitive planes 的论文；仅核对了这些检索条目的书目元数据，没有读其全文，也没有证据表明其包含候选构造。检索未命中不证明不存在先例，亦不作原创性或优先权判断。

## 范围说明

有限公式的搜索是有界的关键词与数据库检索，并非穷尽性综述。三篇 Füredi 论文均读了全文；Wilson 只读 primary abstract 和元数据；Kahn 的此处比较限于已核对的 Corollary 5.4。当前没有发现相同 max 公式的直接先例，但本筛查不据此宣称定理为首次，也不排除尚未检索到的等价表述。
