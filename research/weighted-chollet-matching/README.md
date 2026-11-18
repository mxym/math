# 任意非负加权图的强 Chollet 不等式与精确匹配公式

[完整三页证明（PDF）](paper.pdf) · [TeX 源文件](paper.tex) · [精确复核程序](check.py)

对任意不含自环的有限无向图，给每条边赋予非负实权，令 `H=L+diag(α)`，其中 `L` 是加权 Laplacian，`α≥0`。对每个顶点子集 `S` 都有

    per(H[S] ∘ H[S]) ≤ per(H[S]) · ∏_{i∈S} H_ii ≤ per(H[S])².

主子矩阵保留原图的加权度。允许空集、零权边、孤立点、奇异矩阵及非二分块。事实上所有实对称半正定 Z 矩阵都满足该自乘不等式。

更强的精确结论：固定单位对角的复 Hermitian 半正定矩阵 A。让 B 遍历单位对角的复 Hermitian 半正定矩阵，且令 B 的比较矩阵（对角为 1，非对角为 −|b_ij|）半正定。则 per(A ∘ B) 的最大值为

    max_{匹配 M} ∏_{ij∈M} (1+|a_ij|²) ≤ per(A).

对每个最优匹配，以二阶全一块及单点块构成的 B 就达到该值。证明把永久量写成独立出箭的有向圈乘积的期望，并在每个圈里选取一条边，再用 Lieb 的主块永久量不等式。

## 与此前工作的关系

- Pant–Singh [arXiv:2604.24192v2](https://arxiv.org/html/2604.24192v2) 第 6 节的问题针对简单无权图。仓库[既有无权全图定理及其 Lean 证明](../../preprints/all-graph-chollet-2026-10/README.md)不作为本次新发现。
- 仓库[加权周期及块图证明](../weighted-cycle-chollet/PAPER.md)已探索独立邻点选择和匹配上界，明确未证明所有加权图和半正定 Z 矩阵。目前的完整证明也适用于该先前范围以外的图。
- 函数有向图上的永久量展开和圈乘积分解是已有技巧；具体文献及与本问题的区别见论文末尾。Lieb 的已证主块不等式是外部输入。
- 这是 AI 辅助研究与写作的普通书面证明，不是对任意两个半正定矩阵的 Chollet 猜想的解答，不是外部同行评审、Lean 形式化或历史优先权认证。未改写旧证明或冻结验证范围。

## Reproduction

With Python 3.9+ (standard library only), run:

```sh
python3 check.py
sha256sum -c SHA256SUMS
```

The diagnostic checks every principal set for each of 729 nonnegative edge-weight assignments on four vertices and two diagonal shifts (23,328 instances). The nonbipartite worked example is checked independently using direct permutation sums and Ryser's formula. These finite checks illustrate the proof; they do not prove the all-size theorem. The PDF can be rebuilt from the self-contained source with two passes of `pdflatex -halt-on-error paper.tex` in a TeX Live installation with the listed packages.
