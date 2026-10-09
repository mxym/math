# Strong Chollet inequalities for all simple graph Laplacians

Yongxian Zhang（张永贤），华南理工大学计算机科学与工程学院。

[论文 PDF](paper.pdf) · [独立 TeX ZIP](paper-source.zip) · [完整 Lean 工程](../../formalizations/laplacian-chollet-all-graphs-progress/README.md)

任意有限简单无权图的 Laplacian、任意主子矩阵，均满足
`per(L[S] ∘ L[S]) ≤ per(L[S]) · ∏_{v∈S} deg_G(v)`。其中 `∘` 为逐项乘积。主子矩阵保留原图度数；空矩阵、奇异矩阵、孤立点及非连通图全部包括。非负对角添加也成立。

本文按正常研究论文组织完整书面证明：精确问题与历史来源、两个既有定理、cycle-trace 上界、完整 odd-set matching 约束、两类块、对角添加和 one-point sum、全图组装及复现入口。非周期二连通块还给出证明中已有的显式指数缺口；不声称该常数最优或已单独 Lean 化。

书面证明使用 Lieb 已证明的 block permanent inequality 与 Edmonds 已证明的 matching-polytope theorem。独立 Lean 证明采用 Gram/Fischer 下界、匹配多面体、度数二块的第三迹及加强的顶点数归纳；两条路线的区别在正文说明。完整 Lean 结论覆盖全图与对角添加，本文不把所有辅助陈述都算作已形式化。

已有归档：书面稿 https://doi.org/10.5281/zenodo.23248359；完整 Lean 源码 https://doi.org/10.5281/zenodo.23252138。本文正式稿已作为同系列版本 3.0 公开：https://doi.org/10.5281/zenodo.23252964。旧档案保留。

重编排版：从仓库根目录运行 `python3 preprints/article-revisions-2026-10/build.py`。Lean 内核复现按固定证明工程的 README、case.json 与 reproduce.py 执行。本文排版检查不冒充本轮新 Lean 重放。

范围不包含任意加权图或一般 PSD Chollet 猜想。无外部研究经费；使用AI进行辅助研究，研究方法与写作披露分别列明。保留已有许可及第三方来源；未另行授权原创材料保留全部权利。

[Article audit and exact publication scope](../../reviews/manuscript-quality-2026-10-08/README.md).
