# 论文主定理—Lean 对应表

本表按论文《四个等质量高斯单元：协方差变形与四面体刚性》的实际证明链记录形式化覆盖。表中“已严格证明”只表示当前 Lean 工程中有无 sorry、admit、自定义公理或未披露桥接的内核检查证明；“缺口”表示论文中仍需要补齐的数学命题。

| 论文命题或证明环节 | 必要数学引理 | 当前 Lean 入口 | 覆盖状态 |
|---|---|---|---|
| 四单元平衡价格与原始分区对象 | 可测 winning cell、平衡价格、分区不交、Bochner 一阶矩 | GaussianMeasureBridge.winningCell、GaussianFourGlobal.balanced_winning_limit、GaussianMeasureBridge.FractionalPartition | 已证明对象级引理 |
| 协方差目标的因子化、齐次性与固定方向导数 | PSD 因子化、Gaussian 线性像、对称迹公式 | GaussianFour.actual_centered_covariance_fixed_differential 及 FixedCovarianceDifferential.lean | 已证明一阶方向结果；尚非完整 Frechet Hessian |
| 平衡自矩与价格矩阵关系 | 局部极值的一阶必要条件、中心化、正定约束 | GaussianFour.actual_four_local_extremum_self_moments、GaussianFour/SelfMomentCriticality.lean | 已证明带明确局部极值假设的结果 |
| 价格目标的二阶变分 | Gaussian facet flux、价格 Hessian、常数平移核 | GaussianFour.actual_simplicial_price_hessian、GaussianFour.actual_simplicial_price_hessian_nondegenerate | 已证明价格 Hessian；不能替代协方差 Hessian |
| 秩一边界排除 | Gram 秩等于行空间维数；秩一表示为共线；单位方向归一化；任意标签置换为严格有序；winning cell、质量、自矩置换输运；一维 Gaussian 投影与谱障碍 | GaussianFour.exists_unit_strictMono_rankOne_representation、GaussianFour.winningCell_perm、GaussianFour.exists_rankOne_ordered_actual_obstruction | 已证明 rank-one bridge 与实际质量/自矩输运；任意奇异极限的 facet 矩阵识别仍缺 |
| 奇异边界的 facet 系数 | 正质量图表、图表独立性、系数连续性、Laplacian 极限 | GaussianFour.continuousAt_intrinsicPairWeight、GaussianFour.balanced_simplicial_limit_laplacian | 已证明在书面假设下的实际 Gaussian 通量结果 |
| 秩二平面情形 | 四个自矩点的 affine span 维数界与非平凡仿射关系；完整 hull 分类与谱违背 | GaussianFour.score_vectorSpan_le_two、GaussianFour.exists_nontrivial_affine_relation_of_scoreGram_rank_le_two、GaussianFour.affine_relation_all_coeff_ne_zero_of_triple_affineIndependent、GaussianFour.affine_score_relation_constant、GaussianFour.affine_relation_no_two_diagonal_facets、GaussianFour.affine_relation_one_positive_convex_combination、GaussianFour.affine_relation_has_two_pos_two_neg_of_hull_vertices | 已证明秩二仿射依赖、三点非退化支持、得分常数关系、凸组合构造及凸包顶点下的二正二负结论；完整 hull 分类与实际谱违背仍缺 |
| 正则化临界序列与协方差山路 | 协方差 Hessian、约束保持流、minimax、奇异极限 | GaussianFour/PriceHessian.lean 等仅提供价格侧工具 | 尚未形式化 |
| 四单元 Gaussian 周长下界及刚性 | 实际 Gaussian perimeter 的四单元等质量下界、三单元合并界、刚性 | 现有 GaussianFourCellTheorem 仅接受显式 perimeter bound 假设 | 尚未形式化；不能作为公理或接口输入 |
| 正四面体精确常数 | 实际 Gaussian Bochner 矩、角积分、12*(arctan(sqrt 2))^2/pi^3 | 当前仅有标量代数和部分候选计算 | 尚未完成 |
| 原问题最终不等式与等号分类 | 将上述链条连接到任意可测四胞/分数分区，并处理维数嵌入与 a.e. 等号 | GaussianFourCellTheorem 是条件定理，不是论文主定理 | 尚未完成 |

当前工程因此提供一组真实 Gaussian 对象上的可复核核心证明，尚未导出论文的无条件全局 sharp theorem。任何发表说明都必须保留这一区分。
