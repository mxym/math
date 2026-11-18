# A split graph with nonunimodal domination sequences

A single explicit finite connected split graph has a **nonunimodal** coefficient sequence for each of its ordinary, total and connected domination polynomials. For each family there are three increasing set sizes for which the middle coefficient is strictly smaller than the other two. The argument does not require that the same three indices work for every family.

| Polynomial | Which sets are counted? | Implication |
|---|---|---|
| Ordinary domination | All sets whose closed neighborhoods cover every vertex | A counterexample to [Alikhani–Peng's general conjecture](https://arxiv.org/pdf/0905.2251#page=7), not a result about trees or minimal dominating sets. |
| Total domination | Every vertex, even if selected, must have a selected neighbor | A counterexample to [Alikhani–Jafari, Conjecture 2.9](https://arxiv.org/pdf/1605.02222#page=5). |
| Connected domination | A dominating set must induce a connected subgraph | A negative answer to the **coefficient-shape** subquestion in [Shao–Zhao, Open Problem 4](https://arxiv.org/pdf/2609.06569v5#page=14). Its positive support is an interval, so it also fails log-concavity. This does not settle the paper's questions about roots. |

**Why there is a valley.** Start with the incidence graph of the points and nonvertical lines of the affine plane over the field of order $q=2^{40}$. Replace every position by groups of vertices, make the group vertices a clique, and add one independent auxiliary for each pair of incident groups. A uniform random subset has two ways to guarantee domination: hit every group on the point side, or every group on the line side. These events have exactly equal probability but their expected set sizes differ by $q^2/3$. The [proof](PROOF.md) bounds the mass in each concentrated size range and proves that all remaining dominating subsets contribute too little to fill the intervening valley. In particular, it counts auxiliaries that must be selected when neither neighboring group is hit.

**Size and verification.** The graph has $14q^2+6q^3=7{,}975{,}367{,}974{,}726{,}420{,}198{,}897{,}447{,}170{,}127{,}953{,}920$ vertices. The witness is explicit as a graph and three index windows; the individual coefficients of this graph have not been enumerated. It is not claimed to be the smallest example. [Two exact checkers](CHECKS.md) verify the constants and exhaustively test the counting identities on a 20-vertex model.

**Research draft, 18 November 2026.** The argument and its [separate internal audit](REVIEW.md) were AI-assisted. There has been no external peer review or proof-assistant verification; no global priority is claimed. [Prior work and scope](SOURCES.md) distinguish existing non-log-concavity, independence and zero-forcing results from nonunimodality of domination.

**中文摘要。** 一个显式有限连通分裂图的普通、全及连通支配多项式均非单峰。证明在两个等概率但典型大小不同的点集族之间找出系数谷，并显式控制其余支配集的总量。普通支配结论针对一般图，不解决树的情形；连通支配结论仅涉及系数形状，不涉及根。本稿仅经独立 AI 辅助内部核查，未经外部同行评审。
