# 电路复杂度研究归档索引

三条主线：短线段限制（519）、Heawood 图（582）、射影平面入射函数（2583）。三道原题均未解。以下“纸证已复核”指有人独立检查了数学论证，不等同于 Lean 形式化；“有限重放”只确认明确列出的输入与边界；未经逐分支独立检查的结果列入“待审”。

## 519｜短线段与门消去

- **纸证已复核（有限制）**：在诱导短线段 `a-u-v-b` 的约定条件下，设 `H=G−v`、`K` 为 `H` 的度数至少 2 的顶点诱导图。保留围长、枢纽间距、已知 `H` 下界取等和局部读者条件。给 `v=0` 恰删两门、图亏量恰为 1 的相应 AND/NOT 拼接子类，可对任意父顶点度数证明排除；正向拼接分别处理无 NOT 和恰一存活 NOT。无 NOT 核心是把付费分叉规约为最小点覆盖上的原始读者，再对诱导 `P₄` 的同两次物理出现比较两个限制，迫使同一个最低公共祖先同时为 AND、OR。单 NOT 证明依赖其独有的不变式，不由无 NOT 结论直接推出。整条受限子类未 Lean 化。
- **有限重放**：早期亏量 1 的小点覆盖预算程序可收入附录作为交叉检验，不是任意预算纸证的依赖。保留精确图类、绑定对称性、搜索穷尽理由和执行入口；不收逐次数的日志。
- **待审／未解**：只有一个 `v` 的 OR 读者后接复杂扇出的若干分支已经写成纸稿，尚未统一审计，不算主定理；更高亏量和一般读者／NOT 结构仍开放。

## 582｜Heawood 图的边函数

- **纸证＋独立整数重放**：单调二叉公式最少 **27 门**，且七点星构造达到。证据为 21 个正边、21 个独立负赋值和四个线图距离的整数权重 `(-8, 8, 2, -1)`。通信协议的叶子给出**不相交分区**（不是一般覆盖），每个输入叶合法矩形权重最多 24；总权重 672，故至少 28 叶。可单独归档为完整公式定理，不声称适用于共享 DAG。
- **纸证＋有限重放（26 门、最小安全规范形）**：记 `t` 为输出 OR 树下的安全 AND 创建项数。`t=8` 排除至多两个不同共享内部输出；三共享情形排除所有不连通祖先关系、全纯、恰一个混合输出、所有二入叉及混合共底的一分二。`t=9` 排除至多三个不同共享内部输出。混合共底一分二使用正确预算 `L + q₁ + q₂ + d ≤ 12`，更正版读回重放了 381,364 个几何框架和 4,306 个整数情形，旧版 `≤ 11` 不足以认证全分支。纯共底、两混合上线各一门的一分二有独立纸证和小规模交叉检验，可作为单独附注。`t=10` 的穷尽枚举及 `t=11,12,13` 的 DRAT 排除属既有材料，不应列作本轮新证；只有连同对应实例与验证器才可重放。
- **未解**：较低 `t` 的多共享 DAG；`t=8` 恰三共享仍余至少两混合输出的全序链，以及纯共底、两混合且至少一个上线有两门以上的一分二；`t=8,9` 的更多共享也未排除。注意“不同共享输出数”不是总额外扇出数。

## 2583｜射影平面入射函数的 read-once 规约

- **纸证已复核（任意 `q ≥ 2`）**：设 `N = q² + q + 1`、`E = N(q+1)`。一般精确单调二叉电路有下界 `s ≥ 4N − (q+1)√q − 3q − 5`，另有精确整数改进（Fano 情形给 `s ≥ 22`）。若能固定选一色，使每个活 AND 至多有一个操作数带该色祖先，则下界达到自然星形构造的 `E + N − 1 = N(q+2) − 1`，允许另一色有共享或任意单调 guard。另一个已复核的精确类：仅一处两条含线信号相 AND，其余含线乘法使用原始点 guard，可任意重复原始 guard，但没有纯点注入或额外复杂点 guard。
- **待审**：在齐次、唯一两含线输入 AND、显式追踪方向与位置的模型中，名义额外 OR 预算 `δ ≤ 3` 的分类已写齐；名义／存活副本的总账和 Hall 结构经过复核，末端 guard 路由与 Fano 特殊子类未全部独立核验。唯一富点 guard 的扩展及 `δ = 4` 的若干狭义子类可留作待审附录，不当成一般界。验证局部改写失败的非最小 Fano 电路，只是对该改写的反例，不是原题的反例。
- **未解**：任意 AND/OR 电路都可改为不增加门数的 read-once 电路。多处含线非线性 AND、任意混色注入及多个复杂 guard 的交互未解决。

---

## Short-thread local endgame (conditional)

The following is the last step only. Let $H$ contain the leaf $u$ adjacent to $a$, have girth at least seven, and let $a,b$ be nonadjacent with no common neighbor. Suppose the paid raw forks form a minimum vertex cover $S$ of the subgraph induced by the degree-at-least-two vertices, with $b\in S$. Assume the cut wires $h,r$ stay true with $(a,u)=(0,1)$, no remaining computed sharing, and at most one exterior occurrence of $b$ or any unselected core raw. These are hypotheses of this endgame, not obtained here from an arbitrary circuit.


Since S is a **minimum** K vertex cover and b∈S, b has an unselected K-neighbor z. Otherwise all its K-neighbors would be selected, and deleting b would still cover every K edge, contradiction. Thus z is H-core (deg≥2) but terminal. Choose y adjacent to b other than z, and x adjacent to z other than b. They are all distinct: y=x would form triangle; extra edges y-z and x-b each triangle, x-y four-cycle. So induced path (y-b-z-x). None equals a or u: y,z aren't a by no ab; x isn't a because z would be a common neighbor; u only adjacent a and both b,z differ from a; b distinct by original thread.

Now in actual H set a=0,u=1 and every other raw except (x,y,b,z) to 0. Then actual h=r=1 independently of these four bits by positivity and the u-singleton values. With these cut wires held fixed, the exterior expression is positive read-once on **physical** occurrence tokens: only remaining original forks are raw, so unfold every raw reader as its token, no computed sharing. b and z each represented at most once. At y=x=0, function of b,z is (b∧z). At y=x=1, function is (b∨z); the fixed endpoints don't themselves make an edge, and u's sole neighbor a=0. These statements use only induced P4, regardless of duplicated y,x or other original raws. Both binary restrictions are doubly essential, so b,z are physically present. In any positive read-once formula, the binary operator of a doubly essential two-port cofactor is the gate at their unique LCA: every other branch specializes to a constant, and each surviving unary positive gate relays its bit (or destroys an essential dependency, excluded). The same two physical leaves cannot meet at AND in first restriction and OR in second. Contradiction. No condition on number of exterior copies of a, since a fixed0. No local graph casework or τK limit.

This exact short argument was independently discovered again by extracting conditional pair-LCA constraints from the hardest 21-leaf synthetic miter: rectangular graph rows forced b,z AND and OR simultaneously. The selected b min-cover core neighbor z shows that this conflict is always available in the original all-raw graph, so the large miter relies on stronger simplifications than necessary.


## Heawood: exact monotone formula size

This is a formula theorem, not a lower bound against arbitrary circuits. Identify points and lines with the seven nonzero binary vectors in three dimensions, and put an edge when their dot product over F₂ is zero. Let G be this cubic Heawood graph; the Python replay below reconstructs its 21 edges. For a positive edge e use the input with just its endpoints true. For a center edge c=(p,l) set exactly vertices in I_c=(N(p) minus {l}) union (N(l) minus {p}) true. This is an independent set of four: any edge between its sides would form a 4-cycle with c. Thus it is a valid negative input. We use 21 negatives, not all 37 maximal ones. Index the 21 x 21 matrix by (e,c); let its INTEGRAL weight be (-8, 8, 2, -1) at distance (0,1,2,3) between e,c in the line graph. Each row distance multiplicities 1,4,8,8 give mass 32; all rows have mass 672=28*24.

For every monotone binary formula computing F, an exact rectangle partition of this matrix is obtained by descending the formula from the root. A current gate is true on the positive row and false on the negative column. At an OR choose the first child true on the row, a row-only decision; both children are false on the column. At an AND choose the first child false on the column, a column-only decision; both children are true on the row. Hence each leaf receives a (possibly empty) rectangle, and the rectangles are pairwise DISJOINT and cover the entire matrix. Covering alone is not enough with negative weights. A leaf of input label v receives only rows among its three incident edges and columns c with v outside I_c. For a chosen nonempty row subset S its largest rectangle mass is exactly sum over allowed columns c of max(0,sum over e in S of W[e,c]). The 14-by-7 table (rows in vertex order, subsets as binary masks 1..7 in incident-edge list order) is
0: 24 24 24 24 24 24 24
1: 24 24 24 24 24 24 24
2: 24 24 24 24 24 24 24
3: 24 24 24 24 24 24 24
4: 24 24 24 24 24 24 24
5: 24 24 24 24 24 24 24
6: 24 24 24 24 24 24 24
7: 24 24 24 24 24 24 24
8: 24 24 24 24 24 24 24
9: 24 24 24 24 24 24 24
10: 24 24 24 24 24 24 24
11: 24 24 24 24 24 24 24
12: 24 24 24 24 24 24 24
13: 24 24 24 24 24 24 24
Thus each leaf contributes at most 24, so >=28 leaves, >=27 gates. This includes all depths. A matching 27-gate formula ORs the seven three-edge point stars: 7*(2 OR+1 AND)+6 OR=27. Every <=26 circuit (if one exists) has an internal fanout >=2. Let r=sum_g (fanout(g)-1) over live nonoutput gates. Number of raw input occurrences = m+1-r, so with all 14 variables essential at least 27-m+r are read once, at least two for m<=26 and r>=1.


```python
from collections import deque

edges = [(p-1, 6+l) for p in range(1,8) for l in range(1,8)
         if (p & l).bit_count() % 2 == 0]
N = [set() for _ in range(14)]
for p, l in edges:
    N[p].add(l); N[l].add(p)
neg = [(N[p] - {l}) | (N[l] - {p}) for p,l in edges]
assert all(not any({p,l} <= I for p,l in edges) for I in neg)
adj = [[j for j,f in enumerate(edges) if j != i and set(e)&set(f)]
       for i,e in enumerate(edges)]
weights = (-8,8,2,-1)
W = []
for i in range(len(edges)):
    dist = {i: 0}
    todo = deque([i])
    while todo:
        j = todo.popleft()
        for k in adj[j]:
            if k not in dist:
                dist[k] = dist[j]+1
                todo.append(k)
    W.append([weights[dist[k]] for k in range(len(edges))])
assert sum(map(sum,W)) == 672
for v in range(14):
    incident = [i for i,e in enumerate(edges) if v in e]
    assert len(incident) == 3
    for m in range(1,8):
        mass = sum(max(0,sum(W[i][c] for j,i in enumerate(incident) if m>>j&1))
                   for c,I in enumerate(neg) if v not in I)
        assert mass == 24
print("matrix mass 672; 98 legal-row-subset maxima all 24")
```

---

## Projective planes: a general lower bound by line-prefix bins
Paper proof, not Lean-formalized or a full read-once reduction. Let G be a projective plane of order q≥2, N=q²+q+1. Let s be a clean binary AND/OR size computing exact point-line edge function. The primary unconditional derived lower is s≥4N−(q+1)√q−3q−5, with a sharper exact integer rule below (q2 gives s≥22, short of read1 benchmark 27). For circuits where every raw of one color reaches output without passing a fork, this argument proves the full benchmark s≥N(q+2)−1.

### Incidence and first-fork facts
Each point degree is q+1: the q other points on each containing line partition N−1 other points. Any two distinct lines meet at most one point; fixing one line, each of its q+1 points is on q other lines, with all q(q+1)=N−1 such lines distinct, so in fact any two lines meet exactly once. Both orientations are symmetric. Isolated inputs absent.

Discard dead gates and duplicate-operand semantic aliases (or work in global minimum; the resulting lower applies to original size). There are 2N active essential raw wires. Count fork surplus k from s=3N−1+k: total Σ(outdeg(w)−1) over all nonoutput live wires is s−2N+1=N+k by binary arc count, hence number of different physical fork wires ≤N+k. For each raw, follow its unique consuming chain until the first fork wire, or output if none. Group raws by this terminal; all paths from a member affect exterior only through its terminal, and raw terminals/forks naturally ordered by original circuit topological order (output last). Later-bin raw cannot influence earlier terminal. Call a raw active if some G neighbor is in a strictly later bin. This usage of active means temporal, not semantic relevance.

Any edge endpoints in same bin would have their single-bit internal signal restrict to AND (other raws0) and OR (choose one alternative neighbor of each, forming host-independent pair by triangle/C4; other raws0). The two unique paths coalesce inside terminal, their LCA op cannot change at different fixed contexts while both remain essential; afterwards dependence on the one-bit signal must be identity by monotonicity. Thus every edge has distinct bins and its earlier endpoint active. The active raws form a vertex cover. Two active raws in same bin have identical later neighbors, from empty/u/v profiles through one bit under earlier-zero contexts. If earlier t is neighbor of only one, common later z gives three profiles 00/11/01 (t,z same color by shared neighbor, hence nonedge); impossible. So two active raws in same bin would be open-neighborhood twins, impossible since degrees≥2 and graph C4-free. Thus active raws inject into physical forks, giving |cover|≤N+k. Minimal cover size N by regularity (each vertex covers at most q+1 of N(q+1) edges), so k≥0.

### No active point bin ever contains a raw line
If a line in same bin as active point p is itself active, forbidden by the previous injectivity. Otherwise call it w. Every neighbor point of w lies in strictly earlier bin, from inactivity and no edge endpoints same bin. Choose any later neighbor line z of p (active), distinct from w. By C4, at most one neighbor of w also neighbors z, hence choose an earlier point t in N(w)\N(z). With t=1 and all other exterior points0, test z=0,1; at inputs to bin equal empty, p-only, w-only profiles are 00,01,11, respectively. Here f({t,p})=0 by color and f({t,p,z})=1 via p-z. A single internal bit cannot transmit three profiles. Hence no raw line in p's bin. The argument also works with colors exchanged, no assumption that the active cover is one full side.

Choose orientation so x=#nonactive points ≤ a=#nonactive lines. There are N−x different active point fork bins; all bins containing a line and ending in a physical fork are among remaining ≤(N+k)−(N−x)=k+x. The output bin is separate and may exist even if no line has no fork.

### Exact single-color prefix accounting when bins contain 2+ lines
Call a line good if it has no fork to output (output bin), or its first fork bin has at least two distinct raw lines. Only lines in singleton line-fork bins are omitted (such a bin can also contain irrelevant-color raws, which do not matter). Denote b0=#singleton line fork bins (one omitted line each), m=#multiple-line fork bins of good lines. Thus b0+m≤k+x.

Fix a good line l, and let w be its first-fork terminal or output. In its entire unique prefix l→w, no wire has positive universal all-lines=0 projection: compare output under all points=1 with all lines0 versus only l=1 (output0 versus1). Every prefix wire is a single-bit interface for l, its value must switch; monotonicity forces 0 at all-lines0 and all points1, so identically0 under all-lines0 on every point input. This also ensures disjoint charging below.

Let Z_l be point assignment with exactly all points outside N(l) true. At only l selected and P=Z_l the global output is 0; we need w=0 there. If w is output, immediate. If its raw bin includes another line l', then N(l')\N(l) nonempty by C4 and degree≥2. With only l' selected at same P, output1. Temporarily regard w as external Boolean parameter; neither l nor l' otherwise affects the exterior because all its paths pass through w. Thus w must take different bits on the two assignments (and exterior is monotone in it), giving w=0 on l and w=1 on l'. No argument here requires l to be active or w itself to be safe.

If w=0 at this l+outsider assignment, some AND on the l→w prefix has lateral operand W_l false on that assignment; if every AND lateral operand were true, the initial raw l=1 would propagate through every AND/OR. This operand is independent of l structurally, otherwise l would have two paths before its first fork w (if the AND is w itself, distinct incoming branches still require earlier fork). Thus W_l in universal all-lines0 projection is also false on Z_l. Conversely, for each adjacent p, the true edge row {p,l} versus singleton {p} must switch every l-prefix wire, so every prefix AND lateral operand, including W_l, is true on {p,l} and thus {p} in universal projection. Therefore this one W_l root has exactly neighborhood singleton support N(l) and is low on Z_l.

Perform simultaneous all-lines0 simplification across every gate position, maintaining all nonzero outputs of interest (zero literal folds, neutral aliases; no constant-one generated in monotone clean AO2 from replacing raws by0). No copied original gate positions. For each good l trace backwards from its nonzero projected W_l; at OR both children low on Z_l, at AND pick a fixed low child, stopping at wires with ≤1 singleton support. Every accepted singleton at W_l reaches some terminal accepting it (OR choose a true child at singleton input; fixed child of AND true on every input where AND true). Distinct terminals for each of q+1 neighbors. Binary arc count gives ≥q internal projected gates, each with ≥2 singleton supports ⊆N(l). No original projected internal gate can be charged for another line by C4. None is an original line-prefix gate: any prefix gate for any branch line has universal projection0 as proved. Thus charge q distinct projected gate positions per good line.

Each designated low AND along good l prefix is distinct globally. Prefixes in different bins cannot meet (after any shared wire before first fork, both would have the same first fork or output). In same bin, if l,l' enter this AND from same operand side, the common opposite-side projected root would have to carry both identical neighborhoods, impossible by C4 and q+1≥2. If from opposite sides, choose p adjacent l; the other operand is a prefix wire for l' and absent l structurally, so equals zero all-lines projection at {p,l}, incompatible with the AND needed by switching l. Thus charge one further gate per good line.

Within each line bin with t>=1 good lines, their unique paths merge to one terminal w, so exactly t−1 nodes have two incoming arcs of the union of line prefixes (count one outgoing arc per nonterminal wire within union). Every such merge is OR, not AND: if lines from opposite incoming branches, one operand vanishes all-lines0 and cannot contain the other branch's line before its first fork, so cannot help its single-line positive signal. Distinctness from projected point charges (prefix projection0) and selected AND charge (different gate op). Sum merge count across good bins: ≥#good lines−m−1 (the +1 permits output bin, whether or not present). Total charges:
s ≥ q(N−b0) + (N−b0) + ((N−b0)−m−1)
  = (q+2)(N−b0)−m−1
  ≥ (q+2)N−1−(q+2)(k+x).
Putting s=3N−1+k gives sharp intermediary
**(q−1)N ≤ (q+3)k+(q+2)x.**

If no line ever forks, b0=m=0 and literal full desired bound. More broadly the count pays every output-bin line and every multi-line fork-bin line, regardless of whether earlier shared point or line guards occur; lost singleton bins are the explicit deficit, not generic "bad overlaps."

### Eliminate x via incidence counts
Nonactive raws form independent set (active is a cover). For the x nonactive points, write d_l=#such points incident to line l. Σ d_l=(q+1)x, Σ d_l²=x(x+q) via unique common line for each pair. By Cauchy–Schwarz, they meet ≥(q+1)^2 x/(x+q) lines (valid x=0 by direct interpretation). None of touched lines is nonactive. Hence
a ≤ N−(q+1)^2 x/(x+q) = q(N−x)/(x+q).
Also x+a≥N−k by cover size≤N+k. Rearranging gives x(N−x)≤k(x+q). Since a≥x by orientation, another rearrangement gives x²+2qx≤qN, so x≤√(q(N+q))−q=(q+1)√q−q.

Integer filter: given q, test the least integer k≥0 for which there is integer 0≤x≤N/2 satisfying both inequalities plus (q−1)N≤(q+3)k+(q+2)x. Results for q=2…8: k≥2,4,8,12,19,27,37. This is a necessary-condition check, not exact complexity. Moreover any k<q forces x=0: if x>0 with a≥x, then 1≤x≤q², and x(N−x)/(x+q)≥q (equivalent to (x−1)(q²−x)≥0), contradiction. Then (q−1)N≤(q+3)k fails since N>q+3. Hence universal k≥q in all q.

Smooth closed form: using X=(q+1)√q−q above, k≥((q−1)N−(q+2)X)/(q+3). Since N−k≤(4N+(q+2)X)/(q+3)≤4(q+1)+X,
s≥4N−1−4(q+1)−X=4N−(q+1)√q−3q−5.
Use max of all forms. Asymptotically 4N−O(N^(3/4)), still well below N(q+2)−1. To approach full target the concrete deficit is only line-singleton branch bins whose prefix terminal can be1 on maximal outsiders, because the particular line row may be rescued by downstream branching conditions. Need to charge suitable downstream low gates without overlap between different singleton bins (or restructure their branches). The separate singleton-interface note supplies shared witness accounting toward that step.
