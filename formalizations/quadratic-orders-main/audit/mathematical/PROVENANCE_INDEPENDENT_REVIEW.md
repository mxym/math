# Round5 来源、闭包、声明清单独立复核

日期：2026-10-07（UTC）。对象：`source/` 中交付的 round5 冻结归档。本报告只读源码、重算哈希、独立重走 imports、重新解析既有 compiler logs，并在自动清理的隔离临时副本中运行生产 Python validator 的负控。**没有运行 Lean，没有把作者 cache/log 计作本次 fresh compilation，没有重建 995 个 CFT 模块，没有下载或发布。** 编译和数学语义总判定由主审的独立工作给出。

## 结论摘要

1. **Round3 的 external manifest omission＋duplicate 漏洞已实质修复。** 原来的完整攻击在 round5 的完整 `verify_sources()` 中被拒绝；即使不改漏扫源、只删入口并以重复行补数，也被拒绝。当前 external closure 独立核对为精确 995 CFT＋4 PNT 唯一源码。
2. **当前归档的完整性、owned modules、stored root/inventory 和当前 source map 对应关系通过此复核。** 1833 条 `SHA256SUMS` 全部匹配；129 个主编译单元恰为 128 个 substantive modules 加 umbrella；2926 个 inventory 名称、2880 个 safe logical roots 均无重复；新外部四模块的 7 个 theorem roots 名称与 inventory 完全相同。两项目逻辑根去重为 2885。
3. **不能声称所有离线 validator 已完全硬化。** 历史六组 validator 的 kind 检查余项仍在；新 weak summarizer 对主根 kind/type、同时删 generated declaration、loaded external module 遗漏均有实证接受案例。当前实际日志没有这些错误；Lean producer 和完整打包流程还有额外防线，见 §5。
4. `SOURCE-HASHES.sha256` 是只有四行的历史来源记录，**不是当轮完整归档清单**；路径不直接适用于本解包目录，当前 main lake manifest 也不匹配其中历史 hash。不能拿它代替实际通过的 `SHA256SUMS`。旧 review coverage 文档仍保留 round3 状态，应与当前 round5 总报告区分。

## 1. 归档哈希和原域冻结

### 实际完整性清单

- `SHA256SUMS`：1833 行，1833 个唯一且安全的相对文件路径，所有文件存在、所有 SHA-256 逐项匹配。
- 整个冻结 source 树共有 1835 个文件，唯一未列入上述清单者为 `SHA256SUMS` 自身和 `START-HERE.md`。
- `START-HERE.md` 与已列入清单的 `lean/ROUND5.md` 逐字相同，因此正文已间接绑定。
- 无 symlink。负控前后全树 path→SHA-256 完全相同。
- 外层 release identity 仍须以主审已确认的上传归档 SHA-256 为锚；归档内部可改写的自报 hash 不是数字签名或作者身份认证。

### `SOURCE-HASHES.sha256` 的准确解释

| 历史记录 | 本包核对 |
|---|---|
| `source/preprints/002-quadratic-order-moats/v3/source.tex` | 原路径不存在；迁移到 `lean/references/entry002-v3-source.tex`，bytes/hash 相同 |
| 同目录 PDF | 本包未含 PDF，不能在本包独立复核 PDF hash |
| `source/lean/lean-toolchain` | 去掉历史 `source/` 前缀后 hash 相同 |
| `source/lean/lake-manifest.json` | 去掉前缀后的当前 main manifest hash 不相同，不能作为当前配置认证 |

原稿 tex 的 SHA-256 为 `c1349aba050aeb5c8c20a6dca07fd8d1f74d029ae9702775eaf96177b597d62f`，与当轮 map/provenance 的原稿身份一致。上述历史路径问题没有造成当前完整 `SHA256SUMS` 的遗漏或失配。

独立比较 round3 的全部 80 个 `Entry002/*.lean`：round5 全部逐字不变，新加 48 个模块；因此不仅 `Targets.lean`，旧的 Orders、Algebra、Graphs、原 strong supply、原 finite sieve、旧 restoration 等源码也没有改写原域。`Targets.lean` SHA-256 为 `f4cbd00f1853dc53b955a2b05e7d07223a6a7fe5e0fc762d87e8ed397fe64671`。这一结论是 bytes 的冻结结论，不替代对新增证明链的数学审查。

## 2. Source closure 和 source map

### 主工程

使用独立处理 nested comments 和字符串的 lexer，从实际 `Entry002.lean` 沿 imports 递归：恰覆盖 128 个实体模块和 umbrella，没有漏模块、没有未解析的 owned import。当前 `audited-modules.json` 和 compiler log 的 `MODULES_JSON` 均无重复，且与实际 129 文件集合精确相等，而不只是数量相等。

独立对主 129 单元及三份新增外部 proof source 做 lexical escape scan，共 132 份，无 `sorry`、`admit`、`axiom`、`native_decide`、`unsafe`、`partial`、`implemented_by`、`opaque`、`extern`、`trustCompiler`、`ofReduceBool`、`ofReduceNat` 或 `debug.skipKernelTC` 命中。此扫描只是一道辅助检查，不被当成 Lean kernel 检查。

从实际 weak main/reduction 文件重走 owned import closure，共 124 个 reachable owned/bridge 源码，无缺文件。直接引用的五个 CFT 模块（包括 RayClass.Topology 和 SUnit.Rank）全部包含在经认证的 995 闭包中；新增弱链没有引入未列入 manifest 的直接 CFT 来源。

### 外部固定闭包

生产 `verify_sources()` 当前原包通过，报告：

- authenticated sources = unique external paths = 999
- CFT = 995；PNT = 4
- patched sources = 76；exact patch 新建 paths = 48
- stored Git commit/tree objects = 136
- path-set SHA-256 = `d16aafaa6a3eeeaad6e0fc7370ff9860d86b685d40aaae5bcef9e0a70a5d385c`

另用本审计自己的 import lexer/遍历从固定三个 CFT 入口及 `PrimeNumberTheoremAnd.Wiener` 出发，不调用作者 closure walker，得到了精确相同的 995＋4 集合，并逐项核对真实源码 hash/imports 与 manifest 相同。

本报告没有重新把作者的 Git implementation 当作“独立 native Git 认证”。主审已在另一路逐 hash 复用既有原生 Git 身份认证并核对 round5 来源。这里生产 Git verifier 的 136/999/76/48 是重新执行结果；独立新增的是闭包/清单核对与负控，不是另一次 Lean fresh replay。

### Proof reuse/source-span map

独立按实际原文/实际 owned 文件重算了 `proof-reuse.json` 全部 69 项：48 个 verbatim body/span 和 21 个明确标记的 adaptation 全部对应。具体核对完整源 hash、所选 span hash、owned module hash（元数据提供时），并且所有 verbatim span 实际存在于相应 owned 文件。这里的“adapted”只认证其引用来源，不声称 adaptation 与原证明数学等价。

当轮 `TARGET-MAP.md`、`COMPILED-ENDPOINTS.md`、`overall-verification.json` 明确把新 weak chain 与未闭合的旧 strong natural-density/PNT targets 区分，source map 的文件引用与当前已交付文件相符。

**历史文档余项：** `lean/review-ledger-formal-coverage.json` 仍写 80 modules、2248 roots、`main_target_proved:false`，首条仍是“open unconditional endpoint”；`lean/PROVENANCE.md` 结尾也停留在 round3 的 strong-route 叙述。它们应明确标注为保留的历史 checkpoint，不能作为当前 round5 结论读取。当前 README/ROUND5/overall-verification 已给出新版状态；这里不是说旧 strong target 已被新链证明。

## 3. 当前 stored inventory 和作者声明覆盖

### 主工程

独立逐行核对真实 compiler traversal、`declaration-inventory.json`、`dependency-graph.json`：

| 项目 | 结果 |
|---|---:|
| 全部 owned stored inventory | 2926 个唯一名字 |
| theorem | 2477 |
| definition（全部） | 410 |
| inductive / constructor / recursor | 各 13 |
| safe logical roots | 2880 = 2477 theorem＋403 safe definition |
| root 与 inventory 的 kind 对应 | 全部一致 |

剩余 7 个 definition 是 Lean 生成的 `._unsafe_rec`，标记 `partial:true, unsafe:false`，被明确排除出“safe logical roots”。39 个 inductive/constructor/recursor 也不在 theorem/definition 根数量中。不能把 2880 误写成“所有 2926 个 stored declaration 都作为根”。当前每个 safe logical root 的 closure 都无 unsafe/partial/missing 依赖，因此这些被排除的 generated objects 没有进入安全证明依赖。

stored-body axiom 集合均为 `{propext, Classical.choice, Quot.sound}` 的子集。只有两个公开承认的 cached `collectAxioms` 差异：`Entry002.TimeLaw.ctorIdx`、`Entry002.TimeLaw.last`。本次未把该差异隐藏或改称“所有主根双收集完全一致”。

`completed-traversal-inputs.json` 中 134 个输入 hash 与实际 bytes 全部匹配，覆盖全部 129 份 owned source；所指 traversal log hash 也匹配。

### 历史外部工作负载

| workload | roots | owned inventory | root kind |
|---|---:|---:|---|
| ray | 16 | 4 | 9 theorem＋7 opaque |
| pnt | 6 | 18 | 6 theorem |
| density | 3 | 18 | 3 theorem |
| conductor | 246 | 246 | 194 theorem＋46 definition＋2×inductive/constructor/recursor |
| primeideal | 7 | 7 | 7 theorem |
| analytic | 113 | 112 | 107 theorem＋6 definition |

六组当前 exact names/inventory 均与 pinned ledger 一致、无重复；当前根的两种公理收集一致且仅标准公理，无 unsafe/partial/missing 依赖。这是既有 logs 的重新解析，不能称为本次重新编译。

### 当轮新增外部 weak workload

四个 exact owned module indices：

- `ArithmeticSupplyWeakFromDirichlet`
- `ArithmeticSupplyWeakMainReduction`
- `ArithmeticSupplyWeakMain`
- `Entry002.ArithmeticWeakPrincipalSupplyAssembly`

当前真实 inventory/rows 都是 7 个唯一 theorem，二者名称和 kind 相符。包括 generated `arithmeticSupply_weak_conductor_primeTo_of_gt._proof_1_1` 及 `conductorOrder.congr_simp`，没有只数五个手写 theorem 而漏算 generated root。

当前主根 `Entry002.arithmeticSupply_mainTarget_proved` 的完整 stored type 精确为 `Entry002.MainTarget`，kind 为 theorem，记录的 transitive declaration count 为 125368。其本次独立重新编译与数学含义由主审单列，不能由这里的字符串/log 检查替代。

这 7 个根与主 2880 根重叠两个：

- `Entry002.arithmeticSupply_weak_of_principal_split_witnesses`
- `Entry002.conductorOrder.congr_simp`

因此作者的 2885 个跨项目唯一根数字准确，而非 2887。

997 个实际 loaded historical external modules 无重复，且与 object-binding manifest 精确相等、恰好等于 995 个 CFT 模块加 `ArithmeticSupplyRayBridge`/`ArithmeticSupplyRayConductor`。新 weak log 的 hash、summary root-name hash、binding manifest hash 都匹配。4 个 proof source、5 个新 control/note、7 个 included evidence 全部可读取且 hash 相同；6 个输出 `.olean` 按交付声明不在归档中，未声称本次验证其二进制 bytes。

## 4. Round3 omission＋duplicate 缺口确已修复

关键修复位于 `lean/references/upstream/arithmetic-audit/git_provenance.py`：

- 21–38 行将三个 CFT 和一个 PNT 入口固定于代码，而不是从可删改 manifest 选取。
- 105–110 行严格将 module identity 映射为包内 canonical path。
- 113–140 行拒绝重复 package、重复 physical path、错误 endpoint，以及与独立 authenticated set 不精确相等的清单。
- 193–243 行先用固定 commit/tree 和确切 patch 认证源码，再从真实 imports 递归构造闭包；manifest 只在此后进行核对。
- `verify_sources()` 在任何 manifest-selected source 检查之前执行该认证闭包。

独立临时 fixture 中运行完整生产 `verify_sources()`：

1. 重现 round3 原攻击：把 Wiener 入口行替换为另一个 PNT 重复行，仍保留总行数 999，再向被遗漏 Wiener 源添加注释。**拒绝**：固定入口仍被读取，exact patch 反向重放失败。
2. 保留原 Wiener bytes，仅 omission＋duplicate。**拒绝**：`Duplicate external physical source path`。
3. 另测 external package 重复/遗漏、endpoint 更改、同数重复、单一遗漏、import graph 伪改和非法 module/path，全部拒绝。

因此此前可能只认证 998 个 unique sources 却打印 999 的实证缺口已封住；当前结果不是只靠外层 SHA-256 恰好正确。

## 5. 仍存在的 validator 硬化余项

### 5.1 历史 kind 检查仍不完整

`verify.py:51–67` 的 exact-root 验证比较名字，不比较完整 expected name→kind 映射。`verify_recursive()` 仍仅为 ray 七个 opaque 检查 kind。独立把 PNT 某 row 的 kind 从 theorem 改为 definition，名字/公理/闭包字段不改，**完整 `verify_recursive()` 接受**。这与 round3 报告的低级元数据余项相同。

当前真实 retained log 中 kinds 已另行核对正确；此余项不表示当前六组 theorem 被 definition 替换。

### 5.2 新 weak summarizer 有三个接受非法日志的案例

对隔离树中的真实 `round5_weak_summarize_audit.py` 运行完整 CLI，均保留最后 `EXIT=0`：

| 临时变体 | 生产 summarizer 结果 |
|---|---|
| 主根 kind 改 `definition`，type 改 `False`，inventory 保持原样 | 接受，打印 `PASS: 7 exact owned roots` |
| 从 inventory 和 rows 同时删 generated `_proof_1_1`，保留四个 module 与 required 五个手写名字 | 接受，打印 `PASS: 6 exact owned roots` |
| 从 loaded external module 列表删一个 CFT module，binding manifest 不变 | 接受，仍输出 passed summary |

原因：23–29 行只做 loaded set 的唯一性和 subset 检查；33–39 行只比较 inventory/rows 自报名字与四模块集合；41–59 行没有核对 row/inventory kind、主根完整 type，且 required names 仅为五个手写名字。脚本把 `closed_literal_MainTarget_mandatory:true` 和 `fresh_owned_compilation_and_stored_body_audit:true` 写入 summary，却没有独立建立这些事实。

**重要边界：这些控制不等于绕过完整 proof build/打包流程。** `ArithmeticSupplyWeakClosedCompilerAudit.lean` 的 producer 实际按四个 exact module indices 枚举所有 constants，并检查主根的真实 `Expr` 是 `mkConst Entry002.MainTarget`；producer 对全部根做 stored type/body traversal。`package_round5.py:50–57` 又要求主根是唯一 theorem 且完整 type 为 `Entry002.MainTarget`，并绑定当前 log/source/evidence hashes。因此上述 `definition/False` 变体会被完整 packaging 的主根检查挡住。此处准确结论是“单独 offline summarizer 不足以担保它输出的强断言”，不是当前证明造假或 Lean 不健全。

新 summarizer 对 duplicate inventory 和 duplicate roots 的两个独立负控确实拒绝。当前真实日志的 7 根/4模块/997输入已由本审计另外精确核对。

### 5.3 主工程 postprocessor 的静态余项

`lean/scripts/audit.py:64–66` 只要求 expected modules 是 log modules 的子集，并把 modules 转集合输出；80–81 行比较 root 名称集合，却不独立断言 rows/inventory 唯一，也不逐名验证 kind 一致。因此对不可信或未来手动编辑日志，重复及 kind 不一致并未由这一层完全防御。本报告对**当前**实际 raw log 和 derived JSON 已添加这些唯一性、精确集合、kind 对应检查，全部通过。此项是代码检查，不声称跑过完整 `audit.py` 的伪造编译结果测试。

建议最小修复：固定全部 required name→kind（以及闭合 endpoint 的 exact type）；current generation 完整 roots 和 modules 均使用唯一性＋精确集合；loaded external inputs 与已认证闭包/二进制绑定清单精确相等；historical documents 明确加 checkpoint 标签。元数据 hash 绑定应保留，但不能替代结构性检查。

## 6. 可复现证据和限制

本审计生产负控共 **27 项：23 项拒绝，4 项接受**（上述历史 kind 一项、新 weak summarizer 三项）。

- `provenance_round5_independent_checks.py`
- `PROVENANCE_ROUND5_INDEPENDENT_CHECKS.json` / `.log`
- `PROVENANCE_REUSE_SPAN_CHECKS.json`：69 个 source-span 对应结果
- `PROVENANCE_ROUND5_SOURCE_CLOSURE.json`：132 源辅助扫描、weak owned import closure 和 source/evidence bindings

执行使用 `PYTHONDONTWRITEBYTECODE=1` 与 `python3 -B`。会写 output summary 的生产调用只在 symlink-tree 的隔离目录运行，并在任何变更前 unlink 被选中文件；绝不穿透 symlink 写冻结源。临时 fixtures 已清理，前后 frozen tree hash 对比通过。没有运行会刷新原元数据的 `source_scan.py` CLI、`check_reuse.py` 或 packaging 脚本。

**可用于总判定的准确摘要：当前 round5 交付的归档完整性、既有原域冻结、source closure、unique owned inventory 和根清单覆盖通过；round3 external omission＋duplicate 漏洞已修复；若干 offline metadata validator 仍需硬化，但不能把这些余项误写成当前根缺失、原域缩窄或主定理 kernel 失败。**
