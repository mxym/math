"""Merge the former claim index into existing result entries; classify attempts.

Write a private reviewable candidate. Do not change proof sources or root.
"""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,subprocess

base=Path(__file__).resolve().parent
root=Path('/home/mxym/math-appt-multiscale-20261013')
out=base/'readme-organization-candidates'
catalog=out/'research-attempts-20261015'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def git(*a):return subprocess.check_output(['git','-C',str(root),*a])
if git('rev-parse','HEAD').decode().strip()!='c4e0d9e713ba349d376469231789bb7b36915b7d':raise RuntimeError('Unexpected README source base')
if (out/'README.md').exists():raise RuntimeError('Do not overwrite an existing organization candidate')
zh=(root/'README.md').read_text();en=(root/'README.en.md').read_text()
(out/'before').mkdir(exist_ok=False)
(out/'before'/'README.md').write_text(zh);(out/'before'/'README.en.md').write_text(en)
oldclaim=zh.split('## 已宣称解决的问题\n',1)[1].split('## 证明与复现\n',1)[0]
claimrows=[l for l in oldclaim.splitlines() if l.startswith('| ')][2:]
if len(claimrows)!=16:raise RuntimeError('Expected all16 original source/problem rows')
targets=[
 ('gaussian-four-cell-global-2026-10','所有 d≥3 的全局锐界与正四面体等号分类；包括 Heilman 2014 Conjecture 3 的三维命题'),
 ('erdos-similarity-growing-gaps-2026-10','对满足晚期环带填充条件的一类序列证明正测度仿射非普适性，含相邻比值趋零与间歇环带例子；完整 Erdős 猜想仍开放'),
 ('graph-state-mmi-forbidden-subgraph-2026-10','Fuentes–Keeler–Munizzi–Pollack Conjecture 1：正三重信息蕴含局部等价图有诱导 claw；另给无爪 vertex-minor 分类与七顶点连通阈值'),
 ('all-graph-chollet-2026-10','Pant–Singh Section 6 的强／self-Chollet 问题：任意有限简单无权图、全部主子矩阵，保留原图度数'),
 ('ecqc-pure-state-counterexamples','Iqbal Conjecture 3.1 的纯态问题（arXiv:2509.08286v2 §5）：素数维仅 p=2 普遍成立，奇素数均有满 Schmidt 秩反例，p=3 超出一比特；三维、五维比值最优；已有混合态反例另行归属'),
 ('gaussian-equal-cells-2026-10','Heilman 2019 Conjecture 1.16 的等质量子情形：所有 k≥2 的上界，d≥k−1 时最优值及全部等号，低维严格上界'),
 ('gaussian-fixed-mass-propeller-counterexample-2026-10','Heilman 2019 Conjecture 1.16 任意质量表述的反例：对每个 0<p<1/4 的指定四胞质量族，所有正四面体模型严格非最优；等质量情形保持原结论'),
 ('mutual-information-continuity-2026-10','Berta–Lami–Tomamichel arXiv:2408.15226v2 Eq. (106) 拟议界的实际 3×3 反例：任意小正距离、两侧边缘均变化；固定一侧边缘版本未解决'),
 ('ehrhart-real-rootedness','de Castro Conjecture 10.1（arXiv:2609.06096v1）：(132,213)-避免族全部 d≥3 的实根性，结合既有 d≤1000 定理'),
 ('bapat-q-permanent-counterexamples','Bapat 原区间 q-永久量单调性反例：指定复 Hermitian 有理矩阵及实对称整数反例存在定理'),
 ('entropy-polynomial-roots','Wakhare Conjecture 2 的“两内部根”断言反例：(11,10) 在 (0,1) 至少四个不同实根；另一熵不等式保持原状态'),
 (None,None),
 ('cyclotomic-unimodal-counterexample','Billey–Swanson Conjecture 48 反例：指定 216 次非恒定基本单峰 CGF 没有任何素数阶圆分因子；不声称次数最小'),
 ('cycle-chromatic-classification','Amdeberhan–Moll Conjecture 21／早期 13.1 的一般断言有 C17 反例；全部 C_n、n≥3 的无限对数凹性当且仅当 3≤n≤11'),
 ('q-permanent-halfline','da Fonseca 半轴扩展的实有理 4×4 反例在 q=49、50 间下降；书面结果另给最小阶为4及每个 t>1 的负导数族'),
 ('permanent-padding','Pan–Skandera–Wang Conjecture 9.3：由原作者 Theorem 8.18 经恒等补齐直接推出')]
lines=zh.splitlines(True);record=[]
pre_end=next(i for i,l in enumerate(lines) if l.startswith('## 已书面证明的问题'))
for i,(anchor,scope) in enumerate(targets):
 if anchor is None:
  row='| [全比值仿射几何序列避让](notes/continuum-power-avoidance/README.md) | Burgin–Goldberg–Keleti–MacMahon–Wang Question 1（arXiv:2210.09284v1）的全比值问题给出否定回答；不声称此前仍未解决 | [完整 Lean 几何避让](formalizations/geometric-avoidance/README.md)；限定原版本命题 | — |\n'
  lines.insert(pre_end,row);pre_end+=1
 else:
  hits=[j for j,l in enumerate(lines[:pre_end]) if l.startswith('| ') and anchor in l]
  if len(hits)!=1:raise RuntimeError('Ambiguous preprint anchor '+anchor)
  j=hits[0];cells=lines[j].rstrip('\n').split(' | ')
  if len(cells)!=4:raise RuntimeError('Unexpected preprint column count')
  cells[1]=scope
  if anchor=='q-permanent-halfline':cells[2]='指定反例完整 Lean；最小阶和全 t>1 实参族为书面证明'
  # Preserve every former proof URL, placing a missing one into its
  # corresponding result row rather than keeping a separate claims table.
  for label,link in re.findall(r'\[([^]]+)\]\(([^)]+)\)',claimrows[i]):
   if not any(link in l for l in lines[:pre_end]):cells[2]+='；['+label+']('+link+')'
  row=' | '.join(cells)+'\n';lines[j]=row
 record.append({'original_claim_row':claimrows[i],'merged_into_preprint':anchor or 'geometric-avoidance-versioned-question',
                'new_row':row.rstrip('\n'),'proof_status_not_expanded':True})
zh=''.join(lines)
start=zh.index('## 已宣称解决的问题\n');end=zh.index('## 证明与复现\n',start)
zh=zh[:start]+'''## 尝试过的问题

按领域记录已有探索与阶段结果；详细目标、阅读范围和保全记录见
[分类尝试目录](research/research-attempts-20261015/README.md)。已完成证明的
精确成果列在上面的预印本与书面证明栏。

| 领域 | 尝试过的问题 | 阶段结果与入口 |
| --- | --- | --- |
| 高斯分析与概率 | Wishart 行列式乘积猜想；一般高斯多项式 U 猜想 | 完整目标未闭合；[阶段记录](research/research-attempts-20261015/README.md#高斯分析与概率) |
| 永久量、矩阵与设计 | 一般复 PSD Chollet；Ryser 设计；Lih–Wang；Minc 第六猜想；Ryser rank-six | 保留有限控制与路线分析；[分类记录](research/research-attempts-20261015/README.md#永久量矩阵不等式与设计) |
| 极值图论与离散几何 | Caccetta–Häggkvist；八维 Borsuk 的平衡切片路线 | 原目标仍开放；[尝试范围](research/research-attempts-20261015/README.md#极值图论与离散几何) |
| 理论计算机科学、学习与布尔分析 | 确定性 log-rank；强有标号样本压缩；完整 FEI | 完整猜想未闭合；Han Q3.1 辅助反例另列已审成果；[阶段记录](research/research-attempts-20261015/README.md#理论计算机科学学习与布尔分析) |
| 量子信息与理论物理 | NPT bound entanglement；全维 SIC；去极化容量阈值；Quantum PCP | NPT／容量／PCP 未闭合；SIC 因已有完整主张而结束该阶段；[状态与实际阅读范围](research/research-attempts-20261015/README.md#量子信息与理论物理) |
| 文献筛查与去重 | Sidorenko；Courtade–Kumar；有限能量 EPnI；Unique Games | 按已有完整主张及实际读限保留筛查记录；[候选筛查](research/research-attempts-20261015/README.md#文献筛查后未继续的候选) |

'''+zh[end:]
zh=zh.replace('[已宣称解决的问题](#已宣称解决的问题)','[尝试过的问题](#尝试过的问题)')
en=en.replace('[Claimed results](#claimed-results)','[Problems explored](#problems-explored)')
st=en.index('## Claimed results\n');ed=en.index('## Proof and reproduction\n',st)
en=en[:st]+'''## Problems explored

Research attempts are grouped by field in the [stage catalog](research/research-attempts-20261015/README.md).
Completed proofs retain their precise scopes in the preprint and written-proof
tables above. Stage records preserve their original outcomes and do not acquire
proof status through inclusion in this directory.

| Field | Problems explored | Outcome and records |
| --- | --- | --- |
| Gaussian analysis and probability | Real-degree Wishart determinant products; the general Gaussian polynomial U conjecture | Full targets remain open here; [records](research/research-attempts-20261015/README.md#高斯分析与概率) |
| Permanents, matrices and designs | General complex PSD Chollet; Ryser designs; Lih–Wang; Minc sixth; Ryser rank-six | Bounded controls and route analyses; [records](research/research-attempts-20261015/README.md#永久量矩阵不等式与设计) |
| Extremal graphs and discrete geometry | Caccetta–Häggkvist; a balanced-slice route to eight-dimensional Borsuk | Original problems unresolved; [scope](research/research-attempts-20261015/README.md#极值图论与离散几何) |
| Theoretical CS, learning and Boolean analysis | Deterministic log-rank; strong labeled sample compression; full FEI | Full conjectures unresolved; the reviewed Han auxiliary counterexample is separate; [records](research/research-attempts-20261015/README.md#理论计算机科学学习与布尔分析) |
| Quantum information and theoretical physics | NPT bound entanglement; all-dimensional SIC; depolarizing capacity threshold; Quantum PCP | NPT/capacity/PCP unresolved; SIC stage closed upon an existing full-target claim; [records and read limits](research/research-attempts-20261015/README.md#量子信息与理论物理) |
| Literature screening | Sidorenko; Courtade–Kumar; finite-energy EPnI; Unique Games | Existing full claims screened with explicit reading limits; [records](research/research-attempts-20261015/README.md#文献筛查后未继续的候选) |

'''+en[ed:]
# Move the examples formerly isolated under 'Claimed results' into their
# actual existing manuscript rows; add the missing formalized entries.
en=en.replace('Global sharp bound and equality classification for four equal Gaussian cells',
 'Global sharp bound and equality classification for four equal Gaussian cells, including Heilman2014 Conjecture3')
en=en.replace('Strong inequality for every finite simple unweighted graph and every principal submatrix',
 'Pant–Singh Section6 strong/self-Chollet inequality for every finite simple unweighted graph and every principal submatrix')
en=en.replace('The pure-state assertion holds for prime dimension iff (p=2); all odd primes have full-rank counterexamples',
 'Iqbal Conjecture3.1 pure-state problem: true in prime dimension iff p=2; every odd prime has a full-rank counterexample, with a one-bit qutrit excess; prior mixed-state examples credited')
en=en.replace('Sharp upper bound and equality classification for all equal cell counts',
 'Heilman2019 Conjecture1.16 equal-mass case: every k>=2, equality for d>=k-1 and strict upper bounds below that dimension')
en=en.replace('Strict non-regular improvement for every (0<p<1/4) in the stated four-cell mass family',
 'Counterexample to the arbitrary-mass Heilman2019 Conjecture1.16: every 0<p<1/4 in the stated four-cell family; equal masses retain their theorem')
en=en.replace('A ternary counterexample at every sufficiently small positive distance',
 'Berta–Lami–Tomamichel arXiv:2408.15226v2 Eq.(106): a ternary counterexample at every small positive distance with both marginals changing; fixed-one-marginal question remains open')
extra='''| [Wakhare entropy-polynomial roots](preprints/lean-certified-2026-10/entropy-polynomial-roots/README.md) | Conjecture2's two-interior-root assertion fails at (11,10), with at least four distinct roots; the separate entropy inequality is unchanged | Complete Lean | [23253028](https://doi.org/10.5281/zenodo.23253028) |
| [Affine geometric progression avoidance](notes/continuum-power-avoidance/README.md) | Negative answer to Burgin–Goldberg–Keleti–MacMahon–Wang Question1 as stated in arXiv:2210.09284v1; no claim it was previously open | [Complete Lean geometric avoidance](formalizations/geometric-avoidance/README.md) | — |
| [Cyclotomic unimodality counterexample](preprints/lean-certified-2026-10/cyclotomic-unimodal-counterexample/README.md) | Billey–Swanson Conjecture48: the specified nonconstant unimodal CGF has no prime-order cyclotomic factor; degree216, no minimality claim | Complete Lean | [23249757](https://doi.org/10.5281/zenodo.23249757) |
| [Cycle chromatic classification](preprints/lean-certified-2026-10/cycle-chromatic-classification/README.md) | C17 refutes the general Amdeberhan–Moll assertion; all cycles C_n, n>=3, are infinitely log-concave iff3<=n<=11 | Complete Lean | [23249722](https://doi.org/10.5281/zenodo.23249722) |
| [Half-line q-permanent counterexample](preprints/lean-certified-2026-10/q-permanent-halfline/README.md) | da Fonseca extension fails for a real rational4x4 matrix between q=49 and50; written results give minimal order4 and a negative-derivative family for every t>1 | Specified counterexample fully Lean; remaining family/minimality statements are written proofs | [23249758](https://doi.org/10.5281/zenodo.23249758) |
'''
anchor='The complete catalog, including smaller formalized results and research notes, is in '
pos=en.index(anchor)
en=en[:pos]+extra+'\n'+en[pos:]
for name,text in [('README.md',zh),('README.en.md',en)]:
 if '## 已宣称解决的问题' in text or '## Claimed results' in text:raise RuntimeError('Old duplicate claim section remains')
 (out/name).write_text(text)
# Retain the three owned terminal summaries, without external raw papers,
# unreviewed proofs being promoted, or unrelated branch ranges being merged.
terminal=[
 ('b099d0cc3241c166ed2783a1eadc2c01bbf41c90','research/breadth-tcs-20261015/phase-2/FULL_FEI_STAGE_RESULT.md','tcs-fei.md'),
 ('531af43d55e0ccafe256af7958cc1e664fb3bfda','research/breadth-quantum-20261015/phase-2/FINAL_STAGE_REPORT.md','quantum-sic.md'),
 ('f232bb2702ebbd4ce45af03533651e454aac6eac','research/breadth-quantum-20261015/phase-2/next-target-depolarizing/STAGE.json','quantum-depolarizing.json')]
(catalog/'stage-summaries').mkdir(exist_ok=False)
ledger=[]
for commit,rel,name in terminal:
 blob=git('show',commit+':'+rel);dest=catalog/'stage-summaries'/name;dest.write_bytes(blob)
 ledger.append({'source_commit':commit,'source_repository_path':rel,'public_copy':'stage-summaries/'+name,
                'sha256':sha(dest),'bytes':len(blob),'kind':'frozen author stage outcome, not independently passed mathematical proof'})
(catalog/'STAGE_SOURCES.json').write_text(json.dumps({'utc':datetime.now(timezone.utc).isoformat(),
 'kind':'research-stage catalog, source/status verification only','summaries':ledger,
 'external_raw_papers_published':False,'new_mathematical_proof_claim':False,'new_Lean':False},indent=2)+'\n')
(catalog/'PROJECT_KIND.json').write_text(json.dumps({'kind':'research-attempt catalog','requires':'source/status/index review only; no mathematical promotion'},indent=2)+'\n')
(out/'CLAIM_MERGE_MAP.json').write_text(json.dumps({'source_base':git('rev-parse','HEAD').decode().strip(),
 'kind':'source/scope preservation map for a user-requested README reorganization, not a new mathematical review',
 'all_original_claim_rows':record,'index_bindings':{name:{'before_sha256':sha(root/name),'after_sha256':sha(out/name)} for name in ['README.md','README.en.md']}},indent=2)+'\n')
print(json.dumps({'status':'PRIVATE_README_CANDIDATE_PREPARED','merged_problem_rows':len(record),
                  'catalog_fields':6,'source_base':git('rev-parse','HEAD').decode().strip(),
                  'root_edited':False,'attempt_catalog_source_summaries':len(ledger)}))
