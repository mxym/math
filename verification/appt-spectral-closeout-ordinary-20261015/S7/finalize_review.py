from pathlib import Path
import hashlib,json,datetime
R=Path(__file__).resolve().parent
S=R/'owner-snapshot/worktree/research/breadth-tcs-20261015/phase-7-rectangular-bulk-rigidity'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
dump=lambda p,x:p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
utc=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
inp=json.loads((R/'INPUT_VERIFICATION.json').read_text())
run=json.loads((R/'runs/20261015T144839.352065Z/RESULT.json').read_text())
assert inp['status']==run['status']=='PASS'
read=[]
for x in inp['files']:
    if x['path'].startswith('credited-inputs/'):
        scope='Byte-identical prior complete scientific-text read reused; G construction Section4 and bounded-aspect Section5 reread here; no S5/S6 new theorem used'
    else:scope='Complete new source/record read; author programs read only, not executed'
    read.append(dict(x,read_scope=scope))
read.append({'path':'AUTHOR_V1_MANIFEST.json','sha256':sha(S/'AUTHOR_V1_MANIFEST.json'),
             'read_scope':'Complete; all 17 listed files and manifest itself independently byte-verified'})
dump(R/'READ_LEDGER.json',{'utc':utc(),'scope':'Actual ordinary internal reading','files':read,
 'old_physical_input':'G7-G15 definitions and estimates; complete prior text reading retained and exact bytes compared',
 'not_dependencies':['S5 new results','S6 new results','zero-order all-path losses','phase4 geometry','old Lean receipts'],
 'new_external_search_or_fullpaper_read':False,'author_primary_scope':'Read bounded search record only, no priority certification',
 'author_controls':'Complete source and 12-case stored result read/hash-verified, never executed'})
review={'status':'PASS','decision':'PASS','utc':utc(),
 'review_type':'Independent internal AI-agent ordinary complete mathematical read, not external human/Lean/priority certification',
 'source':{'paper_sha256':sha(S/'PAPER.md'),'paper_bytes':(S/'PAPER.md').stat().st_size,
           'manifest_sha256':sha(S/'AUTHOR_V1_MANIFEST.json'),'owner_zip_sha256':sha(R/'owner.zip')},
 'decisions':{'uniform_state_and_value_profile':'PASS: actual e/scale and E/scale with O_Aepsilon, including arbitrarily tiny positive alpha and continuousalpha1',
              'actual_bulk_and_W2_iff':'PASS: q->1 iff actual L->2,theta->1/2,J->0 iff full empirical W2->fair+-1',
              'fourth_root_stability':'PASS: all-state W2<=C_A(d+epsilon)^(1/4), true mean and exceptional second moment retained',
              'optimal_exponent':'PASS: actual integer-rank APPT sharpness, W2^2~4/l, d~4/l^2 via joint O(l^-4) error',
              'rank_and_scope_examples':'PASS: eventual full rank, persistent peak compatibility and actual counterexample outside alpha gamma condition'},
 'domain':{'matrices':'Every original complex PSD trace-one density, PPT after every global unitary',
           'dimensions':'All integer2<=m<=n, m->infinity','orders':'Every fixed finite A>0, all real0<alpha<=A, alpha gamma->infinity',
           'oscillation':'No limit required of alpha, alpha logm or aspect; crossings1/2,1,2 retained',
           'error':'epsilon=1/m+1/(alpha gamma), constants/common thresholds depending only on A'},
 'proof_checks':['Endpoint kernel1/alpha and bounded-order middle Taylor remainder',
                 'Exact trace moment and uniform removable entropy order1 logarithm',
                 'Actual projection sufficiency for every global unitary and integer half-rank lower bound',
                 'Exact actual middle N, normalized pivot, mean term and spreadJ',
                 'Endpoint stochastic rounding and correct cost of unequal weights',
                 'Whole-spectrum exceptional quadratic mass replacement',
                 'W2 converse uses true second moments',
                 'Exact integer-rank sharpness law and monotone coupling cost',
                 'Uniform O(l^-4) error smaller than l^-2 gap',
                 'True singular-state exclusion and actual protected peak example'],
 'source_findings':[],
 'read_scope':{'new_paper':'Complete','new_metadata_author_code_results':'Complete; code not executed',
               'six_old_scientific_sources':'Prior complete reads reused only after literal equality; G relevant construction reread',
               'new_external_priority_screen':False},
 'independent_controls':{'run':'runs/20261015T144839.352065Z','status':'PASS','source_sha256':run['source_sha256'],
                         'counts':run['counts'],'actual_expected_wrong_variant_failures':7,
                         'unexpected_failures':0,'runtime':run['runtime'],
                         'scope':'Finite exact physical geometry/transport and real-order diagnostics; not a global optimizer or universal numerical certificate'},
 'author_controls':{'read':True,'executed_by_reviewer':False,'finite_cases':12,
                    'original_utc':'2026-10-15T13:49:49.966059+00:00','source_hash_verified':True},
 'not_covered':['Bounded alpha gamma as alpha->0','Unbounded alpha','Fixed m','Exact finite extrema','Eigenvector rigidity',
                'Complete all-order/all-aspect synthesis','Later S8/S9 work','Future publication metadata/transport','New Lean scope','Worldwide priority'],
 'author_root_gaussian_files_modified':False,'lean_executed_or_expanded':False,
 'git_mutation':False,'subagents_spawned':False,'publication_or_external_messages':False}
dump(R/'REVIEW.json',review)
rows=[]
for p in sorted(R.rglob('*')):
    if p.is_file() and p.name!='REPORT_BINDINGS.json':
        rows.append({'path':p.relative_to(R).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)})
dump(R/'REPORT_BINDINGS.json',{'status':'PASS','decision':'PASS','utc':utc(),
 'scope':'Exact private completed S7 review files; excludes future publication metadata and transport',
 'excluded':['REPORT_BINDINGS.json self-reference'],'files':rows})
for x in rows:
    p=R/x['path'];assert p.stat().st_size==x['bytes'] and sha(p)==x['sha256'],x['path']
print(json.dumps({'reports':{name:{'bytes':(R/name).stat().st_size,'sha256':sha(R/name)}
                  for name in ['REVIEW.md','REVIEW.json','REPORT_BINDINGS.json']},'bound_files_read_back':len(rows)},indent=2))
