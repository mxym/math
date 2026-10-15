from pathlib import Path
import hashlib,json,datetime
R=Path(__file__).resolve().parent;S=R/'owner-snapshot/zero-order-all-path-losses-20261015'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
dump=lambda p,o:p.write_text(json.dumps(o,indent=2,ensure_ascii=False)+'\n')
utc=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
inp=json.loads((R/'INPUT_VERIFICATION.json').read_text())
control=json.loads((R/'runs/20261015T143504.482566Z/RESULT.json').read_text())
assert inp['status']==control['status']=='PASS'
ledger=[]
for x in inp['listed_files']:
    rel=x['path']
    if '/UNIFORM_PROFILE.md' in rel or '/SPECTRAL_PROFILE.md' in rel:
        mode='Prior complete scientific reading reused after literal byte equality to private S5 copy; no S5 theorem used'
    elif rel.startswith('control-runs/'):
        mode='Source/result literal equality checked; stored result fully read; intended six author trace assertions inspected; no author execution'
    else:mode='Complete new or credited source/record read; author programs not executed'
    ledger.append(dict(x,read_scope=mode))
ledger.append({'path':'AUTHOR_V1_MANIFEST.json','sha256':sha(S/'AUTHOR_V1_MANIFEST.json'),
               'read_scope':'Complete manifest; 27 listed plus manifest verified; outside owner receipt is absent and not part of snapshot'})
dump(R/'READ_LEDGER.json',{'utc':utc(),'read_type':'Independent ordinary internal mathematical read','files':ledger,
 'old_mathematical_inputs':'Z1/Z4/Z7/Z12-Z14, actual shifted-star and Schmidt sufficient construction; explicitly credited ordinary results',
 'not_automatic_dependencies':['S5','S6','X','phase4 geometry','old Lean receipts'],
 'external_primary_search':'No new search by reviewer; author bounded screen read only; no priority certificate',
 'author_controls':'Full code and stored result read/source-bound, not executed; original UTC retained'})
review={'status':'PASS','decision':'PASS','utc':utc(),
 'review_kind':'Independent internal AI-agent ordinary full mathematical reading, not external human/Lean/priority certification',
 'source':{'paper_sha256':sha(S/'PAPER.md'),'paper_bytes':(S/'PAPER.md').stat().st_size,
           'manifest_sha256':sha(S/'AUTHOR_V1_MANIFEST.json'),'owner_zip_sha256':sha(R/'owner.zip')},
 'decisions':{'exact_losses':'PASS: finite physical deflation, coupled least-power inequality and three nonnegative terms',
              'Theorem_A':'PASS: uniform relative all-state criterion for every shrinking positive-order interval and all integer n>=m',
              'window_consequences':'PASS: finite positive tie plus collapsing/oscillating corners, without false Q/gamma condition at c=0',
              'continuum':'PASS: every p in[0,1] realized by actual all-unitary APPT full-rank family at exact canonical moving tie',
              'rank_endpoint':'PASS: separately defined alpha=0 loss and mixed nonnegative-order paths'},
 'domain':{'matrices':'Actual complex PSD trace-one density, PPT after every global unitary',
           'dimensions':'Integers 2<=m<=n, m->infinity, every n>=m including aspect oscillation',
           'orders':'For every A_m>0 tending to zero, all 0<alpha<=A_m; separate exact alpha=0 extension',
           'state_uniformity':True,'alpha_log_m_or_alpha_gamma_limit_required':False},
 'mathematical_checks':['Z1 value and Z14 state identity genuinely uniform to tiny positive alpha',
                        'Exact t^2Q-8 positive part, both deflation branches',
                        'Actual u^alpha>=min(1,u) coupling and each loss sign',
                        'Wt/W=1+O(1/m), uniform over state, alpha and n',
                        'All finite and degenerating phase-gap consequences including ties/alternation',
                        'Every s in[0,1] Schmidt SOS, true integer rank and actual pivot at canonical tie',
                        'Exact half-rank one-hole variance identity, all p endpoints included',
                        'Singular-spectrum ordering/trace proof and independent rank indicator'],
 'source_findings':[],
 'read_scope':{'new_paper':'Complete','four_old_scientific_texts_reread_complete':['SMALL_ORDER_BOUNDARY','ENTROPY_ASYMPTOTIC','SHARP_ASPECT_RATIO','SUBUNIT_RIGIDITY'],
               'two_byte_equal_prior_full_reads':['UNIFORM_PROFILE','SPECTRAL_PROFILE'],
               'old_review_records':'Both full JSON records read','author_code':'Full read, not executed'},
 'independent_controls':{'run':'runs/20261015T143504.482566Z','status':'PASS','source_sha256':control['source_sha256'],
                         'counts':control['counts'],'actual_rejected_wrong_variants':7,
                         'runtime':control['runtime'],'maximum_mp_dps':3244,
                         'unexpected_mathematical_control_failures':0,
                         'scope':'Finite algebra/physical-family diagnostics, no universal feasible-set numerical certification'},
 'retained_metadata_failure':{'directory':'metadata-failure-1','tool_chunk_id':'be33f9','returncode':1,
                              'diagnosis':'Reviewer assumed outside-ZIP OWNER_V1_RECEIPT was inside ZIP; corrected set contains only manifest beyond 27 listed files',
                              'source_or_math_failure':False,'original_script_and_trace_retained':True},
 'author_controls':{'executed_by_reviewer':False,'stored_result_read':True,'source_hash_verified':True,
                    'original_run':'20261015T141023.802089Z','original_utc':'2026-10-15T14:10:23.842906+00:00'},
 'not_claimed':['New entropy value','Complete all-order spectral rigidity','Every empirical body law','Exact finite optimizer','APPT=ASEP',
                'Lean extension','Worldwide novelty','New major-problem count','Future publication metadata/layout/transport'],
 'author_root_gaussian_files_modified':False,'lean_executed_or_expanded':False,
 'subagents_spawned':False,'git_mutation':False,'publication_or_external_messages':False}
dump(R/'REVIEW.json',review)
rows=[]
for p in sorted(R.rglob('*')):
    if p.is_file() and p.name!='REPORT_BINDINGS.json':
        rows.append({'path':p.relative_to(R).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)})
dump(R/'REPORT_BINDINGS.json',{'status':'PASS','decision':'PASS','utc':utc(),
 'scope':'Exact private completed ordinary review files; no future transport or metadata certification',
 'excluded':['REPORT_BINDINGS.json self-reference'],'files':rows})
print(json.dumps({name:{'bytes':(R/name).stat().st_size,'sha256':sha(R/name)}
                  for name in ['REVIEW.md','REVIEW.json','REPORT_BINDINGS.json']},indent=2))
