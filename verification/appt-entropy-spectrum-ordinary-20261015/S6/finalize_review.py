from pathlib import Path
import hashlib,json,datetime
R=Path(__file__).resolve().parent
S=R/'owner-snapshot/worktree/research/breadth-tcs-20261015/phase-6-growing-peak-rigidity'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
utc=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
dump=lambda p,x:p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
old=R/'runs/20261015T142447.829759Z'
raw='''Traceback (most recent call last):
  File "/mnt/d/math/tmp/research-resume-20261015/independent-growing-peak-rigidity-review-20261015/independent_checks.py", line 194, in <module>
    else: main()
  File "/mnt/d/math/tmp/research-resume-20261015/independent-growing-peak-rigidity-review-20261015/independent_checks.py", line 102, in main
    assert sy.expand((2-e+b)**2-(2-e)**2)==b*(4-2*e+b)
AssertionError
'''
(old/'ACTUAL_TOOL_STDERR.txt').write_text(raw)
dump(old/'FAILURE_RECORDED_AFTER_RETURN.json',{
 'status':'FAIL','returncode':1,'tool_chunk_id':'892ca5','recorded_utc':utc(),
 'run_utc_source':'Directory name created by original checker before assertion',
 'run_utc':'2026-10-15T14:24:47.829759+00:00',
 'note':'Original checker exited before writing RESULT. This separate record preserves the actual returned failure, not a claimed original RESULT.',
 'source_sha256':sha(old/'independent_checks.py'),'actual_tool_stderr':'ACTUAL_TOOL_STDERR.txt',
 'diagnosis':'Sympy structural equality after expanding one side only; corrected polynomial identity by expand(left-right)==0',
 'author_source_finding':False})
f=json.loads((R/'FIRST_REVIEWER_CONTROL_FAILURE.json').read_text())
f['original_stderr_field_is']='Normalized excerpt; complete exact tool-returned traceback separately in first run ACTUAL_TOOL_STDERR.txt'
f['first_run']='runs/20261015T142447.829759Z'
f['first_source_sha256']=sha(old/'independent_checks.py')
dump(R/'FIRST_REVIEWER_CONTROL_FAILURE.json',f)
inp=json.loads((R/'INPUT_VERIFICATION.json').read_text())
run=json.loads((R/'runs/20261015T142527.968604Z/RESULT.json').read_text())
assert run['status']=='PASS'
read=[]
for x in inp['files']:
    mode='Complete new text/code/record read; author programs not executed'
    if x['path'].startswith('credited-inputs/'):
        mode='Prior complete scientific-text read reused after literal byte equality; G Sections 1-3 through G22 reread for this proof'
    read.append({'path':x['path'],'sha256':x['sha256'],'bytes':x['bytes'],'read_scope':mode})
read.append({'path':'AUTHOR_V1_MANIFEST.json','sha256':sha(S/'AUTHOR_V1_MANIFEST.json'),'read_scope':'Complete manifest; all listed bytes and absence of extras independently checked'})
dump(R/'READ_LEDGER.json',{'utc':utc(),'scope':'Actual internal reading; not a new source priority or Lean audit','files':read,
 'new_primary_literature_search':False,'author_search_record':'Read only; bounded query absence not priority certificate',
 'author_controls':'Complete source and stored 21-case result read/hash-verified; no execution',
 'dependency_boundary':'Only G physical input used in S6 proof, not S5/phase4 result'})
review={'status':'PASS','decision':'PASS','utc':utc(),
 'review_type':'Independent internal AI-agent ordinary full mathematical read, not external human/Lean/priority review',
 'source':{'paper_sha256':sha(S/'PAPER.md'),'paper_bytes':(S/'PAPER.md').stat().st_size,
           'owner_zip_sha256':sha(R/'owner.zip'),'manifest_sha256':sha(S/'AUTHOR_V1_MANIFEST.json')},
 'domain':{'fixed_constant':'Every fixed finite C>0','matrix':'Original complex PSD trace-one, PPT after every global unitary',
           'integers':'Every 2<=m<=n; m->infinity','orders':'Real alpha->infinity, alpha<=Cm eventually',
           'window':'chi=alpha log[3D/(D+2)]-logD -> +infinity',
           'oscillation':'All n/m and bounded alpha/m oscillations permitted'},
 'decisions':{'A':'PASS: uniform each-actual-state peak profile and both moment equivalences',
              'B':'PASS: relative entropy iff h/chi->0, with actual peak necessity before logging',
              'C':'PASS: full actual tail flatness, eventual full rank, second-peak power and entire tail moment decay'},
 'source_findings':[],
 'read_scope':{'new_paper':'Complete','new_metadata_and_author_scripts':'Complete, no author execution',
               'credited_scientific_texts':12,'method':'Byte-equal reuse of earlier complete old-input scientific reading; G relevant sections reread',
               'not_reused':'No inference of S6 from S5 or phase4 PASS'},
 'proof_checks':['Uniform K_C independent of n and state','Bounded exceptional square mass rather than cardinality',
                 'Exact trace-centered real powers at zero eigenvalues','Actual all-unitary APPT spike lower bound',
                 'Entropy forces actual peak before log estimate','State-relative bounded log error for chi/alpha->0',
                 'All growing tail powers, not just second peak','Physical star budget implies all nonpeak eigenvalues flatten',
                 'Actual integer exponential-ceiling and reduced-spike counterexamples'],
 'independent_control':{'run':'runs/20261015T142527.968604Z','status':'PASS','source_sha256':run['source_sha256'],
                        'counts':run['counts'],'actual_expected_false_variant_failures':7,
                        'unexpected_first_run_failure':'runs/20261015T142447.829759Z; Sympy structural comparison; original source and trace retained',
                        'scope':'Finite diagnostics, not proof of universal feasible set'},
 'author_control':{'source_read':True,'stored_result_read':True,'executed_by_this_reviewer':False,'finite_cases':21,
                   'original_utc':'2026-10-15T13:34:37.291155+00:00'},
 'not_covered':['alpha/m->infinity','fixed m','bounded alpha','alpha->0','finite chi','exact finite optimizer',
                'all-diverging-order synthesis','future metadata or transport','new Lean/audit scope','historical priority'],
 'author_root_source_mutations':False,'lean_run':False,'subagents_spawned':False,'git_mutations':False}
dump(R/'REVIEW.json',review)
rows=[]
for p in sorted(R.rglob('*')):
    if p.is_file() and p.name!='REPORT_BINDINGS.json':
        rows.append({'path':p.relative_to(R).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)})
dump(R/'REPORT_BINDINGS.json',{'status':'PASS','decision':'PASS','utc':utc(),'scope':'Files of this private completed review; no future publication transport claim',
 'excluded':['REPORT_BINDINGS.json (self-reference)'],'files':rows})
print(json.dumps({name:{'bytes':(R/name).stat().st_size,'sha256':sha(R/name)}
                  for name in ['REVIEW.md','REVIEW.json','REPORT_BINDINGS.json']},indent=2))
