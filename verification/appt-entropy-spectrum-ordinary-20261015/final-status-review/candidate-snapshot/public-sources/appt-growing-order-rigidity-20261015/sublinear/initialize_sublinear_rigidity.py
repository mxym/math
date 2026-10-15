from pathlib import Path
import datetime as dt
import hashlib
import json
import shutil
import subprocess

repo=Path('/home/mxym/math-breadth-tcs-20261015')
root=Path('/home/mxym/math-appt-multiscale-20261013')
folder=repo/'research/breadth-tcs-20261015/phase-5-sublinear-rigidity'
aux=Path('/mnt/d/math/tmp/breadth-tcs-20261015/phase-5-sublinear-rigidity')
folder.mkdir(parents=True,exist_ok=True);aux.mkdir(parents=True,exist_ok=True)
now=dt.datetime.now(dt.timezone.utc)
head='1c76bb8dd03bb622e8ed1eabbe88e8abc5b3e59f'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
names=['research/appt-growing-renyi/PAPER.md','research/appt-growing-renyi/UNIFORM_PROFILE.md',
 'research/appt-growing-renyi/SPECTRAL_PROFILE.md','research/appt-growing-renyi/LINEAR_ORDER_VARIATIONAL.md',
 'research/appt-growing-renyi/ALL_ORDER_VARIATIONAL.md','research/appt-growing-renyi/MACROSCOPIC_HIGH_ORDER.md',
 'research/appt-growing-renyi/SMALL_ORDER_BOUNDARY.md','research/appt-linear-critical-rigidity-20261015/PAPER.md',
 'research/appt-ultralinear-spectrum-20261014/FAST_ORDER_SPECTRA.md',
 'research/appt-all-positive-axis-20261014/PAPER.md','research/appt-all-order-exact-20261014/PAPER.md',
 'research/appt-zero-order-transition-20261014/PAPER.md','research/appt-growing-renyi-order-20261015/PAPER.md',
 'research/appt-finite-entropy-bounds-20261015/PAPER.md','research/appt-multilevel-counterexample/PHASE_RIGIDITY.md']
rows=[]
for name in names:
    p=root/name
    data=subprocess.check_output(['git','-C',str(root),'show',head+':'+name])
    assert p.read_bytes()==data,name
    dest=folder/'credited-inputs'/name;dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_bytes(data);dest.chmod(0o444)
    rows.append({'path':name,'sha256':sha(dest),'bytes':len(data),'commit':head,
      'actual_read_scope':'Complete scientific manuscript read in this role; all-order-exact aggregate truncation recovered by first170-line read; prior full L/V/S reads retained',
      'role':'Credited physical/value proof or local collision/range check; not a new theorem or expanded independent/Lean audit'})
dump(folder/'SOURCE_INPUTS.json',{'created_utc':now.isoformat(),'root_capture_commit':head,'inputs':rows,
 'new_target':'All actual APPT nearoptimizers at growing sublinear positive order, every aspect ratio',
 'not_dependencies':['Four still-being-reviewed phase4 scalar manuscripts','Any new Lean audit','Restricted spectral candidate model'],
 'publication_status':'Author research, no submission/push/index change'})
dump(folder/'TARGET.json',{'created_utc':now.isoformat(),
 'domain':'Every sequence of original complex PSD trace-one densities APPT under every global unitary, integers2<=m<=n,m->infinity,real alpha->infinity,alpha/m->0',
 'objective':'Necessary and sufficient actual spectral criteria at first-nonzero moment-excess and relative entropy-deficit scales; arbitrary peak/bulk ratio and oscillations',
 'uniform_inputs':'G1 opt moment-excess value and G7-G19 physical estimates, plus actual L7 width/peak coupling and S middle definitions',
 'candidate_criterion':'wp min(1,h)+wb min(1,db)->0 for sharp moment excess; replace h by h/(1+chi_plus) for entropy',
 'actual_defects':'h=alpha log(u_D/y1), db=(2-L)+abs(theta-1/2)+J; U=u_D^alpha,V=alpha(alpha-1)gamma/2,wp=U/(U+V),wb=V/(U+V),chi=log(U/D)',
 'must_prove':['Uniform identity for EACH actual state','Weighted variance overshoot control','Explicit J equivalence on nonvanishing bulk weight',
   'chi->+infinity necessity of a physical peak','All extreme ratios and oscillatory crossings','Actual attainment and no substitute finite candidate'],
 'clock_policy':'Continuous APPT depth; no breadth stage budget or two-hour switching clock',
 'status':'Candidate complete route being written, not independently reviewed, no new-major count'})
dump(folder/'PRIMARY_SCREEN.json',{'searched_utc':'2026-10-15T13:01:29Z',
 'queries':['\"absolutely PPT\" \"sublinear\" entropy','\"absolute PPT\" \"Rényi\" spectral rigidity','\"absolutely PPT\" \"growing\" \"order\"'],
 'domains':['arxiv.org'],'result':'No results returned for those bounded exact primary-domain queries',
 'limit':'Not exhaustive literature or priority certification; no external proof was declared solved or unsolved solely from absence',
 'local_check':'Read15 captured manuscripts; G1 value only, G3 bounded aspect, S alpha/m->positive c, FAST alpha/m->infinity, old exact fixed-m results no joint-growing-m rigidity',
 'file_search_diagnostic':'Four initially un-dated directory shorthand paths were absent; recovered real dated paths with rg --files. This was a path lookup error, not a mathematical FAIL.'})
shutil.copyfile(Path(__file__),folder/'initialize_sublinear_rigidity.py')
shutil.copyfile(Path(__file__),aux/'initialize_sublinear_rigidity.py')
print(json.dumps({'created_utc':now.isoformat(),'folder':str(folder),'captured_inputs':len(rows),
 'source_inputs_sha256':sha(folder/'SOURCE_INPUTS.json'),'root_commit':head},indent=2))
