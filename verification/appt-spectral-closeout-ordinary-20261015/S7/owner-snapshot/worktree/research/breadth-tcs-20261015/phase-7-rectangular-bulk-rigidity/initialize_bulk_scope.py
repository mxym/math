from pathlib import Path
import datetime as dt
import hashlib
import json
import shutil
import subprocess

repo=Path('/home/mxym/math-breadth-tcs-20261015')
root=Path('/home/mxym/math-appt-multiscale-20261013')
folder=repo/'research/breadth-tcs-20261015/phase-7-rectangular-bulk-rigidity'
aux=Path('/mnt/d/math/tmp/breadth-tcs-20261015/phase-7-rectangular-bulk-rigidity')
folder.mkdir(parents=True,exist_ok=True)
head='1c76bb8dd03bb622e8ed1eabbe88e8abc5b3e59f'
now=dt.datetime.now(dt.timezone.utc)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
names=[('research/appt-growing-renyi/PAPER.md','G physical mathematical input and credited actual protected-spike example; complete manuscript previously read and sections2-3/5 reread before these new proofs'),
 ('research/appt-growing-renyi/UNIFORM_PROFILE.md','Complete prior read plus sections1-3 reread; credited all-aspect compact-order VALUE, not a new value target'),
 ('research/appt-growing-renyi/SPECTRAL_PROFILE.md','Complete reread; finite gamma nearoptimizer scope and compact-kernel input screen, not the new gamma->infinity result'),
 ('research/appt-growing-renyi/SMALL_ORDER_BOUNDARY.md','Complete prior read retained plus current full statements Z1/Z2 and section6 reread; finite tau,c spectral scope, credited zero-order value'),
 ('research/appt-multilevel-counterexample/SUBUNIT_RIGIDITY.md','Complete reread; finite gamma fixed positive order scope and credited singular-spectrum fact'),
 ('research/appt-multilevel-counterexample/PHASE_RIGIDITY.md','Complete prior read retained, current first140 lines reread; finite gamma purity W1, explicitly not W2')]
rows=[]
for name,scope in names:
    data=subprocess.check_output(['git','-C',str(root),'show',head+':'+name])
    p=folder/'credited-inputs'/name;p.parent.mkdir(parents=True,exist_ok=True)
    p.write_bytes(data);p.chmod(0o444)
    rows.append({'path':name,'sha256':sha(p),'bytes':len(data),'commit':head,'actual_read_scope':scope})
for name in ['PAPER.md','author_bulk_controls.py','AUTHOR_EXACT_CONTROLS.json','initialize_bulk_scope.py']:
    shutil.copyfile(aux/name,folder/name)
dump(folder/'SOURCE_INPUTS.json',{'created_utc':now.isoformat(),'root_capture_commit':head,'inputs':rows,
 'mathematical_input':'G7-G15 actual physical pivot/width/exception square mass/purity/shifted-star inequalities; G16-G18 and SPECTRAL_PROFILE integral kernel extended explicitly to all alpha>0; ordinary Schmidt background and 1D monotone transport',
 'novel_scope':'Actual all-aspect positive bounded-order bulk rigidity including alpha->0 with alpha gamma->infinity, uniform quantitative W2 bound and sharp exponent for actual APPT states',
 'additional_collision_read':'ENTROPY_ASYMPTOTIC headings/statements and rigidity sections6,10,12.2 were checked; not represented as a new complete-file independent read',
 'not_dependencies':['Pending S5/S6 manuscripts','Phase4 scalar geometry','Root developing all-zero-order path synthesis','Any new Lean or expanded audit'],
 'scope_limits':'Existing value claims credited; no full-axis assembly or priority certification'})
dump(folder/'TARGET.json',{'created_utc':now.isoformat(),
 'domain':'For each fixed finite A>0 every actual complex all-global-unitary APPT density sequence,2<=m<=n,m->infinity,0<alpha<=A,alpha gamma->infinity,arbitrary alpha/n oscillation',
 'claims':['Uniform actual entropy ratio equals Q/gamma with explicit O_A[1/m+1/(alpha gamma)] error','Relative entropy nearoptimality iff actual full rescaled empirical law converges W2 to fair atoms+-1','W2<=C_A[d_alpha+epsilon]^(1/4)','Exponent1/4 optimal for an exact integer-rank actual all-unitary APPT projection family'],
 'sharpness':'m=l^4,n=m^2,D=l^12,l even,rankD/2+D/l,c2/(m-1),d~4/l^2,W2^2~4/l,uniform alpha in every fixed positive compact interval',
 'must_keep':['All original state quantifiers','Actual projection APPT proof and integer ranks','Exact W2 cost','Explicit joint-scale finite-value error smaller than the sharpness gap','Exceptional quadratic mass, actual middle mean and J','Crossing1/2,1,2 and alpha->0 bulk-dominant paths'],
 'status':'Complete author ordinary proof; independent review pending; no major-problem or Lean count'})
dump(folder/'PRIMARY_SCREEN.json',{'recorded_utc':now.isoformat(),
 'actual_search_time_window_utc':['2026-10-15T13:38:16.7216107Z','2026-10-15T13:38:25Z'],
 'queries':['"absolutely PPT" "Wasserstein"','"absolute PPT" "unbounded aspect" entropy','"absolutely PPT" "near-minimizers" entropy'],
 'domains':['arxiv.org'],'results':'No results for those bounded exact official-primary-domain queries',
 'local_screen':'Native rg across actual research markdown excluding credited copies; actual old rigidity manuscripts finite gamma, SMALL Z2 finite tau,c; finite-entropy review explicitly excludes all-aspect rigidity',
 'limit':'Bounded source/scope screen, not exhaustive literature or historical priority; no whole external paper independent audit claimed'})
dump(folder/'ATTEMPT_LEDGER.json',{'created_utc':now.isoformat(),'scope':'S7 rectangular bulk quantitative actual-state rigidity',
 'actual_nonmath_diagnostics':[{'utc_window':['2026-10-15T13:36:39.1629582Z','2026-10-15T13:38:16.7216107Z'],
   'failure':'rg queried an imagined appt-entropy-purity-saturation-20261015 research directory, which does not exist',
   'recovery':'Used rg --files and whole actual research markdown search; did not treat path absence as a mathematical gap or audit the parallel Lean modules'}],
 'actual_math_control_failures':[],
 'retained_rejected_inferences':['Ignoring 1/alpha at a zero eigenvalue invalidates uniform alpha->0 bounds','Weak convergence alone cannot imply W2; QE/gamma must be controlled','Formal two-atom law is not an APPT construction; exact projection witness and integer rank supplied','An unquantified E equivalent does not prove d~4/l^2; explicit uniform O(l^-4) value error supplied','A stronger W2 exponent is rejected by actual exact-rank spectra'],
 'research_status':'Complete author proof, not a whole-axis synthesis; root separately researches all-zero-order path criterion',
 'author_controls':'12 finite actual physical spectra and exact inequalities passed; Decimal only labels entropy diagnostics; no exact finite E computed'})
print(json.dumps({'utc':now.isoformat(),'folder':str(folder),'paper_sha256':sha(folder/'PAPER.md'),
 'paper_bytes':(folder/'PAPER.md').stat().st_size,'source_inputs_sha256':sha(folder/'SOURCE_INPUTS.json')},indent=2))
