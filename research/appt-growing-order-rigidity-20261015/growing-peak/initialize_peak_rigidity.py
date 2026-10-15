from pathlib import Path
import datetime as dt
import hashlib
import json
import shutil
import subprocess

repo=Path('/home/mxym/math-breadth-tcs-20261015')
root=Path('/home/mxym/math-appt-multiscale-20261013')
folder=repo/'research/breadth-tcs-20261015/phase-6-growing-peak-rigidity'
aux=Path('/mnt/d/math/tmp/breadth-tcs-20261015/phase-6-growing-peak-rigidity')
folder.mkdir(parents=True,exist_ok=True)
head='1c76bb8dd03bb622e8ed1eabbe88e8abc5b3e59f'
now=dt.datetime.now(dt.timezone.utc)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
names=['research/appt-growing-renyi/PAPER.md','research/appt-growing-renyi/UNIFORM_PROFILE.md',
 'research/appt-growing-renyi/SPECTRAL_PROFILE.md','research/appt-growing-renyi/LINEAR_ORDER_VARIATIONAL.md',
 'research/appt-growing-renyi/ALL_ORDER_VARIATIONAL.md','research/appt-growing-renyi/MACROSCOPIC_HIGH_ORDER.md',
 'research/appt-linear-critical-rigidity-20261015/PAPER.md',
 'research/appt-ultralinear-spectrum-20261014/FAST_ORDER_SPECTRA.md',
 'research/appt-all-positive-axis-20261014/PAPER.md',
 'research/appt-all-order-exact-20261014/PAPER.md',
 'research/appt-growing-renyi-order-20261015/PAPER.md',
 'research/appt-finite-entropy-bounds-20261015/PAPER.md']
rows=[]
for name in names:
    data=subprocess.check_output(['git','-C',str(root),'show',head+':'+name])
    dest=folder/'credited-inputs'/name;dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_bytes(data);dest.chmod(0o444)
    rows.append({'path':name,'sha256':sha(dest),'bytes':len(data),'commit':head,
      'actual_read_scope':'Complete prior scientific manuscript read retained in this role; G7-G18 and G actual examples reread in full relevant sections before this proof',
      'role':'G is credited physical mathematical input; remaining files establish the existing value/spectral scope and are not new audited inputs'})
shutil.copyfile(aux/'PAPER.md',folder/'PAPER.md')
shutil.copyfile(Path(__file__),folder/'initialize_peak_rigidity.py')
dump(folder/'SOURCE_INPUTS.json',{'created_utc':now.isoformat(),'root_capture_commit':head,'inputs':rows,
 'mathematical_dependencies':['G7/G9/G10: actual star, pivot, sorting and trace bounds','G11-G15: bounded middle deviations, bounded exceptional square mass, actual second peak and exact first-peak ceiling','G16-G18: real-power kernel and exact trace centering','G15: actual all-global-unitary APPT pure-spike attainment of the physical peak'],
 'not_dependencies':['Pending phase5 sublinear manuscript','Four phase4 scalar geometry manuscripts','Assumption that necessary physical tests are sufficient','Any new Lean scope'],
 'limits':'Ordinary written theorem inputs credited; no independent audit of old inputs expanded or relabeled'})
dump(folder/'TARGET.json',{'created_utc':now.isoformat(),
 'domain':'Every fixed finite C>0, every original complex all-global-unitary APPT density sequence with integers2<=m<=n,m->infinity,real alpha->infinity,alpha<=Cm,chi=alpha log[3D/(D+2)]-logD->+infinity',
 'objectives':['Uniform each-actual-state profile M/(u_D^alpha/D)=exp(-h)+o(1)','Sharp moment/excess nearoptimality iff h->0','Relative entropy-deficit nearoptimality iff h/chi->0','Actual full-tail flatness, second-peak power decay, and concentration of the full raw moment in the physical peak'],
 'actual_defect':'h=alpha log(u_D/y1)>=0, y1 actual normalized largest eigenvalue',
 'scope_gain':'All aspects and bounded oscillating alpha/m, particularly finite-positive alpha/m and diverging peak ratio, not covered by finite-r S or superlinear FAST',
 'clock_policy':'Continuous APPT depth, no breadth change-topic timer',
 'status':'Complete author ordinary proof, pending distinct independent review; no new-major resolution or Lean promotion'})
dump(folder/'PRIMARY_SCREEN.json',{'recorded_utc':now.isoformat(),
 'actual_search_time_window_utc':['2026-10-15T13:29:17.7493324Z','2026-10-15T13:30:20.7258463Z'],
 'queries':['"absolutely PPT" "spectral rigidity" "order"','"absolutely PPT" "entropy" "peak"','"absolute PPT" "Renyi" "growing"'],
 'domains':['arxiv.org'],'result':'No results returned for these bounded exact primary-domain queries',
 'limit':'Neither exhaustive literature screening nor historical-priority certification; no full-domain claim inferred solely from absence',
 'local_range_screen':'G criterion bounded aspect; G1 sublinear all-aspect value; S finite peak ratio; FAST superlinear order ratio; L/V and uniform/all-positive-axis/exact fixed-m papers value or different joint-limit scope',
 'prior_external_source_scope':'Only earlier official abstract/version screens 2609.18568v1 and 2608.03390v2 retained, not an independent full-paper read of those external works'})
dump(folder/'ATTEMPT_LEDGER.json',{'created_utc':now.isoformat(),'stage':'depth phase6',
 'scope_boundary':'No full-diverging-alpha assembly before separate component and synthesis independent reviews',
 'events':[{'utc_window':['2026-10-15T13:29:17.7493324Z','2026-10-15T13:30:20.7258463Z'],'kind':'file-path diagnostic',
   'actual_failure':'Native rg could not find credited-inputs/G_PAPER.md: old snapshot preserves the original research directory tree, not a flattened alias',
   'recovery':'Listed credited-inputs and read credited-inputs/research/appt-growing-renyi/PAPER.md actual source; no mathematical inference or evidence was lost'}],
 'math_false_variants_retained':['Logging the absolute additive o(r) moment error does not prove a relative entropy criterion','Bare y1->3 or h/alpha->0 misses chi/alpha->0 paths','Multiplying a second-peak ratio by m^2 or D without energy control is not a valid sum estimate','Finite-r S losses and J saturation cannot simply be extrapolated to r->infinity'],
 'actual_mathematical_control_failures_so_far':[]})
print(json.dumps({'utc':now.isoformat(),'folder':str(folder),'paper_sha256':sha(folder/'PAPER.md'),
 'paper_bytes':(folder/'PAPER.md').stat().st_size,'inputs':len(rows)},indent=2))
