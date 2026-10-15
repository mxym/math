"""Source-bound author diagnostics for the lower APPT bulk threshold.

Exact identities and series support the written argument; finite sampled
comparisons do not establish global optimality or all-unitary APPT.
"""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,shutil,traceback,sys
import sympy as s
import mpmath as mp

base=Path(__file__).resolve().parent
mp.mp.dps=120
stamp=datetime.now(timezone.utc)
run=base/'control-runs'/stamp.strftime('%Y%m%dT%H%M%S.%fZ')
run.mkdir(parents=True,exist_ok=False)
names=['PAPER.md','THEOREM_MAP.md','CREDITED_INPUTS.json','PRIMARY_SCOPE.json','checks.py','requirements.txt']
hashes={}
for name in names:
 f=base/name;hashes[name]=hashlib.sha256(f.read_bytes()).hexdigest();shutil.copyfile(f,run/name)
result={'utc':stamp.isoformat(),'kind':'author diagnostics, separate from independent read',
        'input_sha256':hashes,'python':sys.version,'sympy':s.__version__,
        'mpmath':mp.__version__,'decimal_precision':mp.mp.dps,'groups':{},
        'new_Lean':False,'finite_grid_is_not_a_global_proof':True}

def need(ok,msg):
 if not ok:raise AssertionError(msg)
def exact(a,b):return s.simplify(a-b)==0
def q(x):return x/mp.expm1(x) if x else mp.mpf(1)
def gg(x):return -mp.log(q(x))-1+q(x) if x else mp.mpf(0)
def bb(x):return mp.exp(gg(x))
def geom(L):return 2*L*L/(3*(2-L))
def B(c,L,h):return (1-h)*mp.exp(-c*L*h)+h*mp.exp(c*L*(1-h))
def P(c,L,h):return mp.exp(-c*(L*h+geom(L))) if L<2 else mp.mpf(0)
def mixU(c,L):
 if L==0:return mp.mpf(0)
 k=c*L
 return max(mp.mpf(0),(-mp.log(q(k))-gg(2*c))/k)
def UU(c,L,h):
 if L==0:return bb(2*c)-1
 return mp.exp(c*geom(L))*(bb(2*c)*mp.exp(c*L*h)-1-h*mp.expm1(c*L))
def UUmin(c,L):
 if L==0:return bb(2*c)-1
 k=c*L;a=c*geom(L)
 if mixU(c,L)==0:return mp.exp(a)*(bb(2*c)-1)
 return mp.exp(a)*(gg(2*c)-gg(k))/q(k)
def phi(c,t):return UUmin(c,2-c*t)/c**3
def branch(c):
 t=mp.findroot(lambda z:mp.diff(lambda x:phi(c,x),z),(mp.mpf('2.5'),mp.mpf('2.9')),
               tol=mp.mpf('1e-85'))
 L=2-c*t;h=mixU(c,L);r=UUmin(c,L)
 return t,L,h,r

def symbols():
 x,c,t,A,GK=s.symbols('x c t A GK',positive=True)
 gx=s.log((s.exp(x)-1)/x)-1+x/(s.exp(x)-1)
 series=s.series(gx,x,0,7).removeO()
 need(exact(series,x*x/8-x**4/576+x**6/25920),'exact g Taylor series')
 k=2*c-c*c*t;gp=lambda z:z*z/8-z**4/576
 delta=s.expand(gp(2*c)-gp(k))
 coeff0=s.expand(delta/c**3).coeff(c,0)
 coeff1=s.expand(delta/c**3).coeff(c,1)
 need(exact(coeff0,t/2) and exact(coeff1,-t*t/8),'divisible g difference')
 first=s.simplify(coeff1+coeff0*(1-s.Rational(8,3)))
 need(exact(first,-t*t/8-5*t/6),'Phi first coefficient')
 psi=t*s.exp(8/(3*t))/2;v1=s.exp(8/(3*t))*(-t*t/8-5*t/6)
 t0=s.Rational(8,3)
 need(exact(s.diff(psi,t).subs(t,t0),0),'limiting stationarity')
 need(exact(s.diff(psi,t,2).subs(t,t0),3*s.E/16),'limiting curvature')
 need(exact(v1.subs(t,t0),-28*s.E/9),'threshold c4 coefficient')
 need(exact(s.diff(v1,t).subs(t,t0),-s.E/3),'width derivative coefficient')
 need(exact(-s.diff(v1,t).subs(t,t0)/s.diff(psi,t,2).subs(t,t0),s.Rational(16,9)),
      'width c2 coefficient')
 numerator=s.series(s.log((s.exp(x)-1)/x),x,0,5).removeO().subs(x,k)-gp(2*c)
 hm=s.series(numerator/k,c,0,3).removeO()
 need(exact(hm,s.Rational(1,2)-c/6-c*c*t/6),'mixing coefficient')
 Gsmall=s.log(A)-1+1/A
 need(exact(A-1-A*(s.log(A)-GK),A*(GK-Gsmall)),'exact h elimination identity')
 return {'exact_symbolic_checks':10,'g_series':str(series),
         'limiting_curvature':'3e/16','first_width_shift':'16/9'}

def fixed_width_controls():
 total=0
 for c in map(mp.mpf,['0.0001','0.001','0.01','0.1','0.8','1','2']):
  for L in map(mp.mpf,['0','0.001','0.2','0.8','1.5','1.9','1.999999']):
   h=mixU(c,L);U=UUmin(c,L)
   need(0<=h<1,'constrained unique mixing in [0,1)')
   need(abs(UU(c,L,h)-U)<=mp.mpf('1e-90')*max(1,abs(U)),
        'exact optimized h substitution')
   if h>0:
    k=c*L
    need(abs(bb(2*c)*k*mp.exp(k*h)-mp.expm1(k))<mp.mpf('1e-90'),
         'interior h stationarity')
   for z in [mp.mpf(0),mp.mpf('.1'),mp.mpf('.5'),mp.mpf('.9'),mp.mpf(1)]:
    need(UU(c,L,z)>=U-mp.mpf('1e-90')*max(1,abs(U)),'convex h diagnostic')
   total+=1
 return {'width_parameter_pairs':total,'h_comparisons_per_pair':5,
         'width_two_singularity_controlled_analytically':True}

def global_localization_controls():
 count=0
 for c in map(mp.mpf,['0.0001','0.001','0.01','0.05']):
  for L in map(mp.mpf,['0','0.01','0.5','1','1.5','1.9','1.99','1.9999']):
   lower=c*c*(2-L)/8
   need(bb(2*c)-bb(c*L)>=lower-mp.mpf('1e-100'),'global width gap')
   for h in map(mp.mpf,['0','0.1','0.5','0.9','1']):
    need(bb(2*c)-B(c,L,h)>=lower-mp.mpf('1e-100'),'global body gap')
    count+=1
 boundary=[]
 for t in map(mp.mpf,['0.1','0.03','0.01','0.003']):
  lower=t*mp.exp(2/(3*t))/8
  boundary.append({'t':str(t),'rescaled_lower_bound':mp.nstr(lower,25)})
 return {'global_gap_cases':count,'thin_layer_lower_bounds':boundary,
         'finite_cases_do_not_establish_global_compactness':True}

def small_c_controls():
 rows=[]
 for c in map(mp.mpf,['0.001','0.0003','0.0001','0.00001']):
  t,L,h,r=branch(c)
  need(abs(t-(mp.mpf(8)/3+mp.mpf(16)/9*c))<30*c*c,'width expansion diagnostic')
  need(abs(h-(mp.mpf('.5')-c/6-mp.mpf(4)/9*c*c))<30*c**3,'mix expansion diagnostic')
  rseries=4*mp.e/3*c**3-28*mp.e/9*c**4
  need(abs(r-rseries)<100*c**5,'threshold expansion diagnostic')
  need(mp.diff(lambda z:phi(c,z),t,2)>0,'reduced positive curvature')
  poleline=bb(2*c)-1
  need(0<r<poleline,'lower onset precedes bare crossing')
  need(abs(P(c,L,h)-mp.exp(-1))<3*c,'peak slope limit diagnostic')
  value=B(c,L,h)+r*P(c,L,h)
  need(abs(value-bb(2*c))<mp.mpf('1e-90'),'exact coexistence diagnostic')
  need(B(c,L,h)+r*mp.mpf('.99')*P(c,L,h)<bb(2*c),'subthreshold competitor')
  need(B(c,L,h)+r*mp.mpf('1.01')*P(c,L,h)>max(bb(2*c),1+r*mp.mpf('1.01')),
       'strict coupled phase above first onset')
  for ell in map(mp.mpf,['0','0.1','0.5','1','1.5','1.8','1.95','1.99','1.999','1.9999']):
   need(UUmin(c,ell)>=r-mp.mpf('1e-90'),'finite global width regression')
  rows.append({'c':str(c),'t':mp.nstr(t,35),'L':mp.nstr(L,35),'h':mp.nstr(h,35),
               'r_over_c3':mp.nstr(r/c**3,35),'peak_slope':mp.nstr(P(c,L,h),35)})
 return {'analytic_branch_diagnostics':rows,'global_uniqueness_proof':'analytic paper, not findroot'}

def physical_family():
 rows=[]
 for c in map(mp.mpf,['0.01','0.02']):
  t,L,h,r=branch(c);target=bb(2*c);prev=None;seq=[]
  for alpha in [20,60,120]:
   m=int(alpha/c);n=max(m,int(mp.nint(mp.mpf(3)**alpha/(r*m))));D=m*n
   k=max(1,min(D-1,int(mp.floor(h*D))));kap=L/(m-1)
   eta=2*(m-2)*kap*kap/(2-(m-3)*kap);d=2-kap-eta
   need(0<k<D and d>=0 and kap<=mp.mpf(2)/(m-1),'finite APPT family parameter domain')
   z=1+kap*mp.mpf(k)/D+d/D
   moment=(mp.mpf(D-k)/D+mp.mpf(k-1)/D*(1+kap)**alpha+(3-eta)**alpha/D)/z**alpha
   error=abs(moment-target)
   need(error<mp.mpf('.001'),'finite quantum lower-family diagnostic')
   if prev is not None:need(error<prev,'finite integer family convergence diagnostic')
   prev=error
   seq.append({'m':m,'alpha':alpha,'D_digits':len(str(D)),
               'absolute_moment_error':mp.nstr(error,25),
               'relative_excess_error':mp.nstr(error/(target-1),25)})
  rows.append({'c':str(c),'cases':seq})
 return {'actual_integer_rank_and_dimension_sequences':rows,
         'APPT_justification':'credited analytic all-global-unitary sufficient theorem, not sampled matrices'}

def false_variants():
 c=mp.mpf('0.001');t,L,h,r=branch(c);rej=[]
 need(abs(r/c**3-4*mp.e/3)<mp.mpf('.02'),'cubic lower threshold regression')
 need(r/(c*c)<mp.mpf('.01'),'quadratic scale would be false')
 rej.append('replace the lower-onset cubic scale by the bare quadratic crossing')
 correct=4*mp.e/3*c**3-28*mp.e/9*c**4
 wrong=4*mp.e/3*c**3+28*mp.e/9*c**4
 need(abs(r-correct)<abs(r-wrong)/100,'c4 sign regression')
 rej.append('reverse the c4 correction sign')
 need(P(c,L,h)<mp.mpf('.5'),'peak factor is not one at lower onset')
 rej.append('drop the protection exponent when minimizing U')
 need((bb(2*c)-1)/r>100,'zero-width onset competitor is not minimizer at small c')
 rej.append('force zero width or merge both onset thresholds')
 need(UU(c,L,mp.mpf('.5'))>r,'exact mixing is not one half')
 rej.append('replace exact mixing by one half before higher-order expansion')
 need(P(c,2,mp.mpf('.5'))==0 and P(c,L,h)>mp.mpf('.3'),'bulk width-two peak is singular')
 rej.append('apply interior surviving-peak formula at width two')
 return {'false_variants_rejected':rej,'count':len(rej)}

try:
 need(hashes['PAPER.md']=='3e1f67ee40b28af0b9de3a643488524fdb38f508d663f63e2ec82f7bc4322804',
      'unknown mathematical source')
 for name,fn in [('exact_symbolic',symbols),('convex_mixing',fixed_width_controls),
                 ('global_localization',global_localization_controls),('small_c_branch',small_c_controls),
                 ('actual_integer_quantum_family',physical_family),('false_variant_regressions',false_variants)]:
  result['groups'][name]=fn()
 result['status']='PASS'
except BaseException as err:
 result['status']='FAIL';result['error']=str(err);result['traceback']=traceback.format_exc()
finally:
 (run/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'status':result.get('status'),'run':str(run),'groups':list(result['groups']),
                   'error':result.get('error'),'paper_sha256':hashes['PAPER.md']}))
if result['status']!='PASS':raise SystemExit(1)
