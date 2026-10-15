"""Author diagnostics for the ordinary scalar proof, never a replacement for it.

Exact symbolic identities and rational constants are combined with high-
precision endpoint/parameter stress controls and finite physical-family
regressions. Finite sampling does not certify a global maximum or APPT.
"""
from pathlib import Path
from datetime import datetime,timezone
from fractions import Fraction as Rat
import hashlib,json,traceback,shutil,sys,platform
import sympy as s
import mpmath as mp

base=Path(__file__).resolve().parent
mp.mp.dps=100
utc=datetime.now(timezone.utc)
run=base/'control-runs'/utc.strftime('%Y%m%dT%H%M%S.%fZ')
run.mkdir(parents=True,exist_ok=False)
files=['PAPER.md','THEOREM_MAP.md','PRIMARY_SCOPE.json','CREDITED_INPUTS.json',
       'requirements.txt','checks.py','V1_TO_V2.diff']
hashes={}
for name in files:
 p=base/name
 hashes[name]=hashlib.sha256(p.read_bytes()).hexdigest()
 shutil.copyfile(p,run/name)
result={'utc':utc.isoformat(),'kind':'author controls, not independent proof',
        'inputs_sha256':hashes,'python':sys.version,'sympy':s.__version__,
        'mpmath':mp.__version__,'platform':platform.platform(),'groups':{},
        'new_Lean':False,'new_audit_roots':0,'grid_is_not_a_proof':True}
if hashes['PAPER.md']!='83c2240adfbca39009ff446504cc477f47684a0e5de1db52439862053bbcad79':
 raise RuntimeError('Unrecognized mathematical author source')

def need(cond,msg):
 if not cond:raise AssertionError(msg)
def group(name,fn):
 result['groups'][name]=fn()
def eq(a,b):return s.simplify(a-b)==0
def bulk(c,L,h):return (1-h)*mp.exp(-c*L*h)+h*mp.exp(c*L*(1-h))
def geom(L):return 2*L*L/(3*(2-L)) if L<2 else mp.inf
def peak(c,L,h):return mp.exp(-c*(L*h+geom(L))) if L<2 else mp.mpf(0)
def ratio(c,L,h):
 if L==0:return mp.mpf(0)
 return (bulk(c,L,h)-1)/(-mp.expm1(-c*(L*h+geom(L)))) if L<2 else bulk(c,L,h)-1
def bfun(K):return mp.expm1(K)/K*mp.exp(-1+K/mp.expm1(K))
def hb(c):return 1/(2*c)-1/mp.expm1(2*c)
def ffun(L,h):
 if L==0 or L==2:return mp.mpf(0)
 return L*L*h*(1-h)/(2*(L*h+geom(L)))

def symbolic():
 L,h,a,K=s.symbols('L h a K',positive=True)
 f=L*h*(1-h)/(2*(h+a));aopt=h*h/(1-2*h)
 need(eq(s.diff(f,h).subs(a,aopt),0),'theta stationary equation')
 need(eq(s.diff(f,h,2).subs(a,aopt),(-L/(h+a)).subs(a,aopt)),
      'theta curvature at optimum')
 v=3*h*h*(1-2*h)/(3*h*h-4*h+2)
 q=3*h**3-8*h*h+8*h-2
 need(eq(s.diff(v,h),-6*h*q/(3*h*h-4*h+2)**2),'cubic derivative identity')
 need(q.subs(h,s.Rational(1,3))<0<q.subs(h,s.Rational(3,8)),'cubic bracket')
 need(s.diff(q,h).subs(h,s.Rational(1,2))==s.Rational(9,4),'cubic derivative lower bound')
 need(eq(s.diff(2*L/(3*(2-L)),L),4/(3*(2-L)**2)),'a derivative')
 need(eq((2*a+1)**2-4*(a*a+a),1),'positive optimal theta derivative')
 logb=s.log((s.exp(K)-1)/K)-1+K/(s.exp(K)-1)
 deriv=1-1/K+2/(s.exp(K)-1)-K*s.exp(K)/(s.exp(K)-1)**2
 need(eq(s.diff(logb,K),deriv),'log b derivative')
 t=K*s.exp(K)/(s.exp(K)-1)**2
 need(eq(s.diff(s.log(t),K),1/K-1-2/(s.exp(K)-1)),'negative tail log derivative')
 A=L*h+2*L*L/(3*(2-L));B2=L*L*h*(1-h)/2
 B3=L**3*h*(1-h)*(1-2*h)/6
 need(eq(B3/A+B2/2,(B2/A)*(L*(1-2*h)/3+A/2)),'K1 identity')
 return {'exact_symbolic_identities':10,'cubic_bracket':'1/3<h0<3/8',
         'positive_qprime_lower_bound':'9/4','finite_sample_maximization_claim':False}

def exact_constants():
 e2lower=sum(Rat(2)**k/Rat(s.factorial(k)) for k in range(5))
 need(e2lower==7,'e^2 degree-four sum')
 elower=sum(Rat(1,Rat(s.factorial(k)).numerator) for k in range(6))
 need(elower==Rat(163,60),'e degree-five sum')
 need(163**3>20*60**3,'e^3>20 rational cube')
 need(7**5>4*10**2*11,'large c base exponential bound')
 need(Rat(60,361)<Rat(1,6),'log b tail rational bound')
 need(3*(3+2)<=2*3**2,'large-width constant at c3')
 return {'e2_lower':'7 with strictly positive remainder','e_lower':'163/60',
         'e10_lower':7**5,'tail_bound':'60/361<1/6','checks':6}

def endpoint_controls():
 count=0
 for c in map(mp.mpf,['0.00001','0.001','0.02','0.1','1','10']):
  for L in map(mp.mpf,['0','0.0000000001','0.01','0.4','1','1.8','1.9999999999','2']):
   for h in map(mp.mpf,['0','0.0000000001','0.1','0.365','0.5','0.9','0.9999999999','1']):
    Q=ratio(c,L,h);f=ffun(L,h);B2=L*L*h*(1-h)/2
    tol=mp.mpf('1e-75')
    need(mp.exp(-2*c)*f-tol<=Q/c<=mp.exp(2*c)*(f+c*B2)+tol,
         'uniform ratio estimate at '+str((c,L,h)))
    N=bulk(c,L,h)-1
    need(mp.exp(-2*c)*c*c*B2-tol<=N<=mp.exp(2*c)*c*c*B2+tol,
         'integral Taylor estimate')
    count+=1
 return {'tested_parameter_triples':count,'decimal_precision':mp.mp.dps,
         'vanishing_width_and_mixing_endpoints_included':True,
         'claim':'diagnostic finite cases only; the proof is the uniform analytic bound'}

def small_c_controls():
 h0=mp.findroot(lambda h:3*h**3-8*h*h+8*h-2,(mp.mpf(1)/3,mp.mpf(3)/8))
 a0=h0*h0/(1-2*h0);L0=6*a0/(2+3*a0)
 K0=ffun(L0,h0);A0=L0*h0+geom(L0)
 K1=K0*(L0*(1-2*h0)/3+A0/2)
 Hess=mp.matrix([[mp.diff(lambda L:ffun(L,h0),L0,2),
                  mp.diff(lambda L:mp.diff(lambda h:ffun(L,h),h0),L0)],
                 [mp.diff(lambda L:mp.diff(lambda h:ffun(L,h),h0),L0),
                  mp.diff(lambda h:ffun(L0,h),h0,2)]])
 need(Hess[1,1]<0 and mp.det(Hess)>0,'full Hessian negative definite')
 records=[]
 for c in map(mp.mpf,['0.001','0.0001','0.00001']):
  def dL(L,h):return mp.diff(lambda z:ratio(c,z,h)/c,L)
  def dh(L,h):return mp.diff(lambda z:ratio(c,L,z)/c,h)
  Lc,hc=mp.findroot((dL,dh),(L0,h0),tol=mp.mpf('1e-65'))
  val=ratio(c,Lc,hc)
  need(0<Lc<2 and 0<hc<1,'interior analytic branch diagnostic')
  coeff=(val-K0*c)/(c*c)
  need(abs(coeff-K1)<20*c,'second coefficient convergence diagnostic')
  r=(val+bfun(2*c)-1)/2
  need(val>r>bfun(2*c)-1,'genuine mixed interval diagnostic')
  F=bulk(c,Lc,hc)+r*peak(c,Lc,hc)
  need(F>max(bfun(2*c),1+r),'pure-envelope false at small c')
  records.append({'c':str(c),'L':mp.nstr(Lc,30),'h':mp.nstr(hc,30),
                  'rcrit_branch':mp.nstr(val,30),'K1_estimate':mp.nstr(coeff,30)})
 return {'h0':mp.nstr(h0,45),'L0':mp.nstr(L0,45),'K0':mp.nstr(K0,45),
         'K1':mp.nstr(K1,45),'A0':mp.nstr(A0,45),
         'Hessian_determinant':mp.nstr(mp.det(Hess),45),
         'local_branch_diagnostics':records,
         'local_search_is_not_global_uniqueness_proof':True}

def large_c_controls():
 count=0;derivative_cases=0
 for K in map(mp.mpf,['3','3.1','5','10','20','100','2000']):
  deriv=1-1/K+2/mp.expm1(K)-K*mp.exp(K)/(mp.expm1(K)**2)
  need(deriv>mp.mpf('0.5'),'large K log b derivative')
  derivative_cases+=1
 for c in map(mp.mpf,['10','10.01','11','20','50','1000']):
  b2=bfun(2*c);r0=b2-1
  need(c*(1+c)*mp.exp(c)/2<mp.exp(2*c)/(2*mp.e*c)-1,'small width comparison')
  for L in map(mp.mpf,['0','0.00000001','0.1','0.5','1','1.2','1.8','1.99999999','2']):
   for h in [mp.mpf(0),mp.mpf('0.00001'),mp.mpf('0.1'),hb(c),mp.mpf('.5'),mp.mpf('.99'),mp.mpf(1)]:
    q=ratio(c,L,h)
    need(q<=r0*(1+mp.mpf('1e-85')),'global ratio diagnostic')
    if 0<L<2:
     need(q<r0,'strict interior gap diagnostic')
    for factor in [mp.mpf(0),mp.mpf('.5'),mp.mpf(1),mp.mpf(2),mp.mpf(100)]:
     r=factor*r0;v=bulk(c,L,h)+r*peak(c,L,h)
     need(v<=max(b2,1+r)*(1+mp.mpf('1e-85')),'pure envelope diagnostic')
    count+=1
 return {'parameter_triples':count,'affine_r_controls_per_triple':5,
         'log_derivative_cases':derivative_cases,'largest_c':'1000',
         'sample_is_not_full_quantifier_proof':True}

def quantum_lower_family():
 # At c=12,m=160 the actual pole normalization loss is about 1e-904.
 # The initial 100-digit run rounded it to zero and could not establish
 # a strictly decreasing diagnostic sequence. Keep that FAIL unchanged.
 with mp.workdps(1100):
  return quantum_lower_family_high_precision()

def quantum_lower_family_high_precision():
 records=[]
 for c in [10,12]:
  cc=mp.mpf(c);bulkval=bfun(2*cc)
  for factor in map(mp.mpf,['0.5','1','2']):
   prev=None;errs=[]
   for m in [40,80,160]:
    alpha=c*m;targetr=factor*(bulkval-1)
    n=max(m,int(mp.nint(mp.mpf(3)**alpha/(targetr*m))))
    D=m*n;r=mp.mpf(3)**alpha/D
    theta=hb(cc);k=int(mp.floor(theta*D));k=max(1,min(D-1,k))
    kappa=mp.mpf(2)/(m-1);z=1+kappa*mp.mpf(k)/D
    MB=(mp.mpf(k)/D*(1+kappa)**alpha+(1-mp.mpf(k)/D))/z**alpha
    MP=(mp.mpf(D)/(D+2))**alpha*(r+mp.mpf(D-1)/D)
    reference=max(bulkval,1+r);ratioactual=max(MB,MP)/reference
    err=abs(ratioactual-1)
    need(err<mp.mpf('0.5'),'finite family large error diagnostic')
    if prev is not None:need(err<prev,'finite family convergence diagnostic')
    prev=err
    errs.append({'m':m,'alpha':alpha,'integer_D_digits':len(str(D)),
                 'actual_r_relative_error':mp.nstr(abs(r/targetr-1),8),
                 'relative_moment_discrepancy':mp.nstr(err,18)})
   records.append({'c':c,'critical_r_factor':str(factor),'cases':errs})
 return {'actual_integer_dimension_and_rank_sequences':records,
         'decimal_precision':mp.mp.dps,
         'APPT_source':'credited analytic projection/pole sufficient theorem; no sampled-unitary certificate',
         'full_alpha_over_m_unbounded_extension_claim':False}

def rejected_variants():
 rejected=[]
 c=mp.mpf('0.001');L=mp.mpf('.85');h=mp.mpf('.365');r=mp.mpf('.00008')
 F=bulk(c,L,h)+r*peak(c,L,h)
 need(F>max(bfun(2*c),1+r),'small c pure envelope regression')
 rejected.append('pure envelope for all c')
 Q=ratio(c,L,h);N=bulk(c,L,h)-1
 need(Q>100*N,'omitting the ratio denominator regression')
 rejected.append('remove the vanishing denominator in Q')
 h0=mp.findroot(lambda t:3*t**3-8*t*t+8*t-2,mp.mpf('.365'))
 a0=h0*h0/(1-2*h0);L0=6*a0/(2+3*a0);K0=ffun(L0,h0)
 need(abs(ratio(mp.mpf('1e-6'),L0,h0)/mp.mpf('1e-6')-K0)<mp.mpf('1e-5'),
      'small c linear scale regression')
 need(K0>mp.mpf('.1'),'small c nonquadratic threshold')
 rejected.append('replace linear onset K0*c by c^2/2')
 c=mp.mpf(10);r0=bfun(2*c)-1
 need(abs(bulk(c,2,hb(c))-1-r0)<mp.mpf('1e-80'),'bulk critical tie')
 need(bulk(c,0,mp.mpf('.8'))+r0*peak(c,0,mp.mpf('.8'))==1+r0,'pole critical tie')
 rejected.append('delete either active phase at equality')
 need(peak(c,2,mp.mpf('.3'))==0 and not mp.isfinite(geom(mp.mpf(2))),
      'singular width endpoint regression')
 rejected.append('apply finite interior peak correction at width two')
 alpha=mp.mpf('.5');D=4;y=[mp.mpf(2),mp.mpf(2)/3,mp.mpf(2)/3,mp.mpf(2)/3]
 M=sum(x**alpha for x in y)/D
 need(M<1 and mp.log(M)/(alpha-1)>0,'subunit order max-moment definition finding')
 rejected.append('use maximum moment identity below order one')
 return {'actual_rejected_false_statements':rejected,'count':len(rejected)}

try:
 group('exact_symbolic',symbolic)
 group('exact_constants',exact_constants)
 group('global_endpoint_estimates',endpoint_controls)
 group('small_c_analytic_branch',small_c_controls)
 group('large_c_full_rectangle_diagnostics',large_c_controls)
 group('actual_integer_quantum_lower_family',quantum_lower_family)
 group('false_variant_regressions',rejected_variants)
 result['status']='PASS'
except BaseException as e:
 result['status']='FAIL';result['error']=str(e);result['traceback']=traceback.format_exc()
finally:
 (run/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'status':result.get('status'),'run':str(run),'groups':list(result['groups']),
                   'error':result.get('error'),'paper_sha256':hashes['PAPER.md']}))
if result['status']!='PASS':raise SystemExit(1)
