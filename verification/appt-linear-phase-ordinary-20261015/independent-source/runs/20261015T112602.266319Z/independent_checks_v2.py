"""New reviewer implementation; original T5 c>=10 scope only."""
from pathlib import Path
from fractions import Fraction as R
from datetime import datetime,timezone
import hashlib,json,shutil,traceback
import mpmath as mp
import sympy as sp

mp.mp.dps=400
base=Path(__file__).resolve().parent
out=base/'runs'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ');out.mkdir(parents=True,exist_ok=False)
shutil.copyfile(__file__,out/'independent_checks_v2.py');shutil.copyfile(base/'INPUT_V2.json',out/'INPUT_V2.json')
counts={};rejections=[]
def must(condition,label):
    if not condition:raise AssertionError(label)
def reject(name,false_assertion,details):
    try:must(false_assertion,name)
    except AssertionError as e:
        row={'name':name,'status':'REJECTED','actual_exception':repr(e),'details':details};rejections.append(row)
        (out/('REJECTED-'+name+'.json')).write_text(json.dumps(row,indent=2)+'\n')
    else:raise AssertionError('wrong variant survived '+name)
def remainder(x):
    if abs(x)>mp.mpf('.001'):return mp.expm1(x)-x
    term=x*x/2;value=term;n=2
    while term:
        n+=1;term*=x/n;value+=term
        if abs(term)<=mp.eps*abs(value):break
        must(n<10000,'remainder series converges')
    return value
def parts(c,L,h):
    c=mp.mpf(c);L=mp.mpf(L);h=mp.mpf(h)
    Bminus=(1-h)*remainder(-c*L*h)+h*remainder(c*L*(1-h))
    if L==0:return Bminus,mp.mpf(1),mp.mpf(0),mp.mpf(0)
    if L==2:return Bminus,mp.mpf(0),Bminus,mp.mpf(0)
    A=L*h+2*L*L/(3*(2-L));P=mp.exp(-c*A)
    f=L*L*h*(1-h)/(2*A)
    return Bminus,P,Bminus/(-mp.expm1(-c*A)),f
def logbulk(K):
    return mp.log(mp.expm1(K)/K)-1+K/mp.expm1(K)
def hbulk(c):return 1/(2*c)-1/mp.expm1(2*c)
def gradients(c,L,h):
    Bminus,P,Q,f=parts(c,L,h);A=L*h+2*L*L/(3*(2-L));den=-mp.expm1(-c*A)
    Bh=mp.exp(-c*L*h)*(mp.expm1(c*L)-c*L*(1+h*mp.expm1(c*L)))
    BL=c*h*(1-h)*mp.exp(-c*L*h)*mp.expm1(c*L)
    GL=2*L*(4-L)/(3*(2-L)**2)
    return ((BL*den-Bminus*c*(h+GL)*P)/(den*den*c),(Bh*den-Bminus*c*L*P)/(den*den*c))

try:
    L,h,c,A=sp.symbols('L h c A',positive=True)
    a=2*L/(3*(2-L));f=L*h*(1-h)/(2*(h+a));v=3*h*h*(1-2*h)/(3*h*h-4*h+2);q=3*h**3-8*h*h+8*h-2
    must(sp.simplify(sp.diff(v,h)+6*h*q/(3*h*h-4*h+2)**2)==0,'cubic stationary reduction')
    must(sp.simplify(sp.diff(a,L)-4/(3*(2-L)**2))==0,'explicit a derivative')
    ast=h*h/(1-2*h)
    fh=sp.diff(f,h);fhh=sp.diff(fh,h)
    # Substitute a general independent parameter to test the stationary h curvature.
    aa=sp.symbols('a',positive=True);ff=L*h*(1-h)/(2*(h+aa))
    must(sp.simplify(sp.diff(ff,h).subs(aa,ast))==0,'stationary h relation')
    must(sp.simplify((sp.diff(ff,h,2)+L/(h+aa)).subs(aa,ast))==0,'stationary h curvature')
    B=sp.exp(-c*L*h)*(1+h*(sp.exp(c*L)-1))
    B2=L*L*h*(1-h)/2;B3=L**3*h*(1-h)*(1-2*h)/6
    must(sp.simplify(sp.diff(B,c,2).subs(c,0)/2-B2)==0,'second moment Taylor coefficient')
    must(sp.simplify(sp.diff(B,c,3).subs(c,0)/6-B3)==0,'third moment Taylor coefficient')
    K=sp.symbols('K',positive=True);g=sp.log((sp.exp(K)-1)/K)-1+K/(sp.exp(K)-1)
    deriv=1-1/K+2/(sp.exp(K)-1)-K*sp.exp(K)/(sp.exp(K)-1)**2
    must(sp.simplify(sp.diff(g,K)-deriv)==0,'logbulk exact derivative')
    counts['symbolic_identities']=7
    # Rational certification of the cubic root interval and q' positivity.
    def cubic(x):return 3*x**3-8*x*x+8*x-2
    lo,hi=R(1,3),R(3,8);must(cubic(lo)<0<cubic(hi),'root brackets')
    must(9*R(1,2)**2-16*R(1,2)+8>0,'qprime minimum on interval')
    for _ in range(160):
        mid=(lo+hi)/2
        if cubic(mid)<0:lo=mid
        else:hi=mid
    h0=mp.mpf((lo+hi).numerator)/((lo+hi).denominator*2)
    a0=h0*h0/(1-2*h0);L0=6*a0/(2+3*a0);A0=L0*h0+2*L0*L0/(3*(2-L0))
    K0=3*h0*h0*(1-2*h0)/(3*h0*h0-4*h0+2)
    K1=K0*(L0*(1-2*h0)/3+A0/2)
    H=mp.matrix([[mp.mpf(sp.N(sp.diff(f,x,y).subs({L:str(L0),h:str(h0)}),160)) for y in [L,h]] for x in [L,h]])
    must(H[0,0]<0 and mp.det(H)>0,'negative definite full Hessian')
    counts['exact_root_bisections']=160
    endpoints=0
    for cc in map(mp.mpf,['1e-100','1e-40','1e-8','.01','.3','1','10']):
        widths=[mp.mpf(0),cc/(1+cc),cc*cc/(1+cc*cc),mp.mpf(1),2-min(cc*cc,mp.mpf(1)),2-mp.mpf('1e-30'),mp.mpf(2)]
        for LL in widths:
            for hh in [mp.mpf(0),mp.mpf('1e-40'),min(cc,mp.mpf('.5')),mp.mpf('.37'),1-mp.mpf('1e-40'),mp.mpf(1)]:
                bm,P,Q,f0=parts(cc,LL,hh);b2=LL*LL*hh*(1-hh)/2
                low=mp.exp(-2*cc)*f0;up=mp.exp(2*cc)*(f0+cc*b2)
                tolerance=mp.mpf('1e-290')*max(abs(up),mp.mpf('1e-500'))
                must(low<=Q/cc+tolerance and Q/cc<=up+tolerance,'global moving endpoint T11')
                bound=mp.expm1(2*cc)*f0+mp.exp(2*cc)*cc*b2
                must(abs(Q/cc-f0)<=bound+tolerance,'global absolute small-c bound')
                endpoints+=1
    counts['moving_endpoint_cases']=endpoints
    small=[]
    for cc in map(mp.mpf,['.01','.001','.0001']):
        lc,hc=mp.findroot(lambda x,y:gradients(cc,x,y),(L0,h0),tol=mp.mpf('1e-180'))
        rc=parts(cc,lc,hc)[2]
        must(0<lc<2 and 0<hc<1,'small-c branch interior')
        cubic_residual=(rc-K0*cc-K1*cc*cc)/(cc**3)
        must(abs(cubic_residual)<10,'second-order K1 expansion diagnostic')
        small.append({'c':str(cc),'stationary_L':str(lc),'stationary_h':str(hc),'threshold_candidate':str(rc),'third_order_residual':str(cubic_residual),'finite_stationary_diagnostic_not_global_certification':True})
    counts['small_c_stationary_branch_cases']=len(small)
    large=0
    for cc in map(mp.mpf,['10','10.125','20','100']):
        b=mp.exp(logbulk(2*cc));r0=b-1
        must(cc*(1+cc)*mp.exp(cc)/2<mp.exp(2*cc)/(2*mp.e*cc)-1,'strict small-width global bound')
        for LL in map(mp.mpf,['0','1e-8','.2','1','1.0001','1.9','1.999999','2']):
            for hh in [mp.mpf(0),mp.mpf('1e-8'),mp.mpf('.2'),hbulk(cc),mp.mpf('.8'),1-mp.mpf('1e-8'),mp.mpf(1)]:
                bm,P,Q,f0=parts(cc,LL,hh)
                if 0<LL<2:must(Q<r0,'strict nonendpoint threshold separation')
                for rr in [mp.mpf(0),r0/2,r0,r0+1,2*r0]:
                    F=1+bm+rr*P
                    must(F<=max(b,1+rr)+mp.mpf('1e-280')*max(b,1+rr),'large-c envelope bound')
                    large+=1
    counts['large_c_full_parameter_sample_cases']=large
    # Direct domain counterexample: actual pole at alpha=1/2, while concavity gives max moment=1.
    Mhalf=(mp.sqrt(3)+8)/(3*mp.sqrt(11));Ehalf=-2*mp.log(Mhalf)
    reject('extend-log-max-moment-identity-below-one',Ehalf==0,{'m':3,'D':9,'alpha':'1/2','actual_APPT_pole_deficit':str(Ehalf),'max_concave_moment':1,'source_finding_corrected_in_v2':True})
    cc=mp.mpf('1e-5');LL=2-cc**2;hh=mp.mpf('.5');f0=parts(cc,LL,hh)[3];value=parts(cc,LL,hh)[2]/cc
    reject('global-relative-instead-of-absolute-small-c-limit',abs(value/f0-1)<mp.mpf('.1'),{'c':str(cc),'L':str(LL),'Q_over_c_over_f':str(value/f0),'correct_statement':'uniform absolute O(c), not relative to vanishing f'})
    missing=K0*L0*(1-2*h0)/3
    reject('omit-denominator-K1-correction',mp.almosteq(missing,K1),{'correct_K1':str(K1),'omitted_half_B2_version':str(missing),'positive_difference':str(K1-missing)})
    cc=mp.mpf(10);b=mp.exp(logbulk(2*cc));r0=b-1;step=mp.mpf('.01')
    left=(max(b,1+r0)-max(b,1+r0-step))/step;right=(max(b,1+r0+step)-max(b,1+r0))/step
    must(abs(left)<mp.mpf('1e-300') and abs(right-1)<mp.mpf('1e-300'),'one-sided envelope slopes')
    reject('left-derivative-is-greatest-active-slope',left==1,{'left':str(left),'right':str(right),'active_slopes':[0,1]})
    reject('independently-add-optimized-bulk-and-peak',b+r0<=max(b,1+r0),{'coupled_true_envelope':str(b),'false_independent_sum':str(b+r0)})
    # Maximally mixed is actual APPT and has delta0 body but a nonzero physical head slack.
    m=10;alpha=10*m;rr=2*b;D=m*int(mp.ceil(mp.power(3,alpha)/(rr*m)));actual_r=mp.power(3,alpha)/D
    Pmixed=actual_r-mp.mpf(1)/D
    reject('bulk-law-suffices-for-r-positive-near-optimality',Pmixed<mp.mpf('.1'),{'actual_APPT_state':'I/D','body_law':'delta0 exactly','J':0,'peak_loss':str(Pmixed),'physical_deficit':0,'c':10,'r_above_threshold':str(actual_r),'D_integer':str(D)})
    D=9;alpha=3;raw=mp.mpf(3**alpha+D-1)/D;normalized=raw/mp.power(1+mp.mpf(2)/D,alpha)
    reject('omit-actual-pole-trace-normalization',mp.almosteq(raw,normalized),{'raw_moment':str(raw),'actual_moment':str(normalized)})
    m=10;D=m*m;alpha=D*D;u=mp.mpf(3)*D/(D+2)
    logratio=alpha*mp.log(3)-mp.log(D)-(alpha-1)*mp.log(u)
    reject('extend-fixed-C-moment-transfer-to-unbounded-alpha-over-m',logratio<mp.log(2),{'log_lower_bound_scalar_over_all_actual_moments':str(logratio),'m':m,'D':D,'alpha':alpha})
    (out/'SMALL_C.json').write_text(json.dumps({'h0_root_interval':[str(lo),str(hi)],'L0':str(L0),'K0':str(K0),'K1':str(K1),'Hessian':str(H),'branches':small},indent=2)+'\n')
    result={'status':'PASS','utc':datetime.now(timezone.utc).isoformat(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'input_manifest_sha256':hashlib.sha256((base/'INPUT_V2.json').read_bytes()).hexdigest(),'counts':counts,'expected_rejections':rejections,'author_code_imported_or_executed':False,'newly_written_by_reviewer':True,'scope':'v2 original T5 c>=10; no oral c>=1 claim certified','finite_diagnostics_not_global_optimizer_or_all_quantifier_proof':True,'mpmath_precision':mp.mp.dps,'Lean':False}
    (out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'PASS','run':str(out),'counts':counts,'rejections':len(rejections)}))
except Exception:
    (out/'RESULT.json').write_text(json.dumps({'status':'FAIL','utc':datetime.now(timezone.utc).isoformat(),'counts_before_failure':counts,'traceback':traceback.format_exc()},indent=2)+'\n')
    raise
