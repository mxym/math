"""Independent symbolic/quantifier/counterexample diagnostics for the first
three new scopes. No author module is imported; numerical probes are not the
proof of any continuous domain. Author replay is separately recorded.
"""
from pathlib import Path
from datetime import datetime,timezone
from fractions import Fraction as F
from collections import Counter
import ast,hashlib,json,shutil,sys,traceback
import sympy as sy
import mpmath as mp
BASE=Path(__file__).resolve().parent
SRC=BASE/'owner-zip-snapshot/worktree/research/breadth-tcs-20261015/phase-4-depth-appt'
mp.mp.dps=650
STAMP=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
RUN=BASE/'runs'/STAMP;RUN.mkdir(parents=True)
shutil.copyfile(__file__,RUN/'executed_script.py')
R={'utc':STAMP,'kind':'new independent auxiliary diagnostics, not author replay or Lean',
   'author_modules_imported':False,'python':sys.version,'sympy':sy.__version__,
   'mpmath':mp.__version__,'precision_digits':mp.mp.dps,'groups':{}}
def q(t):return t/mp.expm1(t)
def w(t):return -mp.log(q(t))
def d(t):return 1-q(t)
def s(t):return 1-d(t)/t
def gp(t):return s(t)*d(t)
def sp(t):return 1/t**2-mp.exp(t)/mp.expm1(t)**2
def g(t):return w(t)-d(t)
def gpp(t):return sp(t)*d(t)+s(t)**2*q(t)
def elastic(t):return t*s(t)*q(t)/d(t)
def reduced(K,x):
    k=K*x;delta=g(K)-g(k);v=w(k)-g(K)
    aa=2*K*x*x/(3*(1-x))
    W=aa+mp.log(delta)-mp.log(q(k))-mp.log(mp.expm1(g(K)))
    ak=mp.mpf(2)/3*((1-x)**(-2)-1)
    Wx=K*(ak+s(k)-gp(k)/delta)
    Wxx=K*K*(4/(3*K*(1-x)**3)+sp(k)-gpp(k)/delta-gp(k)**2/delta**2)
    return v,W,Wx,Wxx
def exact_symbolic():
    t=sy.symbols('t',positive=True);E=sy.exp(t)-1
    qq=t/E;dd=1-qq;ss=1-dd/t;ww=-sy.log(qq);gg=ww-dd
    H=(t-2)*sy.exp(t)+t+2;ee=t*sy.diff(dd,t)/dd;z=(t-dd)/dd
    checks=[sy.simplify(sy.diff(qq,t,2)-sy.exp(t)*H/E**3),
            sy.simplify(sy.diff(gg,t,2)-sy.diff(ww,t,2)-sy.diff(qq,t,2)),
            sy.simplify(t*sy.diff(gg,t,2)/sy.diff(gg,t)-(qq*z-qq+1/z)),
            sy.simplify(sy.diff(ee,t)/ss-(-ee+qq*(ee+qq)*(1-ee)/((1-qq)*ee)))]
    y=sy.symbols('y',positive=True)
    curv=-sy.log(y)-sy.Rational(3,2)+2*y-y*y/2
    checks.append(sy.simplify(sy.diff(curv,y)+(1-y)**2/y))
    j=sy.symbols('j');poly=32*j**4-96*j**3+86*j*j-20*j-1
    checks += [sy.factor((4*(3-2*j)*j*(j-sy.Rational(1,4))-j)*(5-4*j)-1-poly),
               sy.factor(sy.diff(poly,j,2)+20-192*(2*j-1)*(j-1)),
               sy.simplify(poly.subs(j,sy.Rational(1,2))-sy.Rational(1,2)),
               sy.simplify(poly.subs(j,1)-1)]
    v,z0=sy.symbols('v z0',positive=True)
    phi=sy.exp(-v)-1+v
    integ=sy.integrate((1-z0)*sy.exp(-z0*v),(z0,0,1))
    checks.append(sy.simplify(phi/v**2-integ))
    q0=sy.symbols('q0');delta=1-q0-v
    checks.append(sy.simplify(delta+phi-(sy.exp(-v)-q0)))
    K,k=sy.symbols('K k',positive=True);G=sy.Function('G');W0=sy.Function('w')
    a=2*k*k/(3*(K-k));D=G(K)-G(k)
    obj=a+sy.log(D)+W0(k)
    ak=sy.Rational(2,3)*((1-k/K)**(-2)-1)
    akk=4/(3*K*(1-k/K)**3)
    checks += [sy.simplify(sy.diff(obj,k)-(ak+sy.diff(W0(k),k)-sy.diff(G(k),k)/D)),
               sy.simplify(sy.diff(obj,k,2)-(akk+sy.diff(W0(k),k,2)-sy.diff(G(k),k,2)/D-sy.diff(G(k),k)**2/D**2))]
    p,r,A=sy.symbols('p r A',positive=True);dp=-2*p*r*A
    lower=-dp/p;upper=dp/(1-p)
    checks.append(sy.simplify((upper-lower)+2*r*A/(1-p)))
    for c in checks:assert c==0,c
    return {'exact_symbolic_identities':len(checks),'barrier_second_derivative_factor':'192(2E-1)(E-1)<=0 on [1/2,1]'}
def analytic_diagnostics():
    count=0;barriers=0;monotone=0;concave=0;witnesses=[]
    for val in ['1e-100','1e-30','.000001','.01','.1','1','3','10','30','100']:
        t=mp.mpf(val)
        assert t*gpp(t)/gp(t)>1-g(t)/2
        assert 0<sp(t)<=mp.mpf(1)/12
        count+=1
        if elastic(t)>mp.mpf('.5'):
            assert elastic(t)<1-w(t)/4;barriers+=1
    for xx in ['.01','.1','.5','.9','.9999']:
        x=mp.mpf(xx)
        for kk in ['.001','.1','.519','1','10','100']:
            K=mp.mpf(kk);k=K*x
            assert x*x*sp(k)-gpp(K)<0;concave+=1
            v,W,_,_=reduced(K,x)
            if v>0:
                derivative=mp.diff(lambda T:reduced(T,x)[1],K)
                assert derivative>0;monotone+=1
    for cc in ['.000001','.001','.01','.1']:
        c=mp.mpf(cc);r0=mp.expm1(g(2*c))
        excess=mp.cosh(c/2)-1-r0*(-mp.expm1(-7*c/6))
        assert excess>=mp.mpf(5)/96*c*c
        witnesses.append({'c':cc,'strict_excess':mp.nstr(excess,30)})
    return {'curvature_and_sprime_cases':count,'conditional_elasticity_cases':barriers,
        'strict_admissible_WK_cases':monotone,'strict_v_concavity_cases':concave,
        'explicit_last_boundary_witnesses':witnesses,'finite_cases_not_continuous_proof':True}
def certificate_structure():
    cert=json.loads((SRC/'CRITICAL_EXACT_INTERVAL_CERTIFICATE.json').read_text())
    assert cert['parameters']['precision_bits']==160
    assert cert['parameters']['compact_x']==['1/10','9/10'] and cert['parameters']['core_x']==['1/2','11/20']
    assert cert['source_sha256']==hashlib.sha256((SRC/'critical_exact_intervals.py').read_bytes()).hexdigest()
    tree=ast.parse((SRC/'critical_exact_intervals.py').read_text())
    assert not any(isinstance(x,ast.Constant) and isinstance(x.value,float) for x in ast.walk(tree))
    ranges=[('upper_full_cover',F(1,10),F(9,10),27),('outside_core_left',F(1,10),F(1,2),32),
            ('outside_core_right',F(11,20),F(9,10),13),('core_convexity_cover',F(1,2),F(11,20),1)]
    summary=[]
    def bounds(dct):
        assert dct['scale_bits']==160
        lo=int(dct['lo']);hi=int(dct['hi']);assert lo<=hi
        return lo,hi
    for name,start,end,n in ranges:
        rows=sorted(cert[name],key=lambda r:F(r['x_lo']));assert len(rows)==n
        cursor=start;total=F(0)
        for row in rows:
            l=F(row['x_lo']);h=F(row['x_hi']);assert l==cursor and l<h
            total+=h-l;cursor=h;lo,hi=bounds(row['bound']);method=row['method']
            if method=='inadmissible':assert hi<=0
            elif method=='strict_positive_W':assert lo>F(1,10000)*(1<<160)
            elif method in ['W_excludes_zero','Wx_excludes_zero']:assert lo>0 or hi<0
            elif method=='strict_positive_Wxx_and_admissible':assert lo>F(1,10)*(1<<160) and bounds(row['admissible_v'])[0]>0
            else:raise AssertionError(method)
        assert cursor==end and total==end-start
        summary.append({'name':name,'leaves':n,'start':str(start),'end':str(end),
                  'methods':dict(Counter(row['method'] for row in rows))})
    return {'covers':summary,'total_leaves':sum(x[3] for x in ranges),'whole_K_strip_leaves':45,
        'engine_transcendental_math_and_rounding_review':'manual complete code/proof read; this separate helper verifies exact partition/sign serialization, not a new implementation of the author interval engine'}
def triple_point_diagnostic():
    K,x=mp.findroot(lambda K,x:(reduced(K,x)[1],reduced(K,x)[2]),
                    (mp.mpf('.51934'),mp.mpf('.522')),tol=mp.mpf('1e-550'))
    v,W,Wx,Wxx=reduced(K,x);h=v/(K*x);c=K/2;r=mp.expm1(g(K));L=2*x
    assert mp.mpf(519)/1000<K<mp.mpf(13)/25 and mp.mpf('.5')<x<mp.mpf('.55')
    WK=mp.diff(lambda kk:reduced(kk,x)[1],K)
    P=mp.exp(-c*(L*h+2*L*L/(3*(2-L))))
    assert 0<h<1 and Wxx>mp.mpf('.1') and WK>0 and 0<P<1
    Fval=mp.exp(-c*L*h)*(1+h*mp.expm1(c*L))+r*P
    assert abs(Fval-mp.exp(g(K)))<mp.mpf('1e-500')
    return {'illustrative_c':mp.nstr(c,40),'illustrative_L':mp.nstr(L,40),'illustrative_h':mp.nstr(h,40),
       'P':mp.nstr(P,35),'WK':mp.nstr(WK,35),'Wxx':mp.nstr(Wxx,35),
       'mixed_window_linear_coefficient':mp.nstr(2*r*WK/(1-P),35),
       'root_search_is_not_the_interval_proof':True}
def false_variants():
    out=[]
    def reject(name,claim,witness):
        try:assert claim,name
        except AssertionError as ex:out.append({'name':name,'actual_exception':'AssertionError: '+str(ex),'witness':witness})
        else:raise AssertionError('failed to reject '+name)
    K=mp.mpf(2);x=mp.mpf('.01');v,W,_,_=reduced(K,x)
    reject('drop v>0 from the logarithmic strict mixed test',not(W<0 and v<0),
       {'K':'2','x':'.01','v':mp.nstr(v,30),'W':mp.nstr(W,30),'actual_constrained_U_over_r0':mp.nstr(mp.exp(2*K*x*x/(3*(1-x))),30)})
    t=mp.mpf(10)
    reject('apply e<1-w/4 without the e>1/2 condition',elastic(t)<1-w(t)/4,
       {'t':'10','e':mp.nstr(elastic(t),30),'right_side':mp.nstr(1-w(t)/4,30)})
    t=mp.mpf(1)
    reject('reverse the curvature lower bound',t*gpp(t)/gp(t)<=1-g(t)/2,
       {'t':'1','positive_margin':mp.nstr(t*gpp(t)/gp(t)-(1-g(t)/2),30)})
    v=mp.mpf(1)
    deriv=mp.diff(lambda z:(mp.exp(-z)-1+z)/(z*z),v)
    reject('replace the decreasing phi(v)/v^2 ratio by an increasing one',deriv>=0,
       {'v':'1','actual_derivative':mp.nstr(deriv,30)})
    p=F(1,2);r=F(1);A=F(1);gap=F(1,100)
    wrong=-2*r*A/(1-p)*gap
    reject('reverse the closing-window sign on the mixed side',wrong>0,
       {'exact_p':str(p),'exact_r':str(r),'exact_A':str(A),'c_star_minus_c':str(gap),
        'wrong_negative_width':str(wrong),'correct_positive_width':str(-wrong)})
    return {'actual_expected_assertion_errors':out,'count':len(out)}
try:
    for name,fn in [('exact_symbolic',exact_symbolic),('analytic_diagnostics',analytic_diagnostics),
                    ('exact_certificate_structure',certificate_structure),('triple_point_illustration',triple_point_diagnostic),
                    ('false_variants',false_variants)]:R['groups'][name]=fn()
    R['status']='PASS';R['decision']='PASS'
except BaseException:
    R['status']='FAIL';R['decision']='FAIL';R['traceback']=traceback.format_exc()
finally:
    R['executed_script_sha256']=hashlib.sha256((RUN/'executed_script.py').read_bytes()).hexdigest()
    (RUN/'RESULT.json').write_text(json.dumps(R,indent=2)+'\n')
    print(json.dumps({'run':str(RUN),'status':R['status'],'groups':R['groups']},indent=2))
if R['status']!='PASS':print(R['traceback']);raise SystemExit(1)
