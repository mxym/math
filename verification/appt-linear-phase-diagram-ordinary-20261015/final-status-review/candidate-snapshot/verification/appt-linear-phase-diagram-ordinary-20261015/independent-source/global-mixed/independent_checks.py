"""Independent fourth-scope algebra, exact cell coverage, and diagnostics.
No author module is imported. Finite scalar probes do not replace the full
analytic proof and rigorously replayed interval boxes.
"""
from pathlib import Path
from datetime import datetime,timezone
from fractions import Fraction as F
from collections import Counter
import ast,hashlib,json,math,shutil,sys,traceback
import sympy as sy
import mpmath as mp
BASE=Path(__file__).resolve().parent
SRC=BASE/'owner-zip-snapshot/worktree/research/breadth-tcs-20261015/phase-4-depth-appt'
mp.mp.dps=320
STAMP=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
RUN=BASE/'runs'/STAMP;RUN.mkdir(parents=True)
shutil.copyfile(__file__,RUN/'executed_script.py')
R={'utc':STAMP,'kind':'new independent global-mixed auxiliary checks; no author imports',
   'author_modules_imported':False,'python':sys.version,'sympy':sy.__version__,
   'mpmath':mp.__version__,'precision_digits':mp.mp.dps,'groups':{}}

def symbolic():
    K,x,z,t=sy.symbols('K x z t',positive=True)
    ss,sp,spp,rr,rp=sy.symbols('s sp spp R Rp',real=True)
    delta=1-x;k=K*x;Y=2+delta**2*(3*ss-2);yy=Y/(3*delta**2)
    M=3*rr*Y*delta**2+k*Y**2-9*k*sp*delta**4-12*x*delta
    checks=[sy.factor(M-9*delta**4*(rr*yy+k*yy**2-k*sp-4*x/(3*delta**3)))]
    xx=1-K*z;Z=sy.Rational(2,3)+K**2*z**2*(ss-sy.Rational(2,3))
    T=K*rr*Z*z**2+xx*Z**2-K**4*xx*sp*z**4-sy.Rational(4,3)*xx*z
    checks.append(sy.factor(M.subs(x,xx)-9*K*T))
    dd,v=sy.symbols('delta v',positive=True)
    middle=3*rr*(2+dd**2*(3*ss-2))*dd+v*(1-dd)*(2+dd**2*(3*ss-2))**2-9*v*(1-dd)*sp*dd**4-12*(1-dd)
    checks.append(sy.factor(M.subs({x:1-dd,K:v*dd})/dd-middle))
    S=sy.Function('s');Q=sy.Function('R')
    def totalx(expr):return sy.diff(expr,x)+sy.diff(expr,ss)*K*sp+sy.diff(expr,sp)*K*spp+sy.diff(expr,rr)*K*rp
    Yx=-2*delta*(3*ss-2)+3*K*delta**2*sp
    source_Mx=3*(K*rp*Y*delta**2+rr*Yx*delta**2-2*rr*Y*delta)+K*Y**2+2*k*Y*Yx-9*(K*sp*delta**4+k*K*spp*delta**4-4*k*sp*delta**3)-12*(1-2*x)
    checks.append(sy.factor(totalx(M)-source_Mx))
    totalz=sy.diff(T,z)+sy.diff(T,ss)*(-K**2)*sp+sy.diff(T,sp)*(-K**2)*spp+sy.diff(T,rr)*(-K**2)*rp
    Zz=2*K**2*z*(ss-sy.Rational(2,3))-K**4*z**2*sp
    source_Tz=K*(-K**2*rp*Z*z**2+rr*Zz*z**2+2*rr*Z*z)-K*Z**2+2*xx*Z*Zz-K**4*(-K*sp*z**4-K**2*xx*spp*z**4+4*xx*sp*z**3)-sy.Rational(4,3)*(xx-K*z)
    checks.append(sy.factor(totalz-source_Tz))
    checks.append(sy.simplify(T.subs(K,0)-(sy.Rational(4,9)-4*z/3)))
    h,r,a=sy.symbols('h r a',real=True);kk=sy.symbols('k',positive=True)
    q=kk/(sy.exp(kk)-1);d=1-q
    FF=sy.exp(-kk*h)*(1+h*(sy.exp(kk)-1)+r*sy.exp(-a))
    h0=(d-r*q*sy.exp(-a))/kk
    checks.append(sy.simplify(sy.diff(FF,h).subs(h,h0)))
    checks.append(sy.simplify(sy.diff(FF,h,2).subs(h,h0)+kk*(sy.exp(kk)-1)*sy.exp(-kk*h0)))
    e1=(sy.exp(t)-1)/t;e2=(sy.exp(t)-1-t)/t**2;H=e2/e1
    gg=sy.log(e1)-1+1/e1;A=H*(1-H)
    checks.append(sy.simplify(sy.diff(gg,t)-t*A))
    checks.append(sy.simplify(t*sy.diff(gg,t,2)/sy.diff(gg,t)-(1+t*sy.diff(A,t)/A)))
    for c in checks:assert c==0,c
    # Exact removable values, computed by quotient rules rather than division t.
    E1,E1p,E1pp=F(1),F(1,2),F(1,3)
    E2,E2p,E2pp=F(1,2),F(1,6),F(1,12)
    HH=E2/E1;Hp=(E2p-HH*E1p)/E1;Hpp=(E2pp-2*Hp*E1p-HH*E1pp)/E1
    assert (HH,Hp,Hpp)==(F(1,2),F(-1,12),F(0))
    coeff=0
    for p in [1,2]:
        for derivative in [0,1,2]:
            for j in range(65):
                cc=F(math.factorial(j+derivative),math.factorial(j)*math.factorial(j+derivative+p))
                assert 0<cc<=F(1,math.factorial(j));coeff+=1
    return {'exact_symbolic_identities':len(checks),'finite_exact_series_coefficient_checks':coeff,
        'exact_K_zero_values':{'H':'1/2','Hp':'-1/12','Hpp':'0','A':'1/4','R':'1','Rp':'0'},
        'all_degree_tail_proof':'factorial ratio <=1 for every j, plus the exp Taylor tail; not just these finite coefficients'}

def exact_cell_coverage():
    cert=json.loads((SRC/'GLOBAL_MIXED_TURN_CERTIFICATE.json').read_text())
    expected=[('left_positive',(F(0),F(13,25)),(F(0),F(3,10)),1,35),
       ('first_turn_decreasing',(F(0),F(13,25)),(F(3,10),F(2,5)),-1,1),
       ('middle_negative',(F(0),F(3,5)),(F(0),F(5,2)),-1,28),
       ('right_positive',(F(0),F(13,25)),(F(0),F(3,10)),1,5),
       ('second_turn_decreasing',(F(0),F(13,25)),(F(3,10),F(2,5)),-1,1),
       ('second_far_endpoint_negative',(F(0),F(13,25)),(F(2,5),F(2,5)),-1,4)]
    assert len(cert['stages'])==6
    summaries=[];excluded=[]
    for row,(name,arange,brange,sign,count) in zip(cert['stages'],expected):
        assert row['name']==name and tuple(map(F,row['first']))==arange and tuple(map(F,row['second']))==brange
        assert row['sign']==sign and len(row['leaves'])==count
        boxes=[]
        for leaf in row['leaves']:
            al,ah=map(F,leaf['first']);bl,bh=map(F,leaf['second'])
            assert arange[0]<=al<ah<=arange[1] and brange[0]<=bl<=bh<=brange[1]
            boxes.append((al,ah,bl,bh))
            if leaf['method']=='outside_K_cap':
                assert name=='middle_negative' and al*bl>F(13,25) and leaf['bound'] is None
                excluded.append({'first':[str(al),str(ah)],'second':[str(bl),str(bh)],'exact_product_min':str(al*bl)})
            else:
                bd=leaf['bound'];assert bd['scale_bits']==160;lo=int(bd['lo']);hi=int(bd['hi']);assert lo<=hi
                assert (sign==1 and lo>0 and leaf['method']=='strict_positive') or (sign==-1 and hi<0 and leaf['method']=='strict_negative')
        ae=sorted(set([arange[0],arange[1]]+[x for box in boxes for x in box[:2]]))
        be=sorted(set([brange[0],brange[1]]+[x for box in boxes for x in box[2:]]))
        cells=0
        for al,ah in zip(ae,ae[1:]):
            mid=(al+ah)/2
            if brange[0]==brange[1]:
                assert sum(l<mid<h for l,h,_,_ in boxes)==1;cells+=1
            else:
                for bl,bh in zip(be,be[1:]):
                    bmid=(bl+bh)/2
                    assert sum(l<mid<h and b<bmid<d for l,h,b,d in boxes)==1,(name,al,ah,bl,bh)
                    cells+=1
        summaries.append({'name':name,'leaves':count,'exact_open_grid_cells_checked':cells,
             'closed_boundary_coverage':'each cell closure lies in its one closed covering box',
             'K_zero_line_included':arange[0]==0})
    assert len(excluded)==7
    tree=ast.parse((SRC/'global_mixed_turn_certificate.py').read_text())
    assert not any(isinstance(x,ast.Constant) and isinstance(x.value,float) for x in ast.walk(tree))
    return {'stage_covers':summaries,'total_leaves':74,'all_seven_outside_cap_minima':excluded,
        'not_an_area_only_check':True,'new_author_module_imported':False}

def regular(t):
    # Independent numerical E series, used only for diagnostics.
    def ep(p,r):
        return mp.fsum(mp.mpf(math.factorial(j+r))*t**j/(math.factorial(j)*math.factorial(j+r+p)) for j in range(110))
    e1,e1p,e1pp=[ep(1,j) for j in range(3)];e2,e2p,e2pp=[ep(2,j) for j in range(3)]
    H=e2/e1;Hp=(e2p-H*e1p)/e1;Hpp=(e2pp-2*Hp*e1p-H*e1pp)/e1
    A=H*(1-H);Ap=Hp*(1-2*H);App=Hpp*(1-2*H)-2*Hp**2
    return 1-H,-Hp,-Hpp,1+t*Ap/A,Ap/A+t*(App/A-(Ap/A)**2)
def MM(K,x):
    delta=1-x;k=K*x;s,sp,spp,R,Rp=regular(k);Y=2+delta**2*(3*s-2)
    return 3*R*Y*delta**2+k*Y**2-9*k*sp*delta**4-12*x*delta
def TT(K,z):
    x=1-K*z;k=K*x;s,sp,spp,R,Rp=regular(k);Z=mp.mpf(2)/3+K*K*z*z*(s-mp.mpf(2)/3)
    return K*R*Z*z*z+x*Z*Z-K**4*x*sp*z**4-mp.mpf(4)/3*x*z
def turns(K):
    left=mp.findroot(lambda x:MM(K,x),(mp.mpf('.3'),mp.mpf('.4')),tol=mp.mpf('1e-250'))
    z=mp.findroot(lambda z:TT(K,z),(mp.mpf('.3'),mp.mpf('.4')),tol=mp.mpf('1e-250'))
    return left,1-K*z,z
def q(k):return k/mp.expm1(k)
def gg(k):return -mp.log(q(k))-1+q(k)
def logR(K,x):
    k=K*x;s,sp,spp,R,Rp=regular(k);d=1-q(k);a=2*K*x*x/(3*(1-x));ak=mp.mpf(2)/3*((1-x)**(-2)-1)
    return mp.log(s*d)+a-mp.log(q(k))-mp.log(s+ak)
def root_bisect(fn,l,h,increasing):
    for _ in range(140):
        z=(l+h)/2
        if z==l or z==h:break
        val=fn(z)
        if (val<0)==increasing:l=z
        else:h=z
    return (l+h)/2
def finite_diagnostics():
    rows=[]
    for kk in ['0','1e-40','.0001','.1','.519','.52']:
        K=mp.mpf(kk);alpha,beta,z=turns(K)
        assert mp.mpf('.3')<alpha<mp.mpf('.4') and mp.mpf('.3')<z<mp.mpf('.4')
        assert mp.diff(lambda x:MM(K,x),alpha)<0 and mp.diff(lambda zz:TT(K,zz),z)<0
        rows.append({'K':kk,'alpha':mp.nstr(alpha,35),'right_scaled_turn_z':mp.nstr(z,35),'beta':mp.nstr(beta,35)})
    mixed=[]
    for cc in ['.005','.05','.2','.259']:
        c=mp.mpf(cc);K=2*c;alpha,beta,z=turns(K);r=mp.expm1(gg(K));level=mp.log(r)
        f=lambda x:logR(K,x)-level
        roots=[root_bisect(f,mp.mpf('1e-80'),alpha,True),
               root_bisect(f,alpha,beta,False),root_bisect(f,beta,1-mp.mpf('1e-80'),True)]
        scores=[];curv=[]
        for x in roots:
            k=K*x;aa=2*K*x*x/(3*(1-x));h=(1-q(k)-r*q(k)*mp.exp(-aa))/k
            assert 0<h<1
            scores.append(mp.exp(gg(k)+r*q(k)*mp.exp(-aa)))
            curv.append(mp.diff(lambda xx:logR(K,xx),x))
        assert curv[0]>0 and curv[1]<0 and curv[2]>0
        assert scores[1]>mp.exp(gg(K))
        mixed.append({'c':cc,'r0':mp.nstr(r,30),'three_stationary_widths':[mp.nstr(2*x,30) for x in roots],
               'middle_strict_improvement':mp.nstr(scores[1]-mp.exp(gg(K)),30)})
    return {'turn_diagnostics_including_zero_and_tiny_K':rows,'fixed_c_middle_stationary_diagnostics':mixed,
       'whole_domain_proof_not_inferred_from_samples':True}
def false_variants():
    out=[]
    def reject(name,claim,witness):
        try:assert claim,name
        except AssertionError as e:out.append({'name':name,'actual_exception':'AssertionError: '+str(e),'witness':witness})
        else:raise AssertionError('did not reject '+name)
    K=mp.mpf('.00001');x=1-K*mp.mpf('.1')
    actual=MM(K,x);limit=MM(mp.mpf(0),x)
    reject('replace the moving right width layer by the fixed-x K=0 sign',actual*limit>=0,
       {'K':str(K),'x':mp.nstr(x,35),'actual_M_positive':mp.nstr(actual,30),'fixed_x_limit_negative':mp.nstr(limit,30)})
    K=mp.mpf('.1');x=mp.mpf('.01');k=K*x;r=mp.mpf(1);aa=2*K*x*x/(3*(1-x))
    hu=(1-q(k)-r*q(k)*mp.exp(-aa))/k
    formal=mp.exp(gg(k)+r*q(k)*mp.exp(-aa));actual=1+r*mp.exp(-aa)
    reject('apply the interior optimized log formula after h is clamped at zero',abs(formal-actual)<mp.mpf('1e-100'),
       {'negative_formal_h':mp.nstr(hu,30),'formal_minus_actual':mp.nstr(formal-actual,30)})
    delta=mp.mpf('.6');v=mp.mpf('2.5');score=MM(delta*v,1-delta)/delta
    reject('claim the middle-chart negative sign after discarding the K cap',score<0,
       {'delta':'.6','v':'2.5','K':'1.5','actual_positive_M_over_delta':mp.nstr(score,30)})
    # Same area but duplicated left half and uncovered right half.
    boxes=[(F(0),F(1,2),F(0),F(1)),(F(0),F(1,2),F(0),F(1))]
    area=sum((h-l)*(d-b) for l,h,b,d in boxes)
    count=sum(l<F(3,4)<h and b<F(1,2)<d for l,h,b,d in boxes)
    assert area==1
    reject('accept total rational area as a complete two-dimensional cover',count==1,
       {'area':str(area),'right_half_coverage_count':count})
    return {'actual_expected_assertion_errors':out,'count':len(out)}
try:
    for name,fn in [('symbolic_regular_charts',symbolic),('independent_exact_cell_coverage',exact_cell_coverage),
                    ('finite_scalar_diagnostics',finite_diagnostics),('false_variants',false_variants)]:R['groups'][name]=fn()
    R['status']='PASS';R['decision']='PASS'
except BaseException:
    R['status']='FAIL';R['decision']='FAIL';R['traceback']=traceback.format_exc()
finally:
    R['executed_script_sha256']=hashlib.sha256((RUN/'executed_script.py').read_bytes()).hexdigest()
    (RUN/'RESULT.json').write_text(json.dumps(R,indent=2)+'\n')
    print(json.dumps({'run':str(RUN),'status':R['status'],'groups':R['groups']},indent=2))
if R['status']!='PASS':print(R['traceback']);raise SystemExit(1)
