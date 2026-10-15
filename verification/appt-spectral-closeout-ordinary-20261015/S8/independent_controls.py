"""Reviewer's controls. Numerical checks falsify errors; analytic proof is separate."""
from pathlib import Path
import sys,json,datetime,hashlib,copy,traceback,itertools
from fractions import Fraction as Q
import sympy as sp
import mpmath as mp
out=Path(__file__).resolve().parent
sys.path.insert(0,str(out/'replay-work'))
import critical_exact_intervals as ci
import global_mixed_turn_certificate as gc
mp.mp.dps=80
results={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'positive':[],'negative':[],'unexpected_failures':[]}
def record(name,details=None):results['positive'].append({'name':name,'details':details})
def negative(name,call):
    try:call()
    except (AssertionError,ValueError,KeyError,ZeroDivisionError) as e:
        results['negative'].append({'name':name,'rejected':True,'exception':type(e).__name__,'message':str(e)})
    else:raise AssertionError('MUTANT ACCEPTED '+name)

# Exact symbolic derivatives independently from original elementary definitions.
c,k,E,r,L,x=sp.symbols('c k E r L x',positive=True)
q=k/(E-1);s=E/(E-1)-1/k;g=-sp.log(q)-1+q
dk=lambda v:sp.diff(v,k)+E*sp.diff(v,E)
a=2*k*k/(3*(2*c-k));ak=sp.diff(a,k)
T=r*q*sp.exp(-a);f=g+T
identities={
 'q_prime':sp.factor(dk(q)+s*q)==0,
 'g_prime':sp.factor(dk(g)-s*(1-q))==0,
 'a_k_at_fixed_c':sp.factor(ak.subs(k,2*c*x)-2*x*(2-x)/(3*(1-x)**2))==0,
 'a_c_at_fixed_k':sp.factor(sp.diff(a,c)+4*k*k/(3*(2*c-k)**2))==0,
 'f_k':sp.simplify(dk(f)-(s*(1-q)-T*(s+ak)))==0,
 'f_c_fixed_k':sp.simplify(sp.diff(f,c)-4*T*k*k/(3*(2*c-k)**2))==0,
 'chain_rule_fixed_L':sp.simplify(sp.diff(f.subs({k:c*L,E:sp.exp(c*L)}, simultaneous=True),c)-(sp.diff(f,c)+L*dk(f)).subs({k:c*L,E:sp.exp(c*L)}, simultaneous=True))==0,
 'stationary_factorization':sp.factor((4*k*k/(3*(2*c-k)**2))/2-ak*(k/(2*c))/(2-k/(2*c)))==0,
}
assert all(identities.values()),identities
record('eight_exact_symbolic_identities',identities)

# Independent exact rational containment checks of the integer interval base,
# with negative intervals and inversion, not just positive author boxes.
intervals=[ci.I(-7,-2),ci.I(-3,9),ci.I(2,11),ci.I(-ci.SCALE*3,-ci.SCALE),ci.I(ci.SCALE//3,ci.SCALE*2),ci.I(-ci.SCALE*2,ci.SCALE*4)]
def exact_bounds(v):return Q(v.lo,ci.SCALE),Q(v.hi,ci.SCALE)
def contains(v,t):return Q(v.lo,ci.SCALE)<=t<=Q(v.hi,ci.SCALE)
checks=0
for u,v in itertools.product(intervals,repeat=2):
    ua,ub=exact_bounds(u);va,vb=exact_bounds(v)
    for xx,yy in itertools.product([ua,(ua+ub)/2,ub],[va,(va+vb)/2,vb]):
        assert contains(u+v,xx+yy) and contains(u*v,xx*yy)
        checks+=2
for u in intervals:
    if u.lo<=0<=u.hi:negative('inverse_rejects_zero_interval_'+str(u),lambda u=u:u.inv())
    else:
        for xx in exact_bounds(u):assert contains(u.inv(),1/xx);checks+=1
record('exact_interval_arithmetic_rational_containment',checks)

# Independent cover verifier: coordinate-grid open cells rather than author's
# active-slab tiling. Finite closed rectangles then also cover every edge.
def grid_cover(row):
    a,b=map(Q,row['first']);c,d=map(Q,row['second'])
    boxes=[tuple(map(Q,l['first']+l['second'])) for l in row['leaves']]
    assert boxes
    assert all(a<=al<ar<=b and c<=bl<=br<=d for al,ar,bl,br in boxes)
    aa=sorted({a,b}|{e for box in boxes for e in box[:2]})
    if c==d:
        assert all(bl==br==c for al,ar,bl,br in boxes)
        bb=[(c,c)]
    else:
        assert all(bl<br for al,ar,bl,br in boxes)
        bs=sorted({c,d}|{e for box in boxes for e in box[2:]})
        bb=list(zip(bs,bs[1:]))
    cells=0
    for al,ar in zip(aa,aa[1:]):
        xx=(al+ar)/2
        for bl,br in bb:
            yy=(bl+br)/2
            count=sum(l<xx<u and (v<yy<w if c<d else v==yy==w) for l,u,v,w in boxes)
            assert count==1,('coverage multiplicity',count,str(xx),str(yy))
            cells+=1
    return cells
cert=json.loads((out/'frozen-dependencies/GLOBAL_MIXED_TURN_CERTIFICATE.json').read_bytes())
assert len(cert['stages'])==len(gc.STAGES)==6
cells=[];leafs=0
for row,expected in zip(cert['stages'],gc.STAGES):
    assert row['name']==expected['name'] and row['sign']==expected['sign']
    assert row['first']==list(map(str,expected['first'])) and row['second']==list(map(str,expected['second']))
    cells.append(grid_cover(row))
    for leaf in row['leaves']:
        aa=gc.interval(*map(Q,leaf['first']));bb=gc.interval(*map(Q,leaf['second']))
        bound=gc.evaluate(row['name'],aa,bb)
        if bound is None:
            assert leaf['method']=='outside_K_cap' and row['name']=='middle_negative' and leaf['bound'] is None
            assert (aa*bb).lo>ci.I.rat(13,25).hi
        else:
            saved=leaf['bound'];assert saved['scale_bits']==160
            assert bound==ci.I(int(saved['lo']),int(saved['hi']))
            assert (bound.lo>0 if row['sign']>0 else bound.hi<0)
        leafs+=1
record('independent_global_cover_and_all_bounds',{'leaves':leafs,'elementary_cells_by_stage':cells})
row=cert['stages'][0]
mut=copy.deepcopy(row);mut['leaves'].pop(0)
negative('global_gap_leaf_removed',lambda:grid_cover(mut))
mut2=copy.deepcopy(row);mut2['leaves'].append(copy.deepcopy(mut2['leaves'][0]))
negative('global_overlap_duplicate_leaf',lambda:grid_cover(mut2))
mut3=copy.deepcopy(row)
for leaf in mut3['leaves']:
    if leaf['first'][0]=='0':leaf['first'][0]='1/1000000'
negative('global_K_zero_strip_missing',lambda:grid_cover(mut3))
def check_bound_leaf(leaf,row):
    aa=gc.interval(*map(Q,leaf['first']));bb=gc.interval(*map(Q,leaf['second']))
    bound=gc.evaluate(row['name'],aa,bb);saved=leaf['bound']
    assert bound==ci.I(int(saved['lo']),int(saved['hi']))
mut4=copy.deepcopy(row['leaves'][0]);mut4['bound']['lo']=str(int(mut4['bound']['lo'])+1)
negative('exact_record_one_integer_forgery',lambda:check_bound_leaf(mut4,row))

# Numerical evaluation starts from original F, with automatic differentiation.
def data(t):
    qq=t/mp.expm1(t);ss=1/(1-mp.exp(-t))-1/t
    gg=-mp.log(qq)-1+qq
    return qq,ss,gg,ss*(1-qq)
def original(c0,r0,l,h):
    bulk=mp.exp(-c0*l*h)*(1+h*mp.expm1(c0*l))
    peak=mp.exp(-c0*(l*h+2*l*l/(3*(2-l)))) if l<2 else mp.mpf(0)
    return bulk+r0*peak
def stationary(c0,x0):
    kk=2*c0*x0;qq,ss,gg,gp=data(kk)
    aa=4*c0*x0*x0/(3*(1-x0));aa_k=2*x0*(2-x0)/(3*(1-x0)**2)
    tt=gp/(ss+aa_k);rr=tt*mp.exp(aa)/qq
    hh=(1-qq-tt)/kk
    return rr,hh,tt
numeric=[]
for cs in ['0.000001','0.001','0.02','0.1','0.2','0.2595','0.26','0.7','2']:
    c0=mp.mpf(cs)
    for xs in ['0.08','0.31','0.5','0.73','0.93']:
        xx=mp.mpf(xs);rr,hh,tt=stationary(c0,xx);ll=2*xx
        vv=original(c0,rr,ll,hh)
        assert 0<hh<1
        gradl=mp.diff(lambda l:original(c0,rr,l,hh),ll)
        gradh=mp.diff(lambda h:original(c0,rr,ll,h),hh)
        assert abs(gradl)/vv<mp.mpf('1e-65') and abs(gradh)/vv<mp.mpf('1e-65')
        actual=mp.diff(lambda cc:original(cc,rr,ll,hh),c0)
        predicted=vv*4*tt*xx*xx/(3*(1-xx)**2)
        assert abs(actual-predicted)/vv<mp.mpf('1e-65')
        upper=2*vv*data(2*c0)[3]
        assert 0<actual<upper
        peak=mp.exp(-c0*(ll*hh+2*ll*ll/(3*(2-ll))))
        assert abs(mp.diff(lambda r0:original(c0,r0,ll,hh),rr)-peak)<mp.mpf('1e-65')
        numeric.append({'c':cs,'x':xs,'M_c_over_M':mp.nstr(actual/vv,25),'upper_over_M':mp.nstr(upper/vv,25),'P':mp.nstr(peak,25)})
record('original_F_differentiation_at_45_stationary_points',numeric)

# Reject the actual conceptual mutations using nonstationary original F.
c0=mp.mpf('.2');kk=mp.mpf('.23');rr=mp.mpf('.012')
def reduced(cc,kk0,rr0):
    qq,ss,gg,gp=data(kk0)
    return gg+rr0*qq*mp.exp(-2*kk0*kk0/(3*(2*cc-kk0)))
fixed_k=mp.diff(lambda cc:reduced(cc,kk,rr),c0)
ll=kk/c0
fixed_L=mp.diff(lambda cc:reduced(cc,cc*ll,rr),c0)
def require_close(a,b):assert abs(a-b)<mp.mpf('1e-50'),mp.nstr(a-b,30)
negative('fixed_k_and_fixed_L_identified_away_from_stationarity',lambda:require_close(fixed_k,fixed_L))
qq,ss,gg,gp=data(kk);aa=2*kk*kk/(3*(2*c0-kk));tt=rr*qq*mp.exp(-aa);hh=(1-qq-tt)/kk
vv=mp.exp(reduced(c0,kk,rr));P=mp.exp(-kk*hh-aa)
negative('M_r_replaced_by_log_value_derivative',lambda:require_close(P,qq*mp.exp(-aa)))
def false_positive_at_zero_r():
    actual=mp.diff(lambda cc:reduced(cc,kk,mp.mpf(0)),c0)
    assert actual>0,('actual fixed-k derivative at r=0',str(actual))
negative('positive_M_c_assumed_at_r_zero_noncritical',false_positive_at_zero_r)

# Independently solve coexistence from original F stationarity and tie equations.
# At c=.2 there is one lower and one upper mixed tie under the credited geometry.
coex=[]
for kind,guess in [('B',('.2','.6','.45','.02')),('P',('.2','.45','.45','.024'))]:
    cc=mp.mpf('.2')
    def eq(l,h,rr0):
        val=original(cc,rr0,l,h)
        pure=mp.exp(data(2*cc)[2]) if kind=='B' else 1+rr0
        return (mp.diff(lambda ll0:original(cc,rr0,ll0,h),l),mp.diff(lambda hh0:original(cc,rr0,l,hh0),h),val-pure)
    # Explicit sensible original-coordinate guesses, no one-dimensional curve formula.
    initial=(mp.mpf('1.4') if kind=='B' else mp.mpf('.85'),mp.mpf('.35'),mp.mpf('.018') if kind=='B' else mp.mpf('.025'))
    l,h,rr0=mp.findroot(eq,initial,tol=mp.mpf('1e-60'),maxsteps=100)
    assert 0<l<2 and 0<h<1 and rr0>0
    val=original(cc,rr0,l,h)
    mc=mp.diff(lambda cx:original(cx,rr0,l,h),cc)
    pp=mp.diff(lambda rx:original(cc,rx,l,h),rr0)
    purec=2*mp.exp(data(2*cc)[2])*data(2*cc)[3]
    slope=(purec-mc)/pp if kind=='B' else mc/(1-pp)
    assert slope>0
    def branch(cnew):
        def eqnew(ln,hn,rn):
            pure=mp.exp(data(2*cnew)[2]) if kind=='B' else 1+rn
            return (mp.diff(lambda lx:original(cnew,rn,lx,hn),ln),mp.diff(lambda hx:original(cnew,rn,ln,hx),hn),original(cnew,rn,ln,hn)-pure)
        return mp.findroot(eqnew,(l,h,rr0),tol=mp.mpf('1e-60'),maxsteps=30)[2]
    delta=mp.mpf('1e-12');fd=(branch(cc+delta)-branch(cc-delta))/(2*delta)
    assert abs(fd-slope)<mp.mpf('1e-20')
    coex.append({'kind':kind,'L':mp.nstr(l,35),'h':mp.nstr(h,35),'r':mp.nstr(rr0,35),'analytic_slope':mp.nstr(slope,35),'independent_original_equation_central_difference':mp.nstr(fd,35)})
record('two_coexistence_slope_checks_from_original_F',coex)

# Triple point solved directly from original derivatives plus both pure values.
def triple_eq(cc,ll,hh):
    rr0=mp.expm1(data(2*cc)[2])
    return (mp.diff(lambda l0:original(cc,rr0,l0,hh),ll),mp.diff(lambda h0:original(cc,rr0,ll,h0),hh),original(cc,rr0,ll,hh)-(1+rr0))
ct,lt,ht=mp.findroot(triple_eq,('.25967','1.05','.42'),tol=mp.mpf('1e-65'),maxsteps=50)
rt=mp.expm1(data(2*ct)[2]);mt=1+rt
mct=mp.diff(lambda cc:original(cc,rt,lt,ht),ct)
pt=mp.diff(lambda rr0:original(ct,rr0,lt,ht),rt)
r0p=2*mt*data(2*ct)[3]
bp=(r0p-mct)/pt;pp=mct/(1-pt)
assert 0<pp<r0p<bp
record('triple_original_equations_and_strict_slope_order',{'c':mp.nstr(ct,40),'r':mp.nstr(rt,40),'L':mp.nstr(lt,40),'h':mp.nstr(ht,40),'rP_prime':mp.nstr(pp,40),'r0_prime':mp.nstr(r0p,40),'rB_prime':mp.nstr(bp,40)})

smallc_checks=0
for cs,ls,hs in itertools.product(['.000001','.001','.1','1'],['.000001','.01','.8','1.999999','2'],['0','.00000001','.3','1']):
    cc,ll,hh=map(mp.mpf,[cs,ls,hs])
    bulk=original(cc,0,ll,hh)
    peak=mp.exp(-cc*(ll*hh+2*ll*ll/(3*(2-ll)))) if ll<2 else mp.mpf(0)
    ratio=(bulk-1)/(1-peak)
    assert ratio>=-mp.mpf('1e-60') and ratio<=3*mp.exp(2)*cc
    smallc_checks+=1
record('small_c_endpoint_inequality_edge_falsification',smallc_checks)

results['limitations']=['No numerical sample proves the global theorem','The proof is reviewer analytic reconstruction in REVIEW.md, using exact credited geometry/L/S in their frozen scopes','No whole-axis quantum transfer beyond finite positive c and finite r','Not Lean or human peer review']
(out/'INDEPENDENT_CONTROLS.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps({'positive_groups':len(results['positive']),'negative_rejected':len(results['negative']),'unexpected_failures':len(results['unexpected_failures']),'coexistence':coex},indent=2))
