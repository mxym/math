"""Whole-domain integer interval certificate of two stationary-curve turns.
Author computation only, pending independent ordinary review.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
import datetime as dt
import hashlib
import json
import math
import critical_exact_intervals as m

I=m.I
Q=m.SCALE
N=64
TAIL=m.ceildiv(3*Q,math.factorial(N+1))
COEFF={}
for p in [1,2]:
    for r in [0,1,2]:
        COEFF[p,r]=[I.rat(math.factorial(j+r),math.factorial(j)*math.factorial(j+r+p)) for j in range(N+1)]

@lru_cache(maxsize=None)
def ep_point(p,r,t):
    assert 0<=t<=Q
    x=I(t,t)
    value=I.rat(0)
    for c in reversed(COEFF[p,r]):value=value*x+c
    return I(value.lo,value.hi+TAIL)

def ep(p,r,t):
    return I(ep_point(p,r,t.lo).lo,ep_point(p,r,t.hi).hi)

def normalized(t):
    assert 0<=t.lo<=t.hi<=Q
    E1,E1p,E1pp=[ep(1,j,t) for j in range(3)]
    E2,E2p,E2pp=[ep(2,j,t) for j in range(3)]
    H=E2/E1
    Hp=(E2p-H*E1p)/E1
    Hpp=(E2pp-2*Hp*E1p-H*E1pp)/E1
    A=H*(1-H)
    Ap=Hp*(1-2*H)
    App=Hpp*(1-2*H)-2*Hp*Hp
    R=1+t*Ap/A
    Rp=Ap/A+t*(App/A-(Ap/A)**2)
    return {'s':1-H,'sp':-Hp,'spp':-Hpp,'R':R,'Rp':Rp}

def M_value(K,x,derivative=False):
    delta=1-x;k=K*x
    D=normalized(k)
    s,sp,spp,R,Rp=[D[n] for n in ['s','sp','spp','R','Rp']]
    Y=2+delta**2*(3*s-2)
    value=3*R*Y*delta**2+k*Y**2-9*k*sp*delta**4-12*x*delta
    if not derivative:return value
    Yx=-2*delta*(3*s-2)+3*K*delta**2*sp
    return (3*(K*Rp*Y*delta**2+R*Yx*delta**2-2*R*Y*delta)
            +K*Y**2+2*k*Y*Yx
            -9*(K*sp*delta**4+k*K*spp*delta**4-4*k*sp*delta**3)
            -12*(1-2*x))

def middle_value(delta,v):
    K=v*delta
    cap=I.rat(13,25)
    if K.lo>cap.hi:return None
    K=K.meet(I(0,cap.hi))
    x=1-delta;k=K*x
    D=normalized(k)
    Y=2+delta**2*(3*D['s']-2)
    return 3*D['R']*Y*delta+v*x*Y**2-9*v*x*D['sp']*delta**4-12*x

def T_value(K,z,derivative=False):
    x=1-K*z;k=K*x
    D=normalized(k)
    s,sp,spp,R,Rp=[D[n] for n in ['s','sp','spp','R','Rp']]
    Z=I.rat(2,3)+K**2*z**2*(s-I.rat(2,3))
    value=K*R*Z*z**2+x*Z**2-K**4*x*sp*z**4-I.rat(4,3)*x*z
    if not derivative:return value
    Zz=2*K**2*z*(s-I.rat(2,3))-K**4*z**2*sp
    return (K*(-K**2*Rp*Z*z**2+R*Zz*z**2+2*R*Z*z)
            -K*Z**2+2*x*Z*Zz
            -K**4*(-K*sp*z**4-K**2*x*spp*z**4+4*x*sp*z**3)
            -I.rat(4,3)*(x-K*z))

KMAX=F(13,25)
STAGES=[
 {'name':'left_positive','first':[F(0),KMAX],'second':[F(0),F(3,10)],'sign':1},
 {'name':'first_turn_decreasing','first':[F(0),KMAX],'second':[F(3,10),F(2,5)],'sign':-1},
 {'name':'middle_negative','first':[F(0),F(3,5)],'second':[F(0),F(5,2)],'sign':-1},
 {'name':'right_positive','first':[F(0),KMAX],'second':[F(0),F(3,10)],'sign':1},
 {'name':'second_turn_decreasing','first':[F(0),KMAX],'second':[F(3,10),F(2,5)],'sign':-1},
 {'name':'second_far_endpoint_negative','first':[F(0),KMAX],'second':[F(2,5),F(2,5)],'sign':-1},
]

def interval(a,b):return I(I.frac(a).lo,I.frac(b).hi)
def evaluate(name,a,b):
    if name=='left_positive':return M_value(a,b)
    if name=='first_turn_decreasing':return M_value(a,b,True)
    if name=='middle_negative':return middle_value(a,b)
    if name=='right_positive' or name=='second_far_endpoint_negative':return T_value(a,b)
    if name=='second_turn_decreasing':return T_value(a,b,True)
    raise ValueError(name)

def cover(stage):
    alo,ahi=stage['first'];blo,bhi=stage['second']
    pending=[(alo,ahi,blo,bhi,0)]
    leaves=[];nodes=0
    while pending:
        al,ar,bl,br,depth=pending.pop()
        nodes+=1
        assert nodes<300000 and depth<55,(stage['name'],nodes,depth,al,ar,bl,br)
        a=interval(al,ar);b=interval(bl,br)
        try:bound=evaluate(stage['name'],a,b)
        except AssertionError:bound='subdivide'
        method=None
        if bound is None:method='outside_K_cap'
        elif isinstance(bound,I) and ((stage['sign']>0 and bound.lo>0) or (stage['sign']<0 and bound.hi<0)):
            method='strict_positive' if stage['sign']>0 else 'strict_negative'
        if method:
            leaves.append({'first':[str(al),str(ar)],'second':[str(bl),str(br)],
                           'method':method,'bound':bound.json() if isinstance(bound,I) else None})
        else:
            # Bisect relative to the initial side lengths; degenerate second
            # dimensions are left unchanged and become exact 1D partitions.
            wa=(ar-al)/(ahi-alo)
            wb=(br-bl)/(bhi-blo) if bhi>blo else F(0)
            if wa>=wb:
                mid=(al+ar)/2
                pending.append((mid,ar,bl,br,depth+1));pending.append((al,mid,bl,br,depth+1))
            else:
                mid=(bl+br)/2
                pending.append((al,ar,mid,br,depth+1));pending.append((al,ar,bl,mid,depth+1))
        if nodes%5000==0:print(json.dumps({'stage':stage['name'],'nodes':nodes,'pending':len(pending),'leaves':len(leaves)}),flush=True)
    # Coverage comes from the full recursive bisection. Exact rational area
    # is checked here; a separate replay will validate the full tree partition.
    if bhi>blo:
        assert sum((F(v['first'][1])-F(v['first'][0]))*(F(v['second'][1])-F(v['second'][0])) for v in leaves)==(ahi-alo)*(bhi-blo)
    else:
        assert sum(F(v['first'][1])-F(v['first'][0]) for v in leaves)==ahi-alo
    print(json.dumps({'stage':stage['name'],'nodes':nodes,'leaves':len(leaves)}),flush=True)
    return leaves

def main():
    start=dt.datetime.now(dt.timezone.utc)
    rows=[]
    for stage in STAGES:
        rows.append({'name':stage['name'],'first':[str(x) for x in stage['first']],
                     'second':[str(x) for x in stage['second']],'sign':stage['sign'],
                     'leaves':cover(stage)})
    source=Path(__file__)
    out={'status':'Author exact-interval computation, independent review pending',
         'started_utc':start.isoformat(),'completed_utc':dt.datetime.now(dt.timezone.utc).isoformat(),
         'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
         'base_engine_sha256':hashlib.sha256(Path(m.__file__).read_bytes()).hexdigest(),
         'precision_bits':m.PREC,'E_p_degree':N,'K_cap':str(KMAX),
         'scope':'Two turns of R_stat for all 0<K<=13/25, including K->0 charts',
         'no_floating_point':True,'stages':rows}
    dest=source.with_name('GLOBAL_MIXED_TURN_CERTIFICATE.json')
    dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'certificate':str(dest),'sha256':hashlib.sha256(dest.read_bytes()).hexdigest(),
                      'bytes':dest.stat().st_size,'leaves':sum(len(s['leaves']) for s in rows),
                      'completed_utc':out['completed_utc']}),flush=True)

if __name__=='__main__':main()
