"""Exact integer interval certificate for the last mixed crossing.

All transcendental enclosures use positive Taylor series with explicit rational
remainders. No binary floating-point arithmetic, mpmath, or numerical sign guess
is used in the certificate. Mathematical status remains author-only until review.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import datetime as dt
import hashlib
import json
import math

PREC=160
SCALE=1<<PREC
EXP_N=96
LOG_N=96

def ceildiv(a,b):
    if b<0:a,b=-a,-b
    assert b>0
    return -((-a)//b)

@dataclass(frozen=True)
class I:
    lo:int
    hi:int
    def __post_init__(self):assert self.lo<=self.hi
    @staticmethod
    def rat(p,q=1):
        if q<0:p,q=-p,-q
        return I((p*SCALE)//q,ceildiv(p*SCALE,q))
    @staticmethod
    def frac(x):return I.rat(x.numerator,x.denominator)
    def __add__(self,other):
        other=as_i(other)
        return I(self.lo+other.lo,self.hi+other.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,other):return self+-as_i(other)
    def __rsub__(self,other):return as_i(other)+-self
    def __mul__(self,other):
        other=as_i(other)
        endpoints=[a*b for a in [self.lo,self.hi] for b in [other.lo,other.hi]]
        return I(min(endpoints)//SCALE,ceildiv(max(endpoints),SCALE))
    __rmul__=__mul__
    def inv(self):
        assert not self.lo<=0<=self.hi,('division by zero enclosure',self)
        return I((SCALE*SCALE)//self.hi,ceildiv(SCALE*SCALE,self.lo))
    def __truediv__(self,other):return self*as_i(other).inv()
    def __rtruediv__(self,other):return as_i(other)*self.inv()
    def __pow__(self,n):
        assert n>=0
        result=as_i(1)
        for _ in range(n):result=result*self
        return result
    def meet(self,other):
        lo=max(self.lo,other.lo); hi=min(self.hi,other.hi)
        assert lo<=hi,('contradictory interval enclosures',self,other)
        return I(lo,hi)
    def json(self):return {'lo':str(self.lo),'hi':str(self.hi),'scale_bits':PREC}

def as_i(x):
    if isinstance(x,I):return x
    if isinstance(x,F):return I.frac(x)
    assert isinstance(x,int)
    return I.rat(x)

ONE=as_i(1)
ZERO=as_i(0)
EXP_TAIL=ceildiv(9*(2**(EXP_N+1))*SCALE,math.factorial(EXP_N+1))
LOG_TAIL=ceildiv(9*SCALE,4*(2*LOG_N+1)*3**(2*LOG_N+1))

@lru_cache(maxsize=None)
def exp_point(p):
    assert 0<=p<=2*SCALE,('exp input exceeds proved remainder range',p)
    x=I(p,p)
    term=ONE; total=ONE
    for j in range(1,EXP_N+1):
        term=term*x/j
        total=total+term
    return I(total.lo,total.hi+EXP_TAIL)

def exp_i(x):return I(exp_point(x.lo).lo,exp_point(x.hi).hi)

def log_unit(y):
    assert SCALE<=y.lo<=y.hi<=2*SCALE
    z=(y-1)/(y+1)
    z2=z*z
    term=z; total=ZERO
    for j in range(LOG_N):
        total=total+term/(2*j+1)
        term=term*z2
    return I(2*total.lo,2*total.hi+LOG_TAIL)

LOG2=log_unit(as_i(2))

@lru_cache(maxsize=None)
def log_point(p):
    assert p>0
    n=p.bit_length()-1-PREC
    if n<=0:y=I(p<<(-n),p<<(-n))
    else:y=I(p//(1<<n),ceildiv(p,1<<n))
    return log_unit(y)+n*LOG2

def log_i(x):
    assert x.lo>0,('log nonpositive enclosure',x)
    return I(log_point(x.lo).lo,log_point(x.hi).hi)

@lru_cache(maxsize=None)
def point_data(p):
    t=I(p,p)
    A=exp_i(t)-1
    q=t/A
    d=1-q
    s=1-d/t
    w=-log_i(q)
    g=w-d
    gp=s*d
    return {'q':q,'d':d,'s':s,'w':w,'g':g,'gp':gp}

def data(t):
    left=point_data(t.lo); right=point_data(t.hi)
    q=I(right['q'].lo,left['q'].hi)        # q strictly decreasing
    d=1-q
    out={'q':q,'d':d}
    for name in ['s','w','g','gp']:        # proved strictly increasing
        out[name]=I(left[name].lo,right[name].hi)
    # Analytic whole-domain bound 0 < s' <= 1/12, proved in accompanying note.
    sp=I(0,ceildiv(SCALE,12))
    out['sp']=sp
    out['gpp']=sp*d+out['s']*out['s']*q
    return out

def scalar(K,x,second=False):
    k=K*x
    DK=data(K); Dk=data(k)
    delta=DK['g']-Dk['g']
    assert delta.lo>0
    r0=exp_i(DK['g'])-1
    v=Dk['w']-DK['g']
    a=2*K*x*x/(3*(1-x))
    W=a+log_i(delta)-log_i(Dk['q'])-log_i(r0)
    ak=I.rat(2,3)*(1/(1-x)**2-1)
    Wx=K*(ak+Dk['s']-Dk['gp']/delta)
    out={'v':v,'W':W,'Wx':Wx}
    if second:
        akk=4/(3*K*(1-x)**3)
        out['Wxx']=K*K*(akk+Dk['sp']-Dk['gpp']/delta-Dk['gp']**2/delta**2)
    return out

KL=F(519,1000)
KU=F(13,25)
XL=F(1,10)
XR=F(9,10)
CL=F(1,2)
CR=F(11,20)
KBOX=I(I.frac(KL).lo,I.frac(KU).hi)

def x_interval(a,b):return I(I.frac(a).lo,I.frac(b).hi)
def box_json(a,b):return {'x_lo':str(a),'x_hi':str(b)}
def certify_cover(a,b,kind):
    pending=[(a,b,0)]
    leaves=[]; nodes=0
    while pending:
        l,r,depth=pending.pop()
        nodes+=1
        assert nodes<100000 and depth<40,('coverage resource boundary',kind,l,r,depth)
        x=x_interval(l,r)
        K=I.frac(KU) if kind=='upper_value' else KBOX
        vals=scalar(K,x,second=(kind=='core_convexity'))
        proof=None; bound=None
        if kind=='upper_value':
            if vals['v'].hi<=0:proof='inadmissible';bound=vals['v']
            else:
                mid=(l+r)/2
                center=scalar(K,I.frac(mid))['W']
                refined=vals['W'].meet(center+vals['Wx']*(x-I.frac(mid)))
                if refined.lo>0:proof='strict_positive_W';bound=refined
        elif kind=='outside_core_stationary':
            if vals['v'].hi<=0:proof='inadmissible';bound=vals['v']
            elif vals['W'].lo>0 or vals['W'].hi<0:proof='W_excludes_zero';bound=vals['W']
            elif vals['Wx'].lo>0 or vals['Wx'].hi<0:proof='Wx_excludes_zero';bound=vals['Wx']
        elif kind=='core_convexity':
            if vals['Wxx'].lo>0 and vals['v'].lo>0:
                proof='strict_positive_Wxx_and_admissible';bound=vals['Wxx']
        else:raise ValueError(kind)
        if proof:
            leaf={**box_json(l,r),'method':proof,'bound':bound.json()}
            if kind=='core_convexity':leaf['admissible_v']=vals['v'].json()
            leaves.append(leaf)
        else:
            m=(l+r)/2
            pending.append((m,r,depth+1));pending.append((l,m,depth+1))
    ordered=sorted(leaves,key=lambda p:F(p['x_lo']))
    assert F(ordered[0]['x_lo'])==a and F(ordered[-1]['x_hi'])==b
    assert all(F(left['x_hi'])==F(right['x_lo']) for left,right in zip(ordered,ordered[1:]))
    assert sum(F(p['x_hi'])-F(p['x_lo']) for p in leaves)==b-a
    print(json.dumps({'stage':kind,'x_interval':[str(a),str(b)],'nodes':nodes,'leaves':len(leaves)}),flush=True)
    return leaves

def main():
    start=dt.datetime.now(dt.timezone.utc)
    rupper=exp_i(data(I.frac(KU))['g'])-1
    gplower=data(I.rat(9,20))['gp']
    low_v=data(I.frac(KU*XL))['w']-data(I.frac(KL))['g']
    log10=log_i(as_i(10))
    assert rupper.hi<I.rat(1,20).lo
    assert gplower.lo>I.rat(11,100).hi
    assert low_v.hi<0
    assert log10.hi<I.rat(5,2).lo
    witness=scalar(I.frac(KL),I.rat(521,1000))
    assert witness['v'].lo>0 and witness['W'].hi<0
    print('exact constant bounds and lower strict-mixed witness verified',flush=True)
    upper=certify_cover(XL,XR,'upper_value')
    outside_left=certify_cover(XL,CL,'outside_core_stationary')
    outside_right=certify_cover(CR,XR,'outside_core_stationary')
    convex=certify_cover(CL,CR,'core_convexity')
    leftder=scalar(KBOX,I.frac(CL))['Wx']
    rightder=scalar(KBOX,I.frac(CR))['Wx']
    assert leftder.hi<0 and rightder.lo>0
    source=Path(__file__)
    out={
      'status':'Author exact-interval control; independent ordinary review pending',
      'started_utc':start.isoformat(),'completed_utc':dt.datetime.now(dt.timezone.utc).isoformat(),
      'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
      'parameters':{'precision_bits':PREC,'exp_degree':EXP_N,'log_terms':LOG_N,
                    'no_floating_point':True,'K_lower':str(KL),'K_upper':str(KU),
                    'compact_x':[str(XL),str(XR)],'core_x':[str(CL),str(CR)]},
      'analytic_dependencies':['NO_ISLANDS.md exact frozen v1','LAST_MIXED_BOUNDARY.md exact frozen v1',
          'q decreasing; s,w,g,g_prime increasing; 0<s_prime<=1/12',
          'analytic low/high x exclusions in CRITICAL_UNIQUENESS_CERTIFICATE.md'],
      'constants':{'r0_Kupper_below_one_twentieth':rupper.json(),
                   'gprime_9_over_20_above_11_over_100':gplower.json(),
                   'low_x_admissibility_upper':low_v.json(),
                   'log10_below_five_halves':log10.json()},
      'lower_witness':{'K':str(KL),'x':'521/1000','W':witness['W'].json(),'v':witness['v'].json()},
      'upper_full_cover':upper,
      'outside_core_left':outside_left,'outside_core_right':outside_right,
      'core_convexity_cover':convex,
      'core_derivatives':{'left_Wx':leftder.json(),'right_Wx':rightder.json()},
      'claim':'Unique last-boundary interior scalar tie, nondegenerate, 519/2000<c_star<13/50',
      'scope_limit':'Does not prove uniqueness of every strict mixed optimizer at arbitrary r',
    }
    dest=source.with_name('CRITICAL_EXACT_INTERVAL_CERTIFICATE.json')
    dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'certificate':str(dest),'sha256':hashlib.sha256(dest.read_bytes()).hexdigest(),
                      'bytes':dest.stat().st_size,'completed_utc':out['completed_utc']}),flush=True)

if __name__=='__main__':main()
