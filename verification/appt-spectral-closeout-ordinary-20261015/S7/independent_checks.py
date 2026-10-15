"""Reviewer-written exact geometry/transport and real-order diagnostics.
No author imports or execution. The universal proof is read separately;
finite samples do not certify optimization over all APPT matrices.
"""
from pathlib import Path
from fractions import Fraction as F
import datetime,hashlib,json,platform,subprocess,sys,traceback
import sympy as sy
import mpmath as mp
R=Path(__file__).resolve().parent
mp.mp.dps=1250

def mm(q):return mp.mpf(q.numerator)/q.denominator if isinstance(q,F) else mp.mpf(q)

def w2sq(law):
    # Exact one-dimensional increasing coupling, with beta mass1/2 at+-1.
    source=sorted((F(x),F(w)) for x,w in law if w)
    assert sum(w for x,w in source)==1
    targets=[(F(-1),F(1,2)),(F(1),F(1,2))]
    j=0;remaining=targets[0][1];cost=F(0)
    for x,amount in source:
        while amount:
            moved=min(amount,remaining)
            cost+=moved*(x-targets[j][0])**2
            amount-=moved;remaining-=moved
            if remaining==0 and j==0:j=1;remaining=targets[1][1]
    assert remaining==0
    return cost

def actual(m,n,raw):
    D=m*n;total={}
    for y,c in raw:
        y=F(y);assert y>=0 and c>=0
        if c:total[y]=total.get(y,0)+c
    parts=sorted(total.items(),reverse=True)
    assert sum(c for y,c in parts)==D
    trace=sum(c*y for y,c in parts);assert trace>0
    ys=[(F(D)*y/trace,c) for y,c in parts]
    assert sum(c*y for y,c in ys)==D
    Q=sum(c*(y-1)**2 for y,c in ys);gamma=F(n,m)
    law=[(m*(y-1),F(c,D)) for y,c in ys]
    assert sum(x*w for x,w in law)==0
    assert sum(x*x*w for x,w in law)==Q/gamma
    R0=m*(m-1)//2;j=D-m*(m+1)//2+1;N=D-m*m+2
    B=[];start=1;yR=None;A0=None
    for y,c in ys:
        count=max(0,min(start+c-1,j)-max(start,R0)+1)
        if count:B.append((y,count))
        if start<=R0<start+c:yR=y
        if start<=j<start+c:A0=y
        start+=c
    assert sum(c for y,c in B)==N and A0>0
    h=m-1;kappa=yR/A0-1;L=h*kappa
    mu=sum(c*y for y,c in B)/N
    theta=(mu/A0-1)/kappa if kappa else F(0)
    zz=[(h*(y/A0-1),c) for y,c in B]
    J=sum(c*z*(L-z) for z,c in zz)/N
    v=L*L*theta*(1-theta)-J
    QB=sum(c*(y-1)**2 for y,c in B);QE=Q-QB
    assert 0<=L<=2 and 0<=theta<=1 and J>=0 and 0<=v<=1
    pref=F(N,D)*F(m,h)**2*A0*A0
    meanterm=F(m*m*N,D)*(mu-1)**2
    assert QB/gamma==pref*v+meanterm
    assert N*(mu-1)==-sum(c*(y-1) for y,c in ys)+sum(c*(y-1) for y,c in B)
    nuB=[(m*(y-1),F(c,N)) for y,c in B]
    xi=m*(mu-1);w=F(m,h)*A0
    assert all(m*(y-1)==xi+w*(z-L*theta) for (y,c),(z,count) in zip(B,zz))
    roundcost=w*w*J
    xlo=xi-w*L*theta;xhi=xi+w*L*(1-theta)
    loccost=(1-theta)*(xlo+1)**2+theta*(xhi-1)**2
    weightcost=4*abs(theta-F(1,2))
    midcost=w2sq(nuB);fullcost=w2sq(law)
    assert midcost<=3*(roundcost+loccost+weightcost)
    exccost=2*QE/gamma+F(2*(D-N),D)
    assert fullcost<=2*exccost+F(2*N,D)*midcost
    q=Q/gamma
    assert (q+1-fullcost)**2<=4*q
    return dict(m=m,n=n,D=D,gamma=gamma,ys=ys,law=law,Q=Q,q=q,QB=QB,QE=QE,
                L=L,theta=theta,J=J,v=v,delta=1-v,W2sq=fullcost,
                pref=pref,meanterm=meanterm,fullrank=ys[-1][0]>0)

def projection(m,n,k):
    D=m*n;c=F(2,m-1)
    assert 0<=k<=D and 1-c*F(m-1,2)==0
    return actual(m,n,[(1+c,k),(1,D-k)])

def spread_state(m):
    n=m*m;D=m*n;assert D%4==0
    c=F(2,m-1)
    # I+Y, 0<=Y<=cI: negative witness trace bound proves APPT for every U.
    return actual(m,n,[(1+c,D//4),(1+c/2,D//2),(1,D//4)])

def sharp(l):
    assert l%2==0 and l>=4
    m=l**4;n=m*m;D=m*n;k=D//2+D//l
    assert k==F(D,2)+F(D,l) and 0<k<D
    return projection(m,n,k)

def fkernel(x,alpha):
    x=mm(x);a=mm(alpha)
    if x==-1:return 1/a
    if a==1:return (1+x)*mp.log1p(x)-x
    return (mp.expm1(a*mp.log1p(x))-a*x)/(a*(a-1))

def scaled_entropy(st,alpha):
    a=mm(alpha)
    Fsum=mp.fsum(c*fkernel(y-1,alpha) for y,c in st['ys'])
    if a==1:e=Fsum/st['D']
    else:e=mp.log1p(a*(a-1)*Fsum/st['D'])/(a-1)
    return 2*st['m']**2*e/a

def wrong(name):
    if name=='bounded_kernel_without_alpha':
        assert fkernel(-1,F(1,10**20))<=1000,'WRONG bounded_kernel_without_alpha'
    elif name=='omit_middle_mean':
        st=actual(8,64,[(1,511),(0,1)])
        assert st['QB']/st['gamma']==st['pref']*st['v'],'WRONG omit_middle_mean'
    elif name=='width_mean_without_spread':
        st=spread_state(64)
        assert st['L']==2 and abs(st['theta']-F(1,2))<F(1,100)
        assert st['q']==1,'WRONG width_mean_without_spread'
    elif name=='half_power_stability':
        st=sharp(64);eps=F(2,st['m'])
        assert st['W2sq']<=4*(1-st['q']+eps),'WRONG half_power_stability'
    elif name=='fractional_rank_is_integer':
        l=5;D=l**12;k=F(D,2)+F(D,l)
        assert k.denominator==1,'WRONG fractional_rank_is_integer'
    elif name=='drop_alpha_gamma_hypothesis':
        m=32;D=m**3;q=F(m*m,D-1)
        rigorous_scaled_entropy_lower=2*m
        assert rigorous_scaled_entropy_lower<=q+1,'WRONG drop_alpha_gamma_hypothesis'
    elif name=='omit_trace_denominator':
        m=16;n=256;D=m*n;c=F(2,m-1);k=D//2
        assert k*(1+c)+D-k==D,'WRONG omit_trace_denominator'
    else:raise ValueError(name)

def checks(folder):
    counts={};details={}
    L,theta,J,s=sy.symbols('L theta J s')
    assert sy.expand((L*L*theta-J)-(L*theta)**2-(L*L*theta*(1-theta)-J))==0
    assert sy.expand(1-(L*L*theta*(1-theta)-J)-(1-L*L/4+L*L*(theta-sy.Rational(1,2))**2+J))==0
    cost=(1-theta)*(1-s*theta)**2+(theta-sy.Rational(1,2))*(1+s*(1-theta))**2+sy.Rational(1,2)*(s*(1-theta)-1)**2
    assert sy.expand(cost-(1+s*s*theta*(1-theta)-2*s*(1-theta)))==0
    l,m=sy.symbols('l m',positive=True)
    assert sy.simplify((2*m/(m+2/l))**2*(sy.Rational(1,4)-1/l**2)-(1-4/l**2)/(1+2/(l*m))**2)==0
    alpha,y=sy.symbols('alpha y',positive=True)
    kernel=(y**alpha-1-alpha*(y-1))/(alpha*(alpha-1))
    assert sy.simplify(sy.limit(kernel,alpha,1)-(y*sy.log(y)-y+1))==0
    counts['symbolic_identities']=5

    exact=0
    for m in [8,16,32,64]:
        for gamma in [2,8,m]:
            n=gamma*m;D=m*n
            for rank in [1,D//3,D//2,3*D//5,D-1]:
                projection(m,n,rank);exact+=1
            actual(m,n,[(1,D-1),(0,1)]);exact+=1
            actual(m,n,[(3,1),(1,D-1)]);exact+=1
        spread_state(m);exact+=1
    counts['exact_actual_spectrum_geometry_transport_cases']=exact

    sharp_rows=[];orders=[F(1,3),F(1,2),F(1),F(2),F(7,2)]
    for l in [4,6,10,18,32,64]:
        st=sharp(l);m=st['m'];theta=F(1,2)+F(1,l);s=F(2*m)/(m+F(2,l))
        assert st['q']==(1-F(4,l*l))/(1+F(2,l*m))**2
        assert st['W2sq']==1+st['q']-2*s*(1-theta)
        assert abs(st['q']-(1-F(4,l*l)))<=F(4,l**5)
        assert abs(st['W2sq']-(F(4,l)-F(4,l*l)))<=F(10,l**5)
        es=[]
        for order in orders:
            value=scaled_entropy(st,order)
            # Flat physical states have bounded-order Taylor error O(1/m).
            assert abs(value-mm(st['q']))<mp.mpf(100)/m
            es.append({'order':str(order),'actual_entropy_scaled':mp.nstr(value,25)})
        sharp_rows.append({'l':l,'q':str(st['q']),'W2_squared':str(st['W2sq']),
                           'entropy_diagnostics':es,'exact_integer_rank':True,
                           'not_finite_optimum':'No actual E evaluated; d expansion comes from the universal proof'})
    counts['actual_sharpness_examples']=len(sharp_rows)
    counts['sharpness_real_order_entropy_diagnostics']=len(sharp_rows)*len(orders)
    details['sharpness']=sharp_rows

    real=0
    allorders=[F(1,10**1000),F(1,10**40),F(1,7),F(1,2),
               F(1)-F(1,10**60),F(1),F(1)+F(1,10**60),F(2),F(11,2)]
    for m in [1024,4096]:
        for order in allorders:
            gamma=(10000*order.denominator+order.numerator-1)//order.numerator
            n=m*gamma;D=m*n
            samples=[projection(m,n,D//2),projection(m,n,3*D//5),
                     actual(m,n,[(1,D-1),(0,1)]),actual(m,n,[(3,1),(1,D-1)])]
            for st in samples:
                value=scaled_entropy(st,order)
                epsilon=mp.mpf(1)/m+1/(mm(order)*gamma)
                assert abs(value-mm(st['q']))<=mp.mpf(1000000)*epsilon
                for y,count in st['ys']:
                    x=y-1;f=fkernel(x,order)
                    assert f>=-mp.mpf('1e-1100')
                    assert f<=mp.mpf(243)*mm(x*x)/mm(order)+mp.mpf('1e-1100')
                real+=1
    counts['actual_joint_order_entropy_kernel_diagnostics_including_1e_1000_and_alpha1']=real

    bad=[]
    for name in ['bounded_kernel_without_alpha','omit_middle_mean','width_mean_without_spread',
                 'half_power_stability','fractional_rank_is_integer',
                 'drop_alpha_gamma_hypothesis','omit_trace_denominator']:
        p=subprocess.run([sys.executable,str(Path(__file__).resolve()),'--wrong',name],capture_output=True,text=True)
        (folder/(name+'.stdout.txt')).write_text(p.stdout)
        (folder/(name+'.stderr.txt')).write_text(p.stderr)
        assert p.returncode!=0 and 'AssertionError: WRONG '+name in p.stderr,(name,p.returncode,p.stderr)
        bad.append({'variant':name,'returncode':p.returncode,'intended_assertion_error':True})
    return counts,details,bad

def main():
    utc=datetime.datetime.now(datetime.timezone.utc);folder=R/'runs'/utc.strftime('%Y%m%dT%H%M%S.%fZ')
    folder.mkdir(parents=True);source=Path(__file__).read_bytes();(folder/'independent_checks.py').write_bytes(source)
    result={'utc':utc.isoformat(),'status':'RUNNING','source_sha256':hashlib.sha256(source).hexdigest(),
            'paper_sha256':'3701fa925c3c4098961c227768f62915e9cf388bdafea5918a638ce2b7963a9f',
            'runtime':{'python':platform.python_version(),'sympy':sy.__version__,'mpmath':mp.__version__,'mp_dps':mp.mp.dps},
            'author_program_imported_or_executed':False,
            'scope':'Independent exact transport/physical-family and finite real-order diagnostics; no global optimizer computation or Lean'}
    try:
        c,d,bad=checks(folder);result.update(status='PASS',counts=c,details=d,actual_rejected_wrong_variants=bad)
    except Exception:
        result.update(status='FAIL',unexpected_failure=traceback.format_exc())
        (folder/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');raise
    result['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
    (folder/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
    (R/'LATEST_RUN.json').write_text(json.dumps({'run':str(folder),'source_sha256':result['source_sha256']},indent=2)+'\n')
    print(json.dumps({'status':'PASS','run':str(folder),'counts':c,'rejected_variants':len(bad)},indent=2))

if __name__=='__main__':
    if len(sys.argv)==3 and sys.argv[1]=='--wrong':wrong(sys.argv[2])
    else:main()
