#!/usr/bin/env python3
"""Author finite controls for H0-H4; no independent or formal certificate.

Every execution keeps its own immutable source snapshot and raw result.
Fraction matrix checks, symbolic identities, and high-precision algebraic
comparisons complement (and do not replace) the all-domain written proof.
"""
from pathlib import Path
from fractions import Fraction as F
from datetime import datetime, timezone
import hashlib, json, sys, traceback
import sympy as sp
from mpmath import mp

stage = Path(__file__).resolve().parent
run = stage / 'control-runs' / datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
run.mkdir(parents=True, exist_ok=False)
for name in ('PAPER.md', 'THEOREM_MAP.md', 'FOLLOWUP_TARGET.md', 'checks.py'):
    (run / name).write_bytes((stage / name).read_bytes())
result = {'utc_start': datetime.now(timezone.utc).isoformat(),
          'author_only': True, 'independent_review': False, 'Lean': False,
          'source_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                            for p in run.iterdir() if p.is_file()},
          'groups': {}, 'status': 'RUNNING'}
def save():
    (run / 'RESULT.json').write_text(json.dumps(result, indent=2)+'\n')
def group(name, f):
    print('START '+name, flush=True)
    result['groups'][name] = f()
    save()
    print('PASS '+name, flush=True)
def require(test, reason):
    if not test:
        raise AssertionError(reason)
def small(value):
    return mp.nstr(value, 32)

def symbolic():
    m,z,c,p,b = sp.symbols('m z c p b', positive=True)
    kap = 2/(m-1+z); a=2+kap
    pp=a*z/(z+2); bb=a*z/(2*(1+z))
    def eq(x,y): require(sp.factor(x-y)==0, str(x-y))
    eq(1-bb,(m-1)/((m-1+z)*(1+z)))
    cp=2*kap*m*m*pp/((m-1)*(a-pp))
    cb=2*kap*m*m*bb/((m-1)*(a-2*bb))
    cost=2*m*m*z/((m-1)*(m-1+z))
    eq(cp,cost); eq(cb,cost)
    eq(m/a+2*pp/(a*(a-pp)),(m+z)/a)
    eq(m/a+2*bb/(a*(a-2*bb)),(m+z)/a)
    eq(kap*(m+z)/a,1)
    rr=2/(m-1)-c/(m*m); aa=2+rr
    cpp=2*rr*m*m*p/((m-1)*(aa-p))
    cbb=2*rr*m*m*b/((m-1)*(aa-2*b))
    eq(sp.diff(c-cpp,c),1+2*p*(2-p)/((m-1)*(aa-p)**2))
    eq(sp.diff(c-cbb,c),1+4*b*(1-b)/((m-1)*(aa-2*b)**2))
    k,D,Q,H,h,alpha,L=sp.symbols('k D Q H h alpha L', positive=True)
    r=sp.symbols('r',positive=True); S=D+r*k+h; A=D+Q*k+H
    star=(Q*(D+h)-alpha*r*(D+H))/((alpha-1)*r*Q)
    eq(sp.diff((sp.log(A/D)-alpha*sp.log(S/D))/(alpha-1),k),
       r*Q*(star-k)/(A*S))
    star1=((L-r)*(D+h)-r*H)/(r*r)
    eq(sp.diff((k*L+H)/S-sp.log(S/D),k),r*r*(star1-k)/(S*S))
    u=sp.symbols('u', real=True)
    P=50*u**3-50*u**2-141*u+159
    require(sp.discriminant(P,u)==-7765800,'half-order positive discriminant')
    v=(sp.sqrt(5)-1)/2
    eq(2*v**5,5*sp.sqrt(5)-11); eq(2/v,1+sp.sqrt(5))
    eq(v/(1-v),(1+sp.sqrt(5))/2)
    vv=sp.symbols('v',positive=True)
    derivative=sp.factor(sp.diff(2*vv**2*(1-vv)/(1+vv),vv))
    eq(derivative,-4*vv*(vv**2+vv-1)/(vv+1)**2)
    eq(5-F(559,250)**2,F(19,62500))
    return {'exact_symbolic_identities':15,
            'negative_ratio_derivative':str(derivative),
            'positive_cubic_discriminant':-7765800,
            'half_critical':str(5*sp.sqrt(5)-11)}

def inverse(A):
    n=len(A); aug=[list(A[i])+[F(i==j) for j in range(n)] for i in range(n)]
    for j in range(n):
        pivot=next(i for i in range(j,n) if aug[i][j])
        aug[j],aug[pivot]=aug[pivot],aug[j]
        denom=aug[j][j]; aug[j]=[v/denom for v in aug[j]]
        for i in range(n):
            if i!=j:
                f=aug[i][j]
                aug[i]=[x-f*y for x,y in zip(aug[i],aug[j])]
    return [row[n:] for row in aug]
def pd(A):
    # Exact successive Schur complements, with no numerical eigenvalue tolerance.
    B=[list(row) for row in A]
    while B:
        d=B[0][0]
        if d<=0:return False
        B=[[B[i][j]-B[i][0]*B[0][j]/d for j in range(1,len(B))]
           for i in range(1,len(B))]
    return True
def psd(A):
    B=[list(row) for row in A]
    while B:
        if B[0][0]==0:
            if any(B[0]):return False
            B=[row[1:] for row in B[1:]]
        else:
            d=B[0][0]
            if d<0:return False
            B=[[B[i][j]-B[i][0]*B[0][j]/d for j in range(1,len(B))]
               for i in range(1,len(B))]
    return True
def base(m,a,P):return [[a*F(i==j)-P[i][j] for j in range(m)] for i in range(m)]
def walk_cost(m,a,P):return sum(map(sum,inverse(base(m,a,P))))-F(m)/a

def fraction_controls():
    exact=0; patterns=0; tiny=0
    for m in (3,5,7):
        for z in (F(1,2),F(8,5),F(2),F(4)):
            kap=F(2,m-1+z); a=2+kap
            p=a*z/(z+2); b=a*z/(2*(1+z))
            for s in ('positive','negative-diagonal','negative-edge'):
                positions=[(i,j) for i in range(m) for j in range(i+1,m)] if s!='negative-diagonal' else [(i,i) for i in range(m)]
                for i,j in positions:
                    P=[[F(0) for _ in range(m)] for _ in range(m)]
                    if i==j:P[i][i]=2*b
                    else:P[i][j]=P[j][i]=p if s=='positive' else b
                    B=base(m,a,P); M=[[B[ii][jj]-kap for jj in range(m)] for ii in range(m)]
                    require(pd(B),'boundary base not positive definite')
                    require(psd(M),'actual single-head adverse pattern not PSD')
                    invsum=sum(map(sum,inverse(B)))
                    if s!='negative-edge':require(kap*invsum==1,'boundary equality missing')
                    else:require(kap*invsum<1,'negative edge no strict slack')
                    exact+=1; patterns+=1
    # Fill every positive edge and every negative edge/diagonal slot with
    # omitted mass. Distinct signs may share an off-diagonal matrix entry.
    for m in (6,9):
        for sign in ('positive','negative'):
            for exponent in (6,30,80):
                a=F(2)+F(2,m+1)
                retained=F(1) if sign=='positive' else F(3,5)
                P0=[[F(0) for _ in range(m)] for _ in range(m)]
                if sign=='positive':P0[0][1]=P0[1][0]=retained
                else:P0[0][0]=2*retained
                P=[row[:] for row in P0]; tau=F(1,10**exponent)
                slots=[]
                for i in range(m):
                    for j in range(i+1,m):
                        if not (sign=='positive' and (i,j)==(0,1)):slots.append((i,j,'positive'))
                for i in range(m):
                    for j in range(i,m):
                        if not (sign=='negative' and (i,j)==(0,0)):slots.append((i,j,'negative'))
                mass=tau/len(slots)
                for i,j,s in slots:
                    if i==j:P[i][i]+=2*mass
                    else:P[i][j]+=mass; P[j][i]+=mass
                require(pd(base(m,a,P)),'dense tiny tail lost protected inverse')
                require(walk_cost(m,a,P)>=walk_cost(m,a,P0)+2*tau/(a*a),
                        'full-slot first walk omitted mass')
                tiny+=1
    # A negative edge test alone is a strictly weaker physical condition.
    m=5; z=F(1,2); kap=F(2,m-1+z); a=2+kap; b=a*z/(z+2)
    diag=[[F(0) for _ in range(m)] for _ in range(m)]; diag[0][0]=2*b
    edge=[[F(0) for _ in range(m)] for _ in range(m)]; edge[0][1]=edge[1][0]=b
    require(kap*sum(map(sum,inverse(base(m,a,edge))))==1,'edge mutation calibration')
    require(kap*sum(map(sum,inverse(base(m,a,diag))))>1,'omitted diagonal mutation not rejected')
    # Trace reweighting for a raw body cube mixture.
    q=F(3,2); p=F(2,3)
    v0=[q+p,q,F(1),F(1)]; v1=[q+p,q,q,F(1)]
    raw=[(x+y)/2 for x,y in zip(v0,v1)]; S=sum(raw)
    weights=[sum(v0)/(2*S),sum(v1)/(2*S)]
    for i in range(4):
        correct=weights[0]*v0[i]/sum(v0)+weights[1]*v1[i]/sum(v1)
        require(correct==raw[i]/S,'trace-weighted normalized cube identity')
    require(any(raw[i]/S!=(v0[i]/sum(v0)+v1[i]/sum(v1))/2 for i in range(4)),
            'unweighted normalized mixture mutation not rejected')
    return {'exact_boundary_position_cases':exact,'all_edge_diagonal_patterns':patterns,
            'dense_full_slot_tiny_mass_cases':tiny,'smallest_exact_total_mass':'1e-80',
            'rejected_mutations':['negative-edge-only APPT sufficiency',
                                  'unweighted normalized cube mixture']}

mp.dps=240
def entropy(alpha,hist,D):
    S=mp.fsum(v*n for v,n in hist)
    if alpha==1:
        return mp.fsum(v*mp.log(v)*n for v,n in hist)/S-mp.log(S/D)
    A=mp.fsum(v**alpha*n for v,n in hist)
    return (mp.log(A/D)-alpha*mp.log(S/D))/(alpha-1)
def head_hist(r,u,sign,D,body):
    H=[(1+r*theta,count) for theta,count in body]
    raw=(1+r+u) if sign=='positive' else (1-u)
    old=(1+r) if sign=='positive' else mp.mpf(1)
    # Signed multiplicities allow exact head/tail replacement in moments.
    return H+[(old,-1),(raw,1)]
def ranked(alpha,m,D,z,sign,k):
    r=mp.mpf(2)/(m-1+z); q=1+r; a=2+r
    u=a*z/(z+2) if sign=='positive' else a*z/(2*(1+z))
    hist=[(q,k),(mp.mpf(1),D-k)]
    hist += [(q,-1),(q+u,1)] if sign=='positive' else [(mp.mpf(1),-1),(1-u,1)]
    return entropy(alpha,hist,D)
def real_rank(alpha,m,D,z,sign):
    r=mp.mpf(2)/(m-1+z); q=1+r; a=2+r
    u=a*z/(z+2) if sign=='positive' else a*z/(2*(1+z))
    h=u if sign=='positive' else -u
    if alpha==1:
        L=q*mp.log(q)
        H=(q+u)*mp.log(q+u)-q*mp.log(q) if sign=='positive' else (1-u)*mp.log(1-u)
        return ((L-r)*(D+h)-r*H)/(r*r)
    Q=mp.expm1(alpha*mp.log(q))
    H=(q+u)**alpha-q**alpha if sign=='positive' else (1-u)**alpha-1
    return (Q*(D+h)-alpha*r*(D+H))/((alpha-1)*r*Q)

def rank_controls():
    # Full enumeration of the *stated finite family*, not the quantum feasible set.
    m=5; D=600; R=m*(m-1)//2; K=m*(m+1)//2
    cases=0; nearest_example=None
    for alpha in map(mp.mpf,('.1','.5','1','1.5','2','3')):
        for z in map(mp.mpf,('.5','1.6','2','4')):
            for sign in ('positive','negative'):
                ks=real_rank(alpha,m,D,z,sign)
                k0=max(R,min(D-K,int(mp.floor(ks)))); k1=max(R,min(D-K,int(mp.ceil(ks))))
                allvals=[(ranked(alpha,m,D,z,sign,k),k) for k in range(R,D-K+1)]
                vmax=max(v for v,k in allvals)
                winners={k for v,k in allvals if abs(v-vmax)<mp.mpf('1e-210')}
                require(winners.issubset({k0,k1}),'rank derivative omitted a true integer winner')
                cases+=1
    # Calibrate a real rank just below a half integer. The exact comparison
    # may prefer the more distant ceiling, and must never use nearest alone.
    alpha=mp.mpf(2); sign='positive'
    zs=[mp.mpf('.5')+mp.mpf('3.5')*j/100 for j in range(101)]
    for lo,hi in zip(zs,zs[1:]):
        a=real_rank(alpha,m,D,lo,sign); b=real_rank(alpha,m,D,hi,sign)
        for j in range(int(mp.floor(min(a,b))),int(mp.ceil(max(a,b)))+1):
            target=mp.mpf(j)+mp.mpf('.49999')
            if min(a,b)<target<max(a,b):
                l,h=lo,hi
                for _ in range(190):
                    mid=(l+h)/2; f=real_rank(alpha,m,D,mid,sign)-target
                    if (a-target)*f>0:l=mid
                    else:h=mid
                z=(l+h)/2; ks=real_rank(alpha,m,D,z,sign)
                if ranked(alpha,m,D,z,sign,j+1)>ranked(alpha,m,D,z,sign,j):
                    nearest_example={'m':m,'D':D,'alpha':'2','sign':sign,'z':small(z),
                                     'real_rank':small(ks),'nearest':j,'actual_winner':j+1}
                    break
        if nearest_example:break
    require(nearest_example is not None,'nearest-only rank mutation witness not found')
    return {'complete_integer_enumeration_cases':cases,'integer_values_compared':cases*(D-K-R+1),
            'arithmetic_decimal_digits':mp.dps,'nearest_only_counterexample':nearest_example,
            'scope':'enumeration within one-head families only, not full APPT search'}

def relative_controls():
    cases=0; min_gain_ratio=mp.inf; max_removal_ratio=-mp.inf
    min_strict_margin=mp.inf; nearone_cases=0
    orders=list(map(mp.mpf,('.1','.5','1','1.5','2','3')))+[1-mp.mpf('1e-20'),1+mp.mpf('1e-20')]
    for alpha in orders:
        for m in (50,500,5000):
            # These algebraic comparisons use a cubic-sized actual integer D;
            # localization assumptions are supplied analytically, not inferred
            # from a finite scan at a guessed d_alpha.
            n=max(m,int(mp.mpf('.18')*m*m)); D=m*n
            R=m*(m-1)//2; K=m*(m+1)//2
            upper=D//2; lower=D-upper-5
            body=[(mp.mpf(1),upper),(mp.mpf(0),lower),
                  (mp.mpf(1)/3,2),(mp.mpf(2)/3,3)]
            require(upper>=R and lower>=K,'physical body counts')
            for sign in ('positive','negative'):
                z=mp.mpf(2) if sign=='positive' else mp.mpf('1.6')
                r0=mp.mpf(2)/(m-1+z); a0=2+r0
                u=a0*z/(z+2) if sign=='positive' else a0*z/(2*(1+z))
                for exponent in (4,30,100):
                    tau=mp.mpf(10)**(-exponent); r=r0-50*tau/(m*m)
                    H0=head_hist(r0,u,sign,D,body); H=head_hist(r,u,sign,D,body)
                    X=H[:]
                    # Nineteen removed heads include both signs and trace cancellation.
                    rest=[]
                    for j in range(19):
                        mass=tau/19
                        old=1+r if j%2==0 else mp.mpf(1)
                        changed=old+mass if j%2==0 else old-mass
                        X.extend([(old,-1),(changed,1)]); rest.append(mass)
                    removal=D*(entropy(alpha,X,D)-entropy(alpha,H,D))
                    gain=D*(entropy(alpha,H0,D)-entropy(alpha,H,D))
                    derivative=mp.diff(lambda v:entropy(alpha,head_hist(v,u,sign,D,body),D),r)
                    mu=mp.fsum(th*ct for th,ct in body)/D
                    nu=mp.fsum(th*th*ct for th,ct in body)/D
                    var=nu-mu*mu
                    require(var>mp.mpf('.24'),'near-optimal body variance missing')
                    require(derivative>=alpha*r/8,'localized body derivative lower')
                    require(gain>removal,'relative deformation not strictly improving')
                    require(abs(removal/tau)<3*alpha*(r+tau+mp.mpf(1)/D),
                            'relative tiny-tail trace cancellation lost')
                    require(gain/(50*tau)>alpha*mp.mpf('.18')/9,'finite gain has missing normalization')
                    min_gain_ratio=min(min_gain_ratio,derivative/(alpha*r/8))
                    max_removal_ratio=max(max_removal_ratio,abs(removal/tau))
                    min_strict_margin=min(min_strict_margin,(gain-removal)/tau)
                    cases+=1
                    if alpha!=1 and abs(alpha-1)<mp.mpf('1e-19'):nearone_cases+=1
    # An actual feasible boundary body with only its mandatory upper count is
    # unprofitable; a derivative lower for arbitrary bodies would be false.
    m=500; n=45000; D=m*n; R=m*(m-1)//2; z=mp.mpf(2)
    r=mp.mpf(2)/(m-1+z); p=(2+r)*z/(z+2)
    body=[(mp.mpf(1),R),(mp.mpf(0),D-R)]
    der=mp.diff(lambda v:entropy(mp.mpf(2),head_hist(v,p,'positive',D,body),D),r)
    require(der<2*r/8,'unconditional body derivative mutation not rejected')
    # Wrong trace sign in the negative branch must be separated from actual normalization.
    m=50; D=22500; z=mp.mpf('1.6'); k=D//2; r=mp.mpf(2)/(m-1+z)
    b=(2+r)*z/(2*(1+z)); S=D+r*k-b; A=(1+r)**mp.mpf('.5')*k+D-k-1+(1-b)**mp.mpf('.5')
    correct=(mp.log(A/D)-mp.mpf('.5')*mp.log(S/D))/(-mp.mpf('.5'))
    wrong=(mp.log(A/D)-mp.mpf('.5')*mp.log((D+r*k+b)/D))/(-mp.mpf('.5'))
    require(abs(correct-wrong)>mp.mpf('1e-6'),'negative trace-sign mutation not rejected')
    return {'relative_full_moment_cases':cases,'near_alpha_one_cases':nearone_cases,
            'smallest_total_tail_mass':'1e-100','arithmetic_decimal_digits':mp.dps,
            'minimum_derivative_over_localized_lower':small(min_gain_ratio),
            'maximum_absolute_removed_score_per_mass':small(max_removal_ratio),
            'minimum_strict_gain_minus_loss_per_mass':small(min_strict_margin),
            'rejected_mutations':['unconditional near-flat-body contrast derivative',
                                  'positive trace increment for negative head'],
            'scope':'full normalized algebra under body-variance and budget assumptions; not a full feasible-set search'}

def half_followup():
    # Symbolic exact stationary trace and the coefficient expansions are
    # computed independently from the entropy code in rank_controls.
    w,v,D=sp.symbols('w v D',positive=True)
    kap=w*w-1; Q=w-1; h=v*v-1; H=v-1
    star=(kap*(D+H)-2*Q*(D+h))/(kap*Q)
    require(sp.factor(D+kap*star+h-(w*D-(1-v)*(w-v)))==0,'half exact stationary trace')
    require(sp.factor((D+Q*star+H)-2*Q*(D+kap*star+h)/kap)==0,'half stationarity')
    W=sp.symbols('W',positive=True)
    require(sp.factor(1-(w+1)**2*W/(w*(W+1)**2)
                      -(W-w)*(w*W-1)/(w*(W+1)**2))==0,'half radical crossing denominator')
    r=sp.symbols('r',real=True)
    B=sp.log((1+sp.sqrt(1+r))**2/(4*sp.sqrt(1+r)))
    coefficients=sp.series(B,r,0,5).removeO()
    require(sp.expand(coefficients-r*r/16+r**3/16-sp.Rational(29,512)*r**4)==0,'half bulk expansion')
    eps,z,v0=sp.symbols('eps z v0',positive=True)
    wz=sp.series(sp.sqrt(1+2*eps/(1+z*eps)),eps,0,3).removeO()
    vz=sp.series(v0/sp.sqrt(1+z*eps),eps,0,3).removeO()
    gz=sp.series((1-vz)*(wz-vz)/wz,eps,0,2).removeO()
    require(sp.factor(gz-((1-v0)**2+v0*(1-v0)*(1+z)*eps))==0,'half gain expansion')
    contrast=sp.series(B.subs(r,2*eps)-B.subs(r,2*eps/(1+z*eps)),eps,0,5).removeO()
    require(sp.factor(contrast-(z*eps**3/2-(3*z*z/4+3*z/2)*eps**4))==0,'half contrast expansion')
    vv=(sp.sqrt(5)-1)/2; zz=(1+sp.sqrt(5))/2
    d=2*(1-vv)**2/zz; aa=2*(1-vv)/(zz*vv)+3*(1-vv)**2
    require(sp.simplify(d-(5*sp.sqrt(5)-11))==0,'half leading onset')
    require(sp.simplify(aa-(27-11*sp.sqrt(5))/2)==0,'half linear onset')
    # Curvature of the critical negative ratio is strictly negative.
    neg=2*r*r*(1-r)/(1+r)
    curvature=sp.simplify(sp.diff(neg,r,2).subs(r,vv))
    require(bool(curvature<0),'half critical maximum is degenerate')
    # Numerical scalar candidate from the whole stated compact interval,
    # with two implementations of the crossing. Golden search is a finite
    # control, not a stand-alone global optimization certificate.
    phi=(1+mp.sqrt(5))/2; dstar=5*mp.sqrt(5)-11; astar=(27-11*mp.sqrt(5))/2
    def model(m,z):
        L=m-1; ww=mp.sqrt(1+mp.mpf(2)/(L+z)); WW=mp.sqrt(1+mp.mpf(2)/L)
        vv=mp.sqrt(mp.mpf(L)/((L+z)*(1+z)))
        return (1-vv)*(ww-vv)*(WW+1)**2/(m*(WW-ww)*(ww*WW-1))
    def golden(f,a,b):
        t=(mp.sqrt(5)-1)/2; x=b-t*(b-a); y=a+t*(b-a); fx=f(x); fy=f(y)
        for _ in range(450):
            if fx<fy:a=x; x=y; fx=fy; y=a+t*(b-a); fy=f(y)
            else:b=y; y=x; fy=fx; x=b-t*(b-a); fx=f(x)
        z=(a+b)/2
        return z,f(z)
    numerical=[]
    for m in (50,100,500,1000,5000):
        zm,nmax=golden(lambda z:model(m,z),phi/2,2*phi)
        residual=nmax-dstar*m*m-astar*m
        nround=int(mp.floor(nmax)); dint=mp.mpf(m)*nmax
        real=ranked(mp.mpf('.5'),m,dint,zm,'negative',real_rank(mp.mpf('.5'),m,dint,zm,'negative'))
        t=mp.mpf(2)/(m-1); WT=mp.sqrt(1+t)
        bulk=mp.log((WT+1)**2/(4*WT))
        require(abs(real-bulk)<mp.mpf('1e-205'),'independent crossing does not equal real bulk')
        require(abs(residual)<20,'half onset through linear term not numerically consistent')
        require(abs(m*(zm-phi))<20,'full scalar maximizer not localized at 1/m scale')
        # Use genuine dimensions and compare the two actual integers, for
        # integers immediately below/above the real envelope. A numerical golden
        # search is not the proof of the global envelope in Section 9.
        margins=[]
        for n in (nround,nround+1):
            Dint=m*n; kap=mp.mpf(2)/(m-1)
            W0=mp.sqrt(1+kap)
            kb=mp.mpf(Dint)/(W0+1)
            def bulk_int(k):
                return entropy(mp.mpf('.5'),[(1+kap,k),(mp.mpf(1),Dint-k)],Dint)
            G=max(bulk_int(int(mp.floor(kb))),bulk_int(int(mp.ceil(kb))))
            kn=real_rank(mp.mpf('.5'),m,Dint,zm,'negative')
            family=max(ranked(mp.mpf('.5'),m,Dint,zm,'negative',int(mp.floor(kn))),
                       ranked(mp.mpf('.5'),m,Dint,zm,'negative',int(mp.ceil(kn))))
            margin=family-G
            require(margin>0 if n<nmax else margin<0,'actual rank crossing control disagrees')
            margins.append({'n':n,'m^5_score_margin':small(margin*m**5)})
        numerical.append({'m':m,'real_crossing':small(nmax),'z':small(zm),
                          'onset_residual_after_quadratic_linear_terms':small(residual),
                          'm_z_displacement':small(m*(zm-phi)),'actual_rank_margins':margins})
    # The leading/quadratic expression alone misses a nonzero linear term.
    measured_linear=(nmax-dstar*m*m)/m
    require(abs(measured_linear-astar)<mp.mpf('.005'),'half linear coefficient control')
    require(abs(measured_linear)>1,'dropped linear term mutation not rejected')
    return {'exact_symbolic_identities':8,'critical_ratio_second_derivative':str(curvature),
            'leading_onset':'5sqrt(5)-11','linear_onset':'(27-11sqrt(5))/2',
            'integer_dimensional_controls':10,'scalar_controls':numerical,
            'rejected_mutations':['omit nonzero linear final-onset term'],
            'scope':'bounded scalar search/crossing and actual-rank controls; no global numeric or Diophantine certificate'}

save()
try:
    group('symbolic_identities',symbolic)
    group('exact_fraction_physical_and_tail_controls',fraction_controls)
    group('integer_rank_enumeration',rank_controls)
    group('relative_normalization_tiny_mass',relative_controls)
    group('half_order_linear_final_onset',half_followup)
    result['status']='PASS'
except BaseException as exc:
    result['status']='FAIL'; result['exception']=str(exc)
    result['traceback']=traceback.format_exc()
    print(result['traceback'],flush=True)
finally:
    result['utc_end']=datetime.now(timezone.utc).isoformat()
    save()
    print(json.dumps({'status':result['status'],'run':str(run),'groups':list(result['groups'])}),flush=True)
if result['status']!='PASS':sys.exit(1)
