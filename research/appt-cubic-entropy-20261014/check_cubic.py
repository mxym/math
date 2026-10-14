"""Finite exact and high-precision controls; no proof or Lean execution."""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import hashlib
import json
import math
import mpmath as mp
import sympy as sp

mp.mp.dps = 180
HERE = Path(__file__).resolve().parent

def fstr(x):
    return str(x)

def edge_choices(h):
    for i in range(h):
        for j in range(i+1,h):
            yield (i,j),h
        yield (i,h),h+1
    yield (h,h+1),h+2

def patterns(np,nb):
    out=[]
    def rec(h,ne,be,bd,pa,ba):
        if len(pa)<np:
            for e,hn in edge_choices(h):
                if e not in ne:
                    rec(hn,ne|{e},be,bd,pa+[e],ba)
        elif len(ba)<nb:
            for i in range(h+1):
                if i not in bd:
                    rec(max(h,i+1),ne,be,bd|{i},pa,ba+[('d',i)])
            for e,hn in edge_choices(h):
                if e not in be:
                    rec(hn,ne,be|{e},bd,pa,ba+[('e',e)])
        else:
            out.append((h,tuple(pa),tuple(ba)))
    rec(0,set(),set(),set(),[],[])
    return out

def matrix(p,b,pat):
    h,pe,bs=pat
    a=[[Q(0) for _ in range(h)] for _ in range(h)]
    for w,(i,j) in zip(p,pe):
        a[i][j]+=w;a[j][i]+=w
    for w,(tag,slot) in zip(b,bs):
        if tag=='d':a[slot][slot]+=2*w
        else:
            i,j=slot;a[i][j]+=w;a[j][i]+=w
    return a

def inverse_sum(a):
    """Fraction LDL^T positivity and solve for inverse applied to all ones."""
    n=len(a)
    if not n:return Q(0)
    l=[[Q(int(i==j)) for j in range(n)] for i in range(n)]
    d=[]
    for i in range(n):
        di=a[i][i]-sum(l[i][k]**2*d[k] for k in range(i))
        if di<=0:return None
        d.append(di)
        for j in range(i+1,n):
            l[j][i]=(a[j][i]-sum(l[j][k]*l[i][k]*d[k] for k in range(i)))/di
    v=[]
    for i in range(n):v.append(Q(1)-sum(l[i][k]*v[k] for k in range(i)))
    return sum(v[i]**2/d[i] for i in range(n))

def K(p,b,pat,a=Q(2)):
    m=matrix(p,b,pat);n=len(m)
    h=[[a*int(i==j)-m[i][j] for j in range(n)] for i in range(n)]
    v=inverse_sum(h)
    return None if v is None else v-Q(n)/a

def cost(p,b,pats):
    vals=[K(p,b,pat) for pat in pats]
    if any(v is None for v in vals):return None,None
    best=max(range(len(vals)),key=lambda i:vals[i])
    return 4*vals[best],pats[best]

def mpq(q):return mp.mpf(q.numerator)/q.denominator

def psi(a,x):
    if a==1:return x*mp.log(x)-x+1 if x else mp.mpf(1)
    return (x**a-1-a*(x-1))/(a-1)

def theta(a,k):
    if a==1:return ((1+k)*mp.log1p(k)/k-1)/k
    v=mp.expm1(a*mp.log1p(k))
    return (v-a*k)/((a-1)*k*v)

def entropy(a,D,kappa,k,p,b):
    p=[mpq(v) for v in p];b=[mpq(v) for v in b]
    mean=1+(k*kappa+sum(p)-sum(b))/D
    if a==1:
        val=(k-len(p))*(1+kappa)*mp.log1p(kappa)
        val+=sum((1+kappa+v)*mp.log(1+kappa+v) for v in p)
        val+=sum((1-v)*mp.log(1-v) if v!=1 else 0 for v in b)
        return val/(D*mean)-mp.log(mean)
    powers=(k-len(p))*(1+kappa)**a+D-k-len(b)
    powers+=sum((1+kappa+v)**a for v in p)+sum((1-v)**a for v in b)
    return (mp.log(powers/D)-a*mp.log(mean))/(a-1)

def bulk(a,D,t):
    v=D*theta(a,t)
    ks={max(0,min(D,int(mp.floor(v)))),max(0,min(D,int(mp.ceil(v))))}
    return max(entropy(a,D,t,k,[],[]) for k in ks)

def run():
    report={'scope':'finite controls only, ordinary arithmetic, no formal audit',
            'mpmath_digits':mp.mp.dps,'failed_controls_retained':[]}
    s,z,y=sp.symbols('s z y',nonnegative=True)
    A=s*s+2*s+2*y
    rhs=y*(2*s*(s+2)*(s+2-y)+y*y*(2*s+4-y))
    assert sp.expand(A*A-(s*s+y*y)*(s+2-y)**2-rhs)==0
    two=4*(z*z+2*z+2*y)/(4-4*y-z*z)-2*y/(1-y)-2*z/(1-z)
    fac=sp.factor(two)
    expected=2*z*(4*(1-y)*(y-z)+z*(2-y-z))/((1-y)*(1-z)*(4-4*y-z*z))
    assert sp.factor(two-expected)==0
    report['symbolic_identities']={'shifted_star_squared_difference':True,
                                  'two_negative_strict_interaction':str(fac)}
    counts={}
    for np,nb in [(1,0),(0,1),(1,1),(2,0),(0,2),(2,1),(1,2),(2,2),(3,0)]:
        pats=patterns(np,nb);counts[f'{np},{nb}']=len(pats)
    report['all_finite_slot_pattern_counts']=counts
    profiles=[([Q(1)],[]),([],[Q(1,2)]),([Q(1,3)],[Q(1,4)]),
              ([Q(1,3),Q(1,5)],[]),([],[Q(1,3),Q(1,5)]),
              ([Q(1,4),Q(1,5)],[Q(1,6)]),([Q(1,5)],[Q(1,4),Q(1,8)]),
              ([Q(1,6),Q(1,8)],[Q(1,7),Q(1,9)])]
    records=[];all_schur=0;all_entropy=0
    for p,b in profiles:
        pats=patterns(len(p),len(b));C,winning=cost(p,b,pats)
        assert C is not None
        disjoint=sum(4*x/(2-x) for x in p)+sum(2*x/(1-x) for x in b)
        assert C>=disjoint
        if len(p)+len(b)>1:assert C>disjoint
        c=C+Q(1,10)
        schur=[]
        for m in [16,32,64,128,512]:
            kappa=Q(2,m-1)-c/(m*m)
            feasible=True
            for pat in pats:
                val=K(p,b,pat,2+kappa)
                ok=val is not None and c>=kappa*m*m*(2+kappa)*val/(m-1)
                feasible&=ok;all_schur+=1
            schur.append({'m':m,'all_slot_patterns_actual_APPT':feasible})
            if not feasible:report['failed_controls_retained'].append({'kind':'finite_dimension_strict_margin_not_yet_sufficient','profile':[list(map(str,p)),list(map(str,b))],'m':m})
        rec={'p':list(map(str,p)),'beta':list(map(str,b)),'cost':str(C),
             'disjoint_cost':str(disjoint),'maximizing_pattern':winning,'finite_schur':schur,'entropy_sequences':[]}
        for alpha in [mp.mpf('0.25'),mp.mpf('0.75'),mp.mpf(1),mp.mpf('1.00000001'),mp.mpf(2),mp.mpf(3)]:
            delta=Q(1,2)
            target=sum(psi(alpha,1+mpq(v)) for v in p)+sum(psi(alpha,1-mpq(v)) for v in b)-alpha*mpq(delta)*mpq(c)/2
            vals=[]
            for m in [32,128,512,2048]:
                D=m**3//2;k=mpq(Q(2,m-1)-c/(m*m));t=mpq(Q(2,m-1))
                rk=int(mp.nint(D*theta(alpha,k)))
                assert rk>=m*(m-1)//2+len(p) and D-rk>=m*(m+1)//2+len(b)
                actual=D*(entropy(alpha,D,k,rk,p,b)-bulk(alpha,D,t))
                vals.append({'m':m,'correction':mp.nstr(actual,25),'error_from_graph_target':mp.nstr(actual-target,12)})
                all_entropy+=1
            assert abs(mp.mpf(vals[-1]['error_from_graph_target']))<mp.mpf('0.02')
            rec['entropy_sequences'].append({'alpha':str(alpha),'delta':str(delta),'strict_cost_budget':str(c),'target':mp.nstr(target,25),'values':vals})
        records.append(rec)
    report['exact_profile_controls']=records
    report['all_slot_schur_checks']=all_schur
    report['trace_normalized_entropy_checks']=all_entropy
    controlcount=0
    for p in range(1,20):
        for q in range(1,20):
            x=Q(p,20);b=Q(q,20)
            if x*x>=4*(1-b):continue
            U=x;S=x*x;r=mp.sqrt(mpq(S+b*b))
            C=2*(U*U+4*U+S+4*b)/(4*(1-b)-S)
            assert mpq(C)>=4*r/(2-r)
            for a in [mp.mpf(2),mp.mpf('2.5'),mp.mpf(5)]:
                assert psi(a,1+mpq(x))+psi(a,1-mpq(b))<=psi(a,1+r)+mp.mpf('1e-160')
                controlcount+=1
    report['shifted_star_cost_and_superquadratic_gain_controls']=controlcount
    rejected=[]
    one=patterns(1,0)[0]
    for m in [32,128,512]:
        # The trace/maximally-entangled budget c=2p does not give full APPT.
        p=[Q(1)];c=Q(2);kappa=Q(2,m-1)-c/(m*m)
        val=K(p,[],one,2+kappa)
        assert val is not None and c<kappa*m*m*(2+kappa)*val/(m-1)
        rejected.append({'m':m,'rejected_false_sufficiency':'trace budget alone c=2p',
                         'actual_graph_required_budget':str(kappa*m*m*(2+kappa)*val/(m-1))})
        c=Q(0);kappa=Q(2,m-1)
        val=K(p,[],one,2+kappa)
        assert val is not None and c<kappa*m*m*(2+kappa)*val/(m-1)
        rejected.append({'m':m,'rejected_false_sufficiency':'retain maximal body width despite a nonzero head'})
    # A complete alpha<2 target cannot be replaced by the scalar positive formula.
    p=[Q(7,5),Q(7,5)];C,_=cost(p,[],patterns(2,0));assert C==574
    alpha=mp.mpf(1);delta=mp.mpf('0.00001')
    two_value=2*psi(alpha,1+mpq(p[0]))-alpha*delta*mpq(C)/2
    unpenalized_single_upper=psi(alpha,mp.mpf(3))
    assert two_value>unpenalized_single_upper
    rejected.append({'rejected_unrestricted_alpha1_single_positive_reduction':True,
                     'two_positive_profile_cost':str(C),'delta':str(delta),
                     'two_positive_limiting_value':mp.nstr(two_value,35),
                     'upper_for_every_single_positive_profile':mp.nstr(unpenalized_single_upper,35),
                     'scope':'limiting finite-profile comparison; no alpha<2 closed optimizer claim'})
    report['adversarial_wrong_extension_controls']=rejected
    report['implementation_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    (HERE/'FINITE_CONTROLS.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ['exact_profile_controls']},indent=2))

if __name__=='__main__':run()
