"""Exact finite-copy crossed-Gram search on normalized qutrit Dicke rays.

Each Gram pair is a legal collective rank-two witness family. This sector
does not cover arbitrary coefficient operators. Arithmetic is integer.
"""
from pathlib import Path
from functools import lru_cache
from collections import defaultdict
from fractions import Fraction
import itertools,math,json,time,datetime,random
import numpy as np
PRIVATE=Path('/mnt/d/math/tmp/breadth-quantum-20261015')
PUBLIC=Path('/home/mxym/math-breadth-quantum-20261015/research/breadth-quantum-20261015')
exec((PRIVATE/'finite_rank2_search.py').read_text().split('controls_record=')[0].split('def local_form')[1].join(['def local_form','']).split('def controls')[0])

def types(k,d=3):
    if d==1:return [(k,)]
    return [(a,)+b for a in range(k+1) for b in types(k-a,d-1)]

@lru_cache(None)
def multi(u):
    k=sum(u);return math.factorial(k)//math.prod(math.factorial(x) for x in u)

def conv(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b):
                if y:c[i+j]+=x*y
    return c

@lru_cache(200000)
def polynomial(u,s,delta):
    k=sum(u);out=[1]
    for a,b,e in zip(u,s,delta):
        p=[math.comb(a,j)*math.comb(b,j+e) if 0<=j+e<=b else 0 for j in range(a+1)]
        out=conv(out,p)
    return tuple(out)

def J(u,s,delta,lam=Fraction(1,2)):
    k=sum(u);num,den=lam.numerator,lam.denominator
    return sum((-num)**j*den**(k-j)*math.factorial(j)*math.factorial(k-j)*x for j,x in enumerate(polynomial(u,s,delta)))

@lru_cache(100000)
def diagonal_J(u,v,lam=Fraction(1,2)):
    return J(u,v,(0,)*len(u),lam)

def determinant(u,v,r,s,lam=Fraction(1,2)):
    delta=tuple(a-b for a,b in zip(r,u));assert tuple(a-b for a,b in zip(s,v))==delta
    a=diagonal_J(u,v,lam);b=diagonal_J(r,s,lam);c=J(u,s,delta,lam)
    assert a>0 and b>0
    return multi(v)*multi(r)*a*b-multi(u)*multi(s)*c*c,(a,b,c)

def dicke(u):
    k=sum(u);out=np.zeros(3**k,complex)
    for j in range(3**k):
        digs=np.unravel_index(j,(3,)*k)
        if tuple(digs.count(c) for c in range(3))==u:out[j]=1/math.sqrt(multi(u))
    return out

def qcross_formula(u,v,r,s,lam=Fraction(1,2)):
    k=sum(u);delta=tuple(a-b for a,b in zip(r,u));pref=math.sqrt(math.prod(math.factorial(x) for w in [u,v,r,s] for x in w))/math.factorial(k)
    S=Fraction(multi(u)*multi(s)*J(u,s,delta,lam),math.factorial(k)**2*lam.denominator**k)
    return pref*float(S)

def controls():
    out=[]
    rng=random.Random(1555)
    for k in [2,3,4]:
        ts=types(k);good=0
        while good<15:
            u,v,r=[rng.choice(ts) for _ in range(3)]
            s=tuple(v[i]+r[i]-u[i] for i in range(3))
            if min(s)<0:continue
            us,vs,rs,ss=map(dicke,[u,v,r,s])
            A=np.outer(us,vs.conj());B=np.outer(rs,ss.conj())
            direct=np.vdot(A,local_form(B,(3,)*k,.5)).real
            formula=qcross_formula(u,v,r,s)
            assert abs(direct-formula)<1e-12,(u,v,r,s,direct,formula)
            good+=1
        out.append({'k':k,'direct_partial_trace_cross_checks':good})
    # Known negative control at lambda>1/2: C=sum_i=0,1 |i...><i...|
    # with only one occupied resource slot and fixed spectators.
    det,_=determinant((1,0,0),(1,0,0),(0,1,0),(0,1,0),Fraction(51,100))
    assert det<0
    out.append({'one_copy_negative_control_lambda':'51/100','exact_reduced_Gram_determinant':str(det)})
    return out

results={'schema':'finite-dicke-exact-crossed-gram-v1','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'target':'full N0 unchanged; these are restricted-sector search diagnostics','controls':controls(),'records':[]}
start=time.monotonic()
for k in range(2,15):
    ts=types(k);groups=defaultdict(list)
    for u in ts:
        for v in ts:groups[tuple(a-b for a,b in zip(u,v))].append((u,v))
    count=zero=negative=0;first=None
    for pairs in groups.values():
        for (u,v),(r,s) in itertools.combinations(pairs,2):
            if u==r or v==s:continue
            det,_=determinant(u,v,r,s)
            count+=1;zero+=det==0
            if det<0:negative+=1;first=first or [u,v,r,s,str(det)]
    rec={'k':k,'qutrit_Dicke_types':len(ts),'exact_Gram_pairs':count,'zero_determinants':zero,'negative_determinants':negative,'first_negative':first,'elapsed_seconds':time.monotonic()-start,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    results['records'].append(rec)
    (PUBLIC/'DICKE_EXACT_SEARCH.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(rec),flush=True)
    if negative:break
    polynomial.cache_clear();diagonal_J.cache_clear()

rng=random.Random(151515)
for k in [20,30,50,80,120]:
    ts=types(k);count=zero=negative=0;first=None
    for attempt in range(8000):
        u,v,r=[rng.choice(ts) for _ in range(3)]
        s=tuple(v[i]+r[i]-u[i] for i in range(3))
        if min(s)<0 or u==r or v==s:continue
        det,_=determinant(u,v,r,s)
        count+=1;zero+=det==0
        if det<0:negative+=1;first=[u,v,r,s,str(det)];break
    rec={'k':k,'random_attempts':8000,'exact_Gram_pairs':count,'zero_determinants':zero,'negative_determinants':negative,'first_negative':first,'elapsed_seconds':time.monotonic()-start,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    results['records'].append(rec)
    (PUBLIC/'DICKE_EXACT_SEARCH.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(rec),flush=True)
    if negative:break
    polynomial.cache_clear();diagonal_J.cache_clear()
results['closed_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
results['complete_target_solved']=False
(PUBLIC/'DICKE_EXACT_SEARCH.json').write_text(json.dumps(results,indent=2)+'\n')
