"""Finite actual-Boolean configuration discovery; never a full LR0 claim."""
from fractions import Fraction
from itertools import combinations
from math import comb
from pathlib import Path
import json, random, time
P=1009
rng=random.Random(202610140607)
SECONDS=300
BASE=Path(__file__).resolve().parent
def inverse_det(h):
    r=len(h)
    a=[[Fraction(z) for z in row]+[Fraction(i==j) for j in range(r)] for i,row in enumerate(h)]
    d=Fraction(1)
    for j in range(r):
        q=next((i for i in range(j,r) if a[i][j]),None)
        if q is None:return None
        if q!=j:a[q],a[j]=a[j],a[q];d=-d
        v=a[j][j];d*=v
        a[j]=[z/v for z in a[j]]
        for i in range(r):
            if i!=j and a[i][j]:
                v=a[i][j];a[i]=[x-v*y for x,y in zip(a[i],a[j])]
    assert d.denominator==1
    d=int(d)
    adj=[[a[i][r+j]*d for j in range(r)] for i in range(r)]
    assert all(x.denominator==1 for row in adj for x in row)
    return d,[[int(z) for z in row] for row in adj]
def mask(v):return sum((int(x)<<j) for j,x in enumerate(v))
def vec(x,r):return tuple((x>>j)&1 for j in range(r))
def rref(rows,r):
    a=[list(row) for row in rows]
    jrow=0
    for c in range(r):
        q=next((i for i in range(jrow,len(a)) if a[i][c]%P),None)
        if q is None:continue
        a[q],a[jrow]=a[jrow],a[q]
        v=pow(a[jrow][c]%P,-1,P)
        a[jrow]=[(z*v)%P for z in a[jrow]]
        for i in range(len(a)):
            if i!=jrow and a[i][c]%P:
                v=a[i][c]%P
                a[i]=[(x-v*y)%P for x,y in zip(a[i],a[jrow])]
        jrow+=1
        if jrow==len(a):break
    return tuple(tuple(row) for row in a[:jrow])
def in_span(v,rr):
    a=list(v)
    for row in rr:
        c=next(i for i,z in enumerate(row) if z)
        t=a[c]%P
        if t:a=[(x-t*y)%P for x,y in zip(a,row)]
    return not any(a)
def maximal_flat(points,r,k):
    vs={x:vec(x,r) for x in points}
    cache=set();best=[];basis=[];enumerated=0
    for bs in combinations(points,k):
        rr=rref([vs[x] for x in bs],r)
        if len(rr)!=k or rr in cache:continue
        cache.add(rr);enumerated+=1
        contained=[x for x in points if in_span(vs[x],rr)]
        if len(contained)>len(best):best=contained;basis=list(bs)
    assert len(best)>=k
    return dict(count=len(best),mass=[len(best),len(points)],basis=basis,points=best,distinct_flats=enumerated)
def configuration(h):
    r=len(h);iv=inverse_det(h)
    if iv is None:return None
    d,adj=iv;N=1<<r;allmask=(1<<N)-1
    comp=[]
    for x in range(N):
        v=[sum(adj[i][j] for i in range(r) if x>>i&1) for j in range(r)]
        values=[0]*N;good=1
        for y in range(1,N):
            b=y&-y;j=b.bit_length()-1
            values[y]=values[y^b]+v[j]
            if values[y] in (0,d):good|=1<<y
        comp.append(good)
    br=[mask(row) for row in h]
    bc=[mask([h[i][j] for i in range(r)]) for j in range(r)]
    seed=set(br)
    for _ in range(rng.randrange(1,max(2,2*r))):seed.add(rng.randrange(1,N))
    ybits=allmask
    for x in seed:ybits&=comp[x]
    ys=[y for y in range(N) if ybits>>y&1]
    xs=[x for x in range(N) if comp[x]&ybits==ybits]
    y2=allmask
    for x in xs:y2&=comp[x]
    assert y2==ybits
    assert set(br)<=set(xs) and set(bc)<=set(ys)
    xs=[x for x in xs if x];ys=[y for y in ys if y]
    assert all(sum(vec(x,r)[i]*adj[i][j]*vec(y,r)[j] for i in range(r) for j in range(r)) in (0,d) for x in xs for y in ys)
    return dict(r=r,H=h,determinant=d,adjugate=adj,rows=xs,columns=ys,basis_row_patterns=br,basis_column_patterns=bc)
started=time.monotonic();counts=dict(starts=0,singular=0,too_large=0,evaluated=0);best={};strong_half_failures=[];last=started
while time.monotonic()-started<SECONDS:
    r=rng.choice([4,5,6,7])
    kind=rng.randrange(4)
    if kind==0:
        h=[[int(i==j or (i<j and rng.randrange(2))) for j in range(r)] for i in range(r)]
    elif kind==1:
        h=[[int(i!=j) for j in range(r)] for i in range(r)]
        for _ in range(r//2):
            i=rng.randrange(r);j=rng.randrange(r);h[i][j]^=1
    else:h=[[rng.randrange(2) for j in range(r)] for i in range(r)]
    counts['starts']+=1
    c=configuration(h)
    if c is None:counts['singular']+=1;continue
    m,n=len(c['rows']),len(c['columns'])
    if max(m,n)>18 or comb(m,(r+3)//2)+comb(n,(r+3)//2)>30000:
        counts['too_large']+=1;continue
    k=(r+3)//2
    c['strip_rank_threshold']=k
    c['row_flat']=maximal_flat(c['rows'],r,k)
    c['column_flat']=maximal_flat(c['columns'],r,k)
    delta=max(Fraction(c['row_flat']['count'],m),Fraction(c['column_flat']['count'],n))
    c['best_party_strip_mass']=[delta.numerator,delta.denominator]
    counts['evaluated']+=1
    if r not in best or delta<Fraction(*best[r]['best_party_strip_mass']):
        best[r]=c
        print(json.dumps({'new_best_rank':r,'delta':str(delta),'order':[m,n],'elapsed':round(time.monotonic()-started,3)}),flush=True)
    if delta<Fraction(1,2) and len(strong_half_failures)<5:strong_half_failures.append(c)
    now=time.monotonic()
    if now-last>35:
        print(json.dumps({'progress':counts,'elapsed':round(now-started,3)}),flush=True);last=now
elapsed=time.monotonic()-started
result={'schema':'finite-boolean-rankstrip-discovery-v1','scope':'Selected finite complete Boolean configurations only; not full LR0, not an infinite counterfamily, not a proof of a uniform concentration bound.','new_major_results':0,'seed':202610140607,'requested_seconds':SECONDS,'actual_seconds':elapsed,'counts':counts,'maximal_flat_method':'All independent k-subsets, canonical RREF modulo1009, exact real ranks because every binary minor of order<=7 has absolute determinant<1009 by Hadamard. Lower-dimensional flats can be extended to dimension k within the rank-r family.','best_by_rank':best,'stronger_delta_half_failures':strong_half_failures}
(BASE/'log-rank-rankstrip-discovery.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'done':True,'counts':counts,'seconds':elapsed,'best':{str(r):c['best_party_strip_mass'] for r,c in best.items()},'strong_half_failures':len(strong_half_failures)}),flush=True)
