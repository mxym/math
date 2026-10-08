"""Exact transfer-matrix orbit spectra for k-subsets of S_n."""
from math import comb
from functools import lru_cache


def add(a,b,sgn=1):
    c=a.copy()
    for q,v in b.items():
        nv=c.get(q,0)+sgn*v
        if nv:c[q]=nv
        else:c.pop(q,None)
    return c


def mul(a,b,k):
    c={}
    for (i,j),v in a.items():
        for (l,m),w in b.items():
            if i+l>k:continue
            key=(i+l,j+m)
            c[key]=c.get(key,0)+v*w
    return {q:v for q,v in c.items() if v}


def pw(a,e,k):
    z={(0,0):1}
    while e:
        if e%2:z=mul(z,a,k)
        a=mul(a,a,k)
        e//=2
    return z


def plus_series(k):
    coeff=[{0:1}]
    def cmul(a,b):
        out={}
        for i,v in a.items():
            for j,w in b.items():out[i+j]=out.get(i+j,0)+v*w
        return out
    for m in range(1,k+1):
        curr={i+1:v for i,v in coeff[m-1].items()}
        for j in range(1,m):
            for a,v in cmul(coeff[j],coeff[m-j]).items():curr[a]=curr.get(a,0)-v
        if m==1:
            curr[1]=curr.get(1,0)-1
            curr[0]=curr.get(0,0)+1
        coeff.append({a:v for a,v in curr.items() if v})
    return {(s,t):v for s,poly in enumerate(coeff) for t,v in poly.items()}


@lru_cache(None)
def bases(k):
    plus=plus_series(k)
    z={0:{(0,0):2},1:{(0,0):1,(1,1):1}}
    trace=z[1]
    det={(1,1):1,(1,0):-1}
    for l in range(2,k+1):
        z[l]=add(mul(trace,z[l-1],k),mul(det,z[l-2],k),-1)
    return plus,tuple(z[l] for l in range(1,k+1))


def short_types(n,k):
    def loop(l,rem,chosen):
        if l==k+1:
            if rem==0 or rem>=k+1:yield tuple(chosen)
            return
        for v in range(rem//l+1):
            chosen.append(v)
            yield from loop(l+1,rem-l*v,chosen)
            chosen.pop()
    yield from loop(1,n,[])


def moment(n,k,typ):
    plus,Z=bases(k)
    rem=n-sum((j+1)*v for j,v in enumerate(typ))
    assert rem==0 or rem>=k+1
    poly=pw(plus,rem,k)
    for l,count in enumerate(typ,1):
        if count:poly=mul(poly,pw(Z[l-1],count,k),k)
    F=tuple(poly.get((k,j),0) for j in range(k+1))
    assert min(F)>=0 and sum(F)==comb(n,k),(n,k,typ,F,poly)
    return F


def partitions(n,top=None):
    if n==0:
        yield ()
        return
    if top is None:top=n
    for l in range(min(n,top),0,-1):
        for q in partitions(n-l,l):yield (l,)+q


def literal(n,k,p):
    from itertools import combinations
    g=[]
    for length in p:
        start=len(g)
        g.extend(start+(j+1)%length for j in range(length))
    F=[0]*(k+1)
    for e in combinations(range(n),k):
        image=set(g[i] for i in e)
        F[sum(i in image for i in e)]+=1
    return tuple(F)


def test():
    tests=0
    for n in range(3,13):
        for k in range(1,min(n,5)+1):
            seen=set()
            for p in partitions(n):
                a=tuple(p.count(i) for i in range(1,k+1))
                F=moment(n,k,a)
                b=literal(n,k,p)
                assert F==b,(n,k,p,F,b)
                seen.add(a)
                tests+=1
            assert len(seen)==len(list(short_types(n,k)))
    print('EXACT TRANSFER IDENTITY VERIFIED',tests,'(degree,subset size,conjugacy type) combinations')


if __name__=='__main__':test()
