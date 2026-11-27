"""Independent exact triangular Bernstein replay for both seven-dimensional charts.

Usage: python3 audit.py
     or python3 audit.py upper-charts.json uniqueness-charts.json
With no arguments, uses embedded byte-identical copies of the pinned data.
Only Python's standard library is used. Neither original verifier is imported.
"""
from collections import deque
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, product
from math import comb, factorial, lcm
from pathlib import Path
import base64
import hashlib
import json
import sys
import zlib

assert __debug__
SCALE = 10**7
DEG = 10

def plusmul(dst, a, w):
    for e,q in a.items():
        dst[e] = dst.get(e,0)+w*q

def multiply(a,b):
    c={}
    for (i,j),v in a.items():
        for (k,l),w in b.items():
            if v and w: c[i+k,j+l]=c.get((i+k,j+l),0)+v*w
    return c

def ppowers(a,d):
    v=[{(0,0):F(1)}]
    for _ in range(d):v.append(multiply(v[-1],a))
    return v

@lru_cache(None)
def sphere_poly(ambient,d):
    # Solve the normalized zonal differential equation, downward on degrees.
    if d==0:return {0:F(1)}
    if ambient==1:
        assert d==1
        return {1:F(1)}
    a={d:F(1)}
    for k in range(d-2,-1,-2):
        den=d*(d+ambient-2)-k*(k+ambient-2)
        a[k]=-(k+2)*(k+1)*a[k+2]/den
    h=sum(a.values())
    assert h
    return {k:v/h for k,v in a.items()}

def power_poly(r,items):
    out={(0,0):F(-SCALE)}
    for a,b,w in items:
        for i,u in sphere_poly(r,a).items():
            for j,v in sphere_poly(7-r,b).items():
                out[i,j]=out.get((i,j),0)-w*u*v
    return {k:v for k,v in out.items() if v}

def region_triangles(r,w):
    if r==1:
        for x in (F(-1),F(1)):
            if w==1:
                if x>F(1,2):continue
                top=F(1)
            else:top=min(F(1),(F(1,2)-w*x)/(1-w))
            if top>=-1: yield ((x,F(-1)),(x,top),(x,F(-1)))
        return
    P=[(F(-1),F(-1)),(F(1),F(-1)),(F(1),F(1)),(F(-1),F(1))]
    D=[]
    def g(p): return w*p[0]+(1-w)*p[1]-F(1,2)
    for x,y in zip(P,P[1:]+P[:1]):
        gx,gy=g(x),g(y)
        if gx<=0:D.append(x)
        if gx*gy<0:
            t=gx/(gx-gy)
            D.append(tuple((1-t)*u+t*v for u,v in zip(x,y)))
    assert len(D)>=3
    assert all(g(v)<=0 for v in D)
    for j in range(1,len(D)-1):yield (D[0],D[j],D[j+1])

def coords(d):
    return [(d-i-j,i,j) for i in range(d+1) for j in range(d+1-i)]

def substitution(pol,T,d):
    z={}
    U,V=[ppowers({(0,0):T[0][i],(1,0):T[1][i]-T[0][i],(0,1):T[2][i]-T[0][i]},d)
         for i in range(2)]
    for (i,j),w in pol.items():plusmul(z,multiply(U[i],V[j]),w)
    # Bernstein normalization on a simplex (lambda_0+lambda_1+lambda_2=1).
    bs=[]
    for h,i,j in coords(d):
        bs.append(sum(w*F(comb(i,a)*comb(j,b),comb(d,a)*comb(d-a,b))
                      for (a,b),w in z.items() if a<=i and b<=j))
    den=lcm(*(t.denominator for t in bs))
    return [int(t*den) for t in bs]

def m3(A,B):
    C={}
    for e,x in A.items():
        for f,y in B.items():
            g=tuple(a+b for a,b in zip(e,f))
            C[g]=C.get(g,0)+x*y
    return C

@lru_cache(None)
def children_ops(d):
    # Twice the barycentric coordinates of each child vertex.
    a,b,c=(2,0,0),(0,2,0),(0,0,2)
    u,v,w=(1,1,0),(1,0,1),(0,1,1)
    coords_d=coords(d)
    lookup={s:i for i,s in enumerate(coords_d)}
    ff=[factorial(i) for i in range(d+1)]
    def fb(e):
        x,y,z=e
        return ff[x]*ff[y]*ff[z]
    basis=[(1,0,0),(0,1,0),(0,0,1)]
    result=[]
    for child in ((a,u,v),(u,b,w),(v,w,c),(u,w,v)):
        powers=[]
        for row in zip(*child):
            l={e:c for e,c in zip(basis,row) if c}
            powers.append([{(0,0,0):1}])
            for _ in range(d):powers[-1].append(m3(powers[-1][-1],l))
        out=[[] for _ in coords_d]
        for z,(i,j,k) in enumerate(coords_d):
            lead=ff[d]//fb((i,j,k))
            for e,x in m3(m3(powers[0][i],powers[1][j]),powers[2][k]).items():
                out[lookup[e]].append((z,lead*x*fb(e)))
        result.append(out)
    return result

def certificate(B,d):
    ops=children_ops(d)
    todo=[(B,0)]
    visits=0
    while todo:
        co,dep=todo.pop();visits+=1
        if min(co)>=0:continue
        assert dep<18 and max(co)>=0
        for op in ops:todo.append(([sum(c*co[i] for i,c in row) for row in op],dep+1))
    return visits

def cover(rows,bound):
    by_size={}
    high=0
    for r,a,b,k,terms in rows:
        assert all(type(i) is int for i in (r,a,b,k))
        assert r in (1,2,3) and k>=0 and 0<=a<b<=2**k
        lo,hi=F(a,2**k),F(b,2**k)
        by_size.setdefault(r,[]).append((lo,hi))
        assert all(type(i) is int and type(j) is int and type(c) is int
                   and i>=0 and j>=0 and 0<i+j<=DEG and c>0
                   and (r!=1 or i<=1) for i,j,c in terms)
        val=SCALE+sum(t[2] for t in terms)
        assert val<bound*SCALE
        high=max(high,val)
    for r,spans in by_size.items():
        spans.sort()
        left=F(0)
        for a,b in spans:
            assert a<=left
            left=max(left,b)
        assert left==1
    assert set(by_size)=={1,2,3}
    ntri=nodes=0
    for r,a,b,k,terms in rows:
        p=power_poly(r,terms)
        for x in (a,b):
            w=F(x,2**k)
            for T in region_triangles(r,w):
                ntri+=1
                try:nodes+=certificate(substitution(p,T,DEG),DEG)
                except AssertionError as e:
                    raise AssertionError((bound,r,a,b,k,w,T)) from e
    print(f"bound < {bound}: {len(rows)} charts, {ntri} original triangles,"
          f" {nodes} exact Bernstein subdivisions, max diagonal numerator {high}.",flush=True)

def e7():
    V=[]
    for i,j in combinations(range(6),2):
        for a,b in product((-2,2),repeat=2):
            v=[0]*8;v[i]=a;v[j]=b;V.append(tuple(v))
    for a in (-2,2):V.append((0,)*6+(a,-a))
    for W in product((-1,1),repeat=6):
        if W.count(-1)%2==1:
            for a in (-1,1):V.append(W+(a,-a))
    dot=lambda v,w:sum(a*b for a,b in zip(v,w))
    assert len(set(V))==126
    assert all(dot(x,x)==8 and x[6]+x[7]==0 for x in V)
    assert max(dot(x,y) for x,y in combinations(V,2))==4
    R=set(V)
    def ref(x,r):
        a=dot(x,r); assert a%4==0
        return tuple(v-a*b//4 for v,b in zip(x,r))
    assert all(ref(x,r) in R for r in V for x in V)
    seen={V[0]}
    todo=deque([V[0]])
    while todo:
        x=todo.popleft()
        for r in V:
            y=ref(x,r)
            if y not in seen:seen.add(y);todo.append(y)
    assert seen==R
    print("independent integral E7 root witness and reflection transitivity: 126",flush=True)


def group_and_antipodal_checks():
    # Directly transcribed from the public ATLAS standard generators.
    # https://brauer.maths.qmul.ac.uk/Atlas/exc/G22/gap0/U33G1-Zr7aB0.g
    a=((-1,0,0,0,0,0,0),(0,-1,0,0,0,0,0),(0,1,0,0,0,1,0),
       (-1,0,0,0,0,0,1),(0,0,0,0,1,0,0),(0,1,1,0,0,0,0),
       (-1,0,0,1,0,0,0))
    b=((0,-1,0,0,0,-1,0),(0,1,1,0,0,0,0),(0,-1,0,0,0,0,0),
       (1,0,0,0,0,0,0),(0,0,0,0,0,0,-1),(0,0,0,-1,0,0,1),
       (0,0,0,0,1,0,1))
    def mul(X,Y):
        return tuple(tuple(sum(x*y for x,y in zip(v,w)) for w in zip(*Y)) for v in X)
    E=tuple(tuple(int(i==j) for j in range(7)) for i in range(7))
    c=mul(mul(b,b),b)
    P=[E]
    H={E}
    for x in P:
        for y in (a,c):
            z=mul(x,y)
            if z not in H:
                H.add(z);P.append(z)
                assert len(H)<=8
    assert len(H)==8
    # Independently solve the common fixed equations by full row reduction.
    A=[[F(X[i][j]-E[i][j]) for j in range(7)] for X in (a,c) for i in range(7)]
    rank=0
    for i in range(7):
        k=next((j for j in range(rank,len(A)) if A[j][i]),None)
        if k is None:continue
        A[k],A[rank]=A[rank],A[k]
        w=A[rank][i]
        A[rank]=[x/w for x in A[rank]]
        for j in range(rank+1,len(A)):
            w=A[j][i]
            A[j]=[x-w*y for x,y in zip(A[j],A[rank])]
        rank+=1
    assert rank==7

    # Gaussian-integer arithmetic for the distinct nonreal degree-seven trace.
    # https://brauer.maths.qmul.ac.uk/Atlas/exc/G22/gap0/U33G1-Ar7bB0.g
    Z=(0,0); P=(1,0); M=(-1,0); J=(0,1); N=(0,-1)
    C=((Z,P,Z,Z,Z,Z,Z),(P,Z,Z,Z,Z,Z,Z),(Z,Z,Z,P,Z,Z,Z),
       (Z,Z,P,Z,Z,Z,Z),((1,1),(-1,-1),M,P,P,Z,Z),(Z,Z,Z,Z,Z,P,Z),
       (Z,Z,J,N,Z,Z,P))
    D=((Z,Z,P,Z,Z,Z,Z),(P,Z,Z,Z,Z,Z,Z),(Z,Z,Z,Z,P,Z,Z),
       (Z,Z,Z,Z,Z,P,Z),(Z,Z,Z,Z,Z,Z,P),(Z,N,N,M,Z,M,N),
       (M,P,P,Z,M,Z,P))
    def gaussian_mm(A,B):
        return tuple(tuple((sum(a*c-b*d for (a,b),(c,d) in zip(x,y)),
                            sum(a*d+b*c for (a,b),(c,d) in zip(x,y)))
                           for y in zip(*B)) for x in A)
    X=gaussian_mm(C,gaussian_mm(D,D))
    assert (sum(X[i][i][0] for i in range(7)),sum(X[i][i][1] for i in range(7)))==(-1,1)

    # Recheck the exact even LP polynomial used in the classical antipodal
    # 126-point equality argument.
    f={0:F(1)}
    for k,a in [(2,F(234,11)),(4,F(448,11))]:
        for i,x in sphere_poly(7,k).items():f[i]=f.get(i,0)+a*x
    assert f=={0:F(0),2:F(-21),4:F(84)}
    print("U3(3) standard matrices: eight elements, common fixed rank 7,"
          " nonreal trace -1+i verified; classical antipodal polynomial verified.",flush=True)


# Pinned mxym/math chart JSON data, embedded losslessly for standalone replay.
PACKED = [
    ("87688270cf65152b5113df42ec531fecc2844adf5d1e2420b9a70c0844e44b38",
     "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"),
    ("43537e2de4da87f2da9f3ea96804e6b8fcc55cd38a5a9c7e0695a3568d783575",
     "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"),
]

if __name__=="__main__":
    if len(sys.argv) not in (1,3):
        raise SystemExit("usage: python3 audit.py [upper-charts.json uniqueness-charts.json]")
    for i,((sha,coded),bound) in enumerate(zip(PACKED,(127,126))):
        data=(zlib.decompress(base64.b64decode(coded)) if len(sys.argv)==1
              else Path(sys.argv[i+1]).read_bytes())
        assert hashlib.sha256(data).hexdigest()==sha
        cover(json.loads(data),bound)
    e7()
    group_and_antipodal_checks()
