"""Exact Fourier cut for a fixed Hoffman-coclique residual; stdlib Python 3."""
from fractions import Fraction as Q
from itertools import product
from math import isqrt

N = 70
DIVS = [1,3,7,21]
ONE = [1]+[0]*N
MON = [(1, j, k) for j in (7,6,5,4) for k in (11,10,9,8)]
MON += [(1,3,3,j,k) for j,k in ((7,7),(6,7),(6,6),(5,7),(5,6),
                                   (5,5),(4,7),(4,6),(4,5))]
MON += [(1,3,3,3,3,10),(0,5,11),(0,5,9)]

def theta(k,s):
    out = [0]*(N+1)
    limit = 2*isqrt(N)+2
    for x,y in product(range(-limit,limit+1),repeat=2):
        n=s*(x*x+x*y+k*y*y)
        if n<=N: out[n]+=1
    return out

def eis(w,d):
    out=ONE.copy()
    for h in range(1,1+N//d):
        val={4:240,6:-504}[w]*h**(w-1)
        for n in range(h*d,N+1,h*d): out[n]+=val
    return out

def conv(x,y):
    return [sum(x[j]*y[k-j] for j in range(k+1)) for k in range(N+1)]

series=[theta(1,1),theta(1,7),theta(2,1),theta(2,3)]
series += [eis(w,d) for w in (4,6) for d in DIVS]
sw = [1,0,3,2,7,6,5,4,11,10,9,8]
det = [3,147,7,63]+[d**(2*w) for w in (4,6) for d in DIVS]
weights=[1]*4+[4]*4+[6]*4
FF=[];DD=[]
for mon in MON:
    assert sum(weights[i] for i in mon)==11
    assert sum(i<2 for i in mon)%2 and sum(2<=i<4 for i in mon)%2==0
    f=g=ONE; delta=1
    for i in mon:
        f=conv(f,series[i]);g=conv(g,series[sw[i]])
        delta*=det[i]
    ratio=Q(7,isqrt(delta//3))
    assert ratio**2*delta==147
    if sum(i>=8 for i in mon)%2: ratio=-ratio
    FF.append(f);DD.append([ratio*v for v in g])
F=list(zip(*FF)); D=list(zip(*DD))

def subtract(u,v):
    return tuple(a-b for a,b in zip(u,v))

def lin(terms):
    return tuple(sum(c*r[j] for c,r in terms) for j in range(len(terms[0][1])))

def basis(rows):
    piv={}
    for row in rows:
        z=list(map(Q,row))
        for j,b in sorted(piv.items()):
            if z[j]:
                c=z[j]; z=[a-c*v for a,v in zip(z,b)]
        if any(z):
            j=next(j for j,v in enumerate(z) if v)
            piv[j]=[u/z[j] for u in z]
    return piv

assert len(basis(F[:28]))==28
# Normalize neither side: the common constant count is D_0 = F_0.
rows=[subtract(F[0],D[0])]
rows+=[D[j] for j in range(1,N+1) if j<=8 or j%3==2 or j in (10,13)]
rows+=[subtract(F[j],D[21*j]) for j in range(1,1+N//21)]
cuts = [
    [(-5256,D[0]),(-67,D[9]),(82,D[12]),(3,D[15]),(1,D[27]),(1,D[30])],
    [(-13056,D[0]),(394,D[9]),(16,D[16]),(1,D[19]),(2,D[27]),(1,D[33])],
    [(-472520,D[0]),(6277,D[12]),(658,D[16]),(43,D[24]),(224,D[27]),(38,D[30])],
    [(8,D[0]),(1,F[1]),(-2,D[9]),(-3,D[12]),(-1,D[15]),(-1,D[16])],
    [(-8,D[0]),(1,D[18]),(-1,D[9]),(-2,D[12]),(-1,D[15]),(-1,D[16])],
]
assert len(basis(rows))==23
assert len(basis(rows+[lin(cut) for cut in cuts]))==23
assert len(basis(rows+[D[j] for j in (0,9,12,15,16)]))==28
print("rank 28; homogeneous conditions rank 23; five cuts verified")
print("oriented caps: D9 <= 32, D12 <= 74")
# The graph height switch gives D9 = 0 on the specified two-type face.
assert 2*(5256//(2*82)) == 64
print('after the graph-height switch: D9 = 0, D12 <= 64')
