from functools import lru_cache
from itertools import combinations, permutations

P = 1009
q = 5
c = (0, 2, 3, 7, 11)
u = (0, 13, 0, 0, 23)
A = {0: [(0, 0, 1)]}
D = {0: [(i, 0, u[i]) for i in range(1, q)]}
for i in range(1, q):
    j = (-i) % q
    A[i] = [(0, i, 1), (j, 0, c[i])]
    D[i] = [(i, i, u[i]), (j, j, u[j] + 13)]
    if i in (2,3): D[i] = []

@lru_cache(None)
def trace_coefficient(row, col, k):
    # Columns use the relabeling col -> -col.
    seq = sum(zip(row, ((-x) % q for x in col)), ())
    value = 0
    for hits in combinations(range(8), k):
        walks = [(i, i, 1) for i in range(q)]
        for pos, label in enumerate(seq):
            steps = D[label] if pos in hits else A[label]
            walks = [(start, end, value * edge)
                     for start, mid, value in walks
                     for tail, end, edge in steps if mid == tail]
        value += sum(v for i, j, v in walks if i == j)
    return value % P

def rotation_orbits(words):
    out = []
    for x in sorted(words):
        orbit = [x]
        while True:
            y = orbit[-1][1:] + orbit[-1][:1]
            if y == x:
                break
            orbit.append(y)
        if min(orbit) == x and len(orbit) % 2 == 0:
            out.append(orbit)
    return out

def mat(rows, cols, degree):
    # The rotation -1 coordinate of an input basis vector is its
    # alternating orbit sum; the output coordinate is at its representative.
    return [[sum((-1)**j * trace_coefficient(r[0], w, degree)
                 for j, w in enumerate(o)) % P for o in cols] for r in rows]

def solve(A, B):
    n = len(A)
    H = [a[:] + b[:] for a, b in zip(A, B)]
    pivots = []
    for j in range(n):
        k = next(k for k in range(j, n) if H[k][j])
        H[j], H[k] = H[k], H[j]
        pivots.append(H[j][j])
        z = pow(H[j][j], -1, P)
        H[j] = [z * v % P for v in H[j]]
        for i in range(n):
            if i != j:
                z = H[i][j]
                H[i] = [(x - z*y) % P for x, y in zip(H[i], H[j])]
    return [row[n:] for row in H], pivots

def check(S):
    R = rotation_orbits(set(permutations(S)))
    C = rotation_orbits(set().union(*(set(permutations(S[:i]+(0,)+S[i+1:]))
                                       for i in range(len(S)))))
    assert not any(any(row) for row in mat(R, R, 0))
    assert not any(any(row) for row in mat(R, R, 1))
    H = mat(C, C, 0)
    L = mat(R, C, 1)
    X, _ = solve(H, mat(C, R, 1))
    Z = [[(y-sum(a*b for a,b in zip(l,x))) % P
          for y,x in zip(row, zip(*X))] for row,l in zip(mat(R, R, 2), L)]
    I = [[int(i == j) for j in range(len(R))] for i in range(len(R))]
    _, pivots = solve(Z, I)
    print(S, "size", len(Z), "pivots", pivots)

def orbs(words,z):
    out=[]
    for x in sorted(words):
        o=[x]
        while (y:=o[-1][1:]+o[-1][:1])!=x:o.append(y)
        if min(o)==x and pow(z,len(o),P)==1: out.append(o)
    return out
def getmat(R,C,k,z):
    return [[sum(pow(z,j,P)*trace_coefficient(r[0],w,k) for j,w in enumerate(o))%P for o in C] for r in R]
def gauss(A):
    H=[row[:] for row in A]
    I=list(range(len(H)))
    piv=[]
    for j in range(len(H[0])):
        try:k=next(k for k in range(len(piv),len(H)) if H[k][j])
        except StopIteration:continue
        i=len(piv)
        piv.append(j)
        H[i],H[k]=H[k],H[i]
        I[i],I[k]=I[k],I[i]
        v=pow(H[i][j],-1,P)
        H[i]=[v*b%P for b in H[i]]
        for l in range(len(H)):
            if l!=i: H[l]=[(x-H[l][j]*y)%P for x,y in zip(H[l],H[i])]
    return I[:len(piv)],piv,H
zs=[z for z in range(P) if pow(z,4,P)==1]
Ms=sorted({tuple(sorted(w)) for w in __import__('itertools').product(range(q),repeat=4)})
for S in ((0,0,1,4),(0,0,2,3)):
  for z in zs:
    R=orbs(set(permutations(S)),z)
    B=getmat(R,R,0,z); ip,jp,G=gauss(B)
    if len(jp)<len(R):print('base defect',S,z,len(R)-len(jp))
def dot(x,y):return sum(a*b for a,b in zip(x,y))%P
def trans(A): return list(map(list,zip(*A)))
def mv(A,v):return [dot(row,v) for row in A]
def left(v,A):return mv(trans(A),v)
def basis(M,z):
 R=orbs(set(permutations(M)),z)
 B=getmat(R,R,0,z); ip,jp,E=gauss(B)
 F=set(range(len(R)))-set(jp); tp=gauss(trans(B))[1]; G=set(range(len(R)))-set(tp)
 def kern(A,piv,free):
  _,_,H=gauss(A)
  res=[]
  for e in sorted(free):
   v=[0]*len(R);v[e]=1
   for j,k in enumerate(piv):v[k]=-H[j][e]%P
   res.append(v)
  return res
 return R,ip,jp,kern(trans(B),tp,G),kern(B,jp,F)
def Q(M,N,z):
 R,_,_,K,_=basis(M,z);S,_,_,_,L=basis(N,z)
 if not K or not L:return []
 T=getmat(R,S,2,z)
 Z=[[dot(x,mv(T,y)) for y in L] for x in K]
 for S0 in Ms:
  if S0.count(0)%2 != 1:continue
  C=orbs(set(permutations(S0)),z)
  if not C:continue
  G1=[left(x,getmat(R,C,1,z)) for x in K]
  if not any(any(x) for x in G1):continue
  G2=trans([mv(getmat(C,S,1,z),x) for x in L])
  if not any(any(x) for x in G2):continue
  H=getmat(C,C,0,z)
  X,_=solve(H,G2)
  Z=[[(y-dot(x,k))%P for y,k in zip(row,trans(X))] for x,row in zip(G1,Z)]
 return Z
M=(0,0,1,4);N=(0,0,2,3)
assert Q(M,M,469) == [[935]]
assert Q(M,M,540) == [[400]]
print("Residual coefficients for the two nonreal sectors: 935, 400")

