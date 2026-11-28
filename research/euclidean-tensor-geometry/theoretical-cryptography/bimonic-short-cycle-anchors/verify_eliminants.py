"""Finite specialised Sylvester checks, without external inputs."""
from fractions import Fraction as Q
from itertools import product

def det(rows):
    A=[list(map(Q,row)) for row in rows]
    z=Q(1)
    for i in range(len(A)):
        k=next((k for k in range(i,len(A)) if A[k][i]),None)
        if k is None: return 0
        if k!=i:
            A[k],A[i]=A[i],A[k]
            z=-z
        v=A[i][i]
        z*=v
        for j in range(i+1,len(A)):
            q=A[j][i]/v
            for a in range(i,len(A)): A[j][a]-=q*A[i][a]
    return z

def res(A,B):
    # A and B are in descending order with fixed formal degree.
    n,m=len(A)-1,len(B)-1
    rows=[[0]*i+list(A)+[0]*(m-1-i) for i in range(m)]
    rows += [[0]*i+list(B)+[0]*(n-1-i) for i in range(n)]
    return det(rows)

def diagonal(t):
    a,b=4*t+3,-4*t-1
    P2=[1,0,-a*a-b*b,0,a*a*b*b] # in endpoint variable
    return res(P2,[1,-3*t-8])

pair_count=0
for t,y in product([Q(j,2) for j in range(-18,19)],range(-9,10)):
    A=[1,0,-(2*t+1)**2]
    f=[-4,-4,y*y-1] # f(u,y)=y^2-(2u+1)^2
    assert res([1,-t],f)==y*y-(2*t+1)**2
    assert res(A,f)==(y*y-(4*t+3)**2)*(y*y-(-4*t-1)**2)
    # Reversal theorem includes the repeated root when t=-1/2.
    assert res(A,[1,0,-(2*t+1)**2])==0
    pair_count+=1

vals=set()
for t in range(-20,21):
    v=diagonal(t)
    assert v==((3*t+8)**2-(4*t+3)**2)*((3*t+8)**2-(-4*t-1)**2)
    if v==0: vals.add(t)
assert vals=={5,7}  # Non-integral diagonal roots are not counted here.
for t in range(-9,12):
    a=[1,0,-(2*t+1)**2]
    assert res(a,[-1,3*t-1])==5*t*(t-2)
assert 5**2-(2*2+1)**2==0 and 3*2-5-1==0
print("PASS exact Sylvester identities: %d forward/composed/backtracking cases; 41 diagonals including 2 integral roots; 21 independent two-edge checks." % pair_count)
