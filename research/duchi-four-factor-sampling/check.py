"""Independent fail-closed audit: exact integer matrix products, no author imports."""
from fractions import Fraction as Q
from itertools import product, permutations
from math import isqrt, perm
from functools import reduce
from collections import defaultdict

def need(ok, item):
    if not ok:
        raise ArithmeticError(item)

def mm(x,y):
    a,b,c,d=x; e,f,g,h=y
    return (a*e+b*g,a*f+b*h,c*e+d*g,c*f+d*h)

def det(x):
    a,b,c,d=x
    return a*d-b*c

I=(1,0,0,1); O=(0,0,0,0)
K=101**7
# Coordinates of (99+20i)^j expanded as integers, not trigonometric approximations.
unit=[(1,0),(99,20),(99*99-20*20,2*99*20),
      (99**3-3*99*20**2,3*99**2*20-20**3)]
weights=(0,3,3,0)
P=[]
for j,((x,y),b) in enumerate(zip(unit,weights)):
    need(x*x+y*y==101**(2*j),'vector length')
    scale=99**b*101**(7-2*j-b)
    A=tuple(scale*v for v in (x*x,x*y,x*y,y*y))
    need(det(A)==0 and A[1]==A[2] and 0<A[0]+A[3]<=K,'rank-one PSD contraction')
    P.append(A)

def norm_times_K4(z):
    A=reduce(mm,(P[i] if i<4 else O for i in z),I)
    need(det(A)==0,'word not rank at most one')
    ss=sum(a*a for a in A)
    s=isqrt(ss)
    need(s*s==ss,'norm not integer after scaling')
    return s

def key(z):
    names=tuple(dict.fromkeys(z))
    return tuple(names.index(i) for i in z)
blockscores={z:norm_times_K4(z) for z in product(range(5),repeat=4)}
maxval={}
loss={}
for z in product(range(4),repeat=4):
    pi=key(z); score=blockscores[z]
    maxval[pi]=max(score,maxval.get(pi,-1))
    cand=sum(weights[i] for i in z)+sum((v-u)**2 for v,u in zip(z,z[1:]))
    loss[pi]=min(cand,loss.get(pi,1000))
need([loss[k] for k in sorted(loss)]==[0,4,5,7,8,5,9,12,8,4,11,12,12,8,9],
     '15 second-order losses')
counts=defaultdict(int); sums=defaultdict(int)
for k,v in maxval.items():
    counts[len(set(k))]+=1
    sums[len(set(k))]+=v
need(list(counts[i] for i in range(1,5))==[1,7,6,1],'pattern counts')
W=maxval[(0,1,2,3)]
need(Q(W,K**4)==Q(99,101)**9,'without replacement value')
# Expand n^4*(WOR-WR) algebraically in the ordinary monomial basis.
falls=[[1]]
for j in range(4):
    p=falls[-1]
    out=[0]*(len(p)+1)
    for i,c in enumerate(p):
        out[i]-=j*c;out[i+1]+=c
    falls.append(out)
def coeff_difference(values):
    out=[0,0,0,0,W]
    for k in range(1,5):
        for i,v in enumerate(falls[k]):
            out[i]-=v*values[k]
    return [Q(v,K**4) for v in out]
D=1126825030131969720661201
a,b,e=82396441351706403933495,453284944698127805248788,278074855080257891924992
pol=coeff_difference(sums)
need(pol==[0,Q(2*e,D),Q(-2*b,D),Q(2*a,D),0],'all polynomial coefficients')
need(min(a,10*a-b,25*a-5*b+e)>0,'shift to n=5+x')
def gap(n):
    return sum(v*n**j for j,v in enumerate(pol))/n**4
delta=Q(143122330764557928036854,140853128766496215082650125)
need(gap(5)==delta and gap(4)<0,'boundary n')
# Build both full and halved actual block assignments, including missing-label zeros.
for n in (4,5,6):
    fmaps=[]; half=[]
    for L in permutations(range(n),4):
        M=tuple((L.index(v) if v in L else 4) for v in range(n))
        fmaps.append(M)
        if L[0]<L[3]:
            half.append(M)
    need(len(fmaps)==perm(n,4)==2*len(half),'block dimensions')
    allsum=dsum=0
    for word in product(range(n),repeat=4):
        def val(m):
            return blockscores[tuple(m[i] for i in word)]
        hi=max(map(val,half))
        need(hi==max(map(val,fmaps))==maxval[key(word)],'word norm or reflection')
        allsum+=hi
        if len(set(word))==4:
            dsum+=hi
    wor=Q(dsum,perm(n,4)*K**4)
    wr=Q(allsum,n**4*K**4)
    need(wor-wr==gap(n),'raw versus symbolic')
    if n==5:
        oldS,oldR=wor,wr
    print('n=%d, dimension=%d, S-R=%s'%(n,perm(n,4),wor-wr))
paddedS=Q(perm(5,4),perm(6,4))*oldS
paddedR=Q(5**4,6**4)*oldR
need(paddedS-paddedR<0,'zero-padding population is not the all-n argument')
print('padding old five-label population by one zero gives S-R =',paddedS-paddedR)
# Independent exclusion of Liu (arXiv:2611.07649) path-Gram model as a
# direct source of a four-factor witness within his stated 0<rho<=1/2.
# Compute the coefficients as polynomials in q=1/rho for walks of 3 steps.
byk=[]
for k in range(1,5):
    coeff=[0]*4
    for w in product(range(k),repeat=4):
        if set(w)!=set(range(k)) or max(abs(i-j) for i,j in zip(w,w[1:]))>1:
            continue
        h=sum(i==j for i,j in zip(w,w[1:]))
        coeff[h]+=1
    div=1 if k==1 else 2
    need(all(v%div==0 for v in coeff),'undirected path quotient')
    byk.append([v//div for v in coeff])
need(byk==[[0,0,0,1],[1,3,3,0],[2,3,0,0],[1,0,0,0]],'Liu m=4 walk polynomials')
cc=[0,0,0,0,-1]
for k,coeff in enumerate(byk,1):
    h=sum(v*2**i for i,v in enumerate(coeff))
    for i,pv in enumerate(falls[k]):
        cc[i]+=h*pv
need(cc==[0,-1,6,2,0],'Liu q=2 lower bound')
print('PASS: exact matrix norms, all-word block reversal, coefficients, loss, padding and Liu comparison')
