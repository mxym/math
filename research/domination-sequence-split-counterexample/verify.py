"""Original-derivation checks, fail closed, pure Python. Not a large-graph enumeration."""
from fractions import Fraction as Q
from math import comb
from itertools import product
from collections import Counter

def need(ok,msg):
    if not ok: raise ArithmeticError(msg)

# Give an explicit basis for the huge field if desired: GF(2)[x]/(f).
def polyrem(a,b):
    if b==0: raise ZeroDivisionError()
    while a.bit_length()>=b.bit_length():
        a ^= b<<(a.bit_length()-b.bit_length())
    return a

def polygcd(a,b):
    while b: a,b=b,polyrem(a,b)
    return a

def sq(a): return sum(1<<(2*i) for i in range(a.bit_length()) if (a>>i)&1)
f=(1<<40)|0x39
x=2
for k in range(1,41):
    x=polyrem(sq(x),f)
    if k in (8,20): need(polygcd(x^2,f)==1,'proper-degree field factor')
need(x==2,'Frobenius-40 residue')
q=2**40;b=q*q;N=14*b+6*b*q;r=b//32
d=Q(1,2**16)
A=(1,6);B=(2,2,3)
def hit(sizes):
    v=Q(1)
    for s in sizes:v*=1-Q(1,2**s)
    return v
def inc(sizes):return sum(Q(s,2*(2**s-1)) for s in sizes)
need(hit(A)==hit(B)==Q(63,128),'phase weights')
need((inc(A),inc(B),inc(B)-inc(A))==(Q(23,42),Q(37,42),Q(1,3)),'phase separation')
# Verify the concentration constants without ever constructing exponentially large powers.
need(q//256>=80+3+12 and b==2**80 and 7<8,'small tail')
need(30*d<=Q(1,512) and Q(1,256)-30*d>=Q(1,512),'medium tail')
need(d*(2**20)==16 and d*d*q/2==128,'large tail')
need(b//512>=12 and 126*b>=12,'power comparison')
need(2*(Q(1,4095)+Q(1,4096))+Q(1,4096)<Q(1,100),'mixed bound')
need(sum(i*i for i in A+B)==54 and 54+Q(3*q,2)<=2*q,'variance proxy')
need(Q(2048,q)<Q(1,100) and Q(b,6)>2*r and r>=1,'window separation')
need(Q(99,100*(2*r+1))>Q(3,100*(2*r-1)),'strict valley')
ma=Q(N,2)+b*inc(A);mb=Q(N,2)+b*inc(B);mm=(ma+mb)/2
def floor(x):return x.numerator//x.denominator
def ceil(x):return -floor(-x)
windows=[(ceil(m-r),floor(m+r)) for m in (ma,mm,mb)]
need(0<=windows[0][0] and windows[0][1]<windows[1][0] and windows[1][1]<windows[2][0] and windows[2][1]<=N,'integer windows')
for a,c in windows:need(2*r-1<=c-a+1<=2*r+1,'window cardinality')
print('q, N:',q,N)
print('three closed integer windows:',windows)
# Independently verify the two-sided affine incidence inequalities over tiny prime fields,
# squaring only when q*e-uv<0 in the one-sided inequality.
inc_checks=0
for p in (2,3):
    sites=list(product(range(p),repeat=2));n=len(sites)
    mat=[sum(1<<j for j,(s,h) in enumerate(sites) if (y-s*x-h)%p==0) for x,y in sites]
    tram=[sum(1<<i for i in range(n) if mat[i]>>j&1) for j in range(n)]
    for rows in (mat,tram):
        for U in range(1,1<<n):
            u=U.bit_count();D=[sum((U>>i&1)*(e>>j&1) for i,e in enumerate(rows)) for j in range(n)]
            need(sum(D)==p*u and sum(t*t for t in D)<=p*u+u*(u-1),'incidence moments')
            need(sum(x>0 for x in D)*(p+u)>=n*u,'neighborhood expansion')
            vals=[0]
            for j in range(n):vals+= [v+D[j] for v in vals]
            for V,E in enumerate(vals):
                v=V.bit_count();err=u*v-p*E
                need(err<=0 or err*err<=p**3*u*v,'mixing')
                inc_checks+=1
print('two-sided cut checks at q=2,3:',inc_checks)
# One-site one-incidence toy, same 14 variable groups + 6 auxiliaries. Compare direct
# ordinary/total/connected domination at each clique pattern against forced auxiliary
# counts and the pure-event sandwich. This toy is not claimed bimodal.
sizes=A+B;nvar=sum(sizes);groups=[];off=0
for k in sizes:groups.append(((1<<k)-1)<<off);off+=k
clin=(1<<nvar)-1
pairn=[groups[i]|groups[j] for i in (0,1) for j in (2,3,4)]
nvaraux=len(pairn);nall=nvar+nvaraux;allv=(1<<nall)-1
adj=[clin^(1<<i) for i in range(nvar)]+pairn.copy()
for h,nei in enumerate(pairn):
    for i in range(nvar):
        if nei>>i&1:adj[i]|=1<<(nvar+h)
union=[0]
for nei in adj:union+= [t|nei for t in union]
aux_counts=Counter()
for C in range(1<<nvar):
    missing=sum(1 for t in pairn if not t&C)
    phase=all(C&t for t in groups[:2]) or all(C&t for t in groups[2:])
    have=Counter()
    for H in range(1<<nvaraux):
        D=C|(H<<nvar);nb=union[D];dom=D|nb==allv;tot=nb==allv
        if dom:have[H.bit_count()]+=1
        # Flood-fill induced selected graph without use of split-graph characterization.
        seen=D&(-D)
        while seen:
            old=seen;seen |= union[seen]&D
            if seen==old:break
        con=bool(D) and seen==D and dom
        need(not phase or (dom and tot and con),'pure sandwich')
        need(not tot or dom,'total subset');need(not con or dom,'connected subset')
        aux_counts[dom,tot,con]+=1
    for j in range(nvaraux+1):
        expect=comb(nvaraux-missing,j-missing) if j>=missing else 0
        need(have[j]==expect,'conditional weight by size')
need(sum(aux_counts.values())==2**20,'toy exhaustive cardinality')
print('one-site toy exact subset classifications (ordinary,total,connected):',sorted(aux_counts.items()))
