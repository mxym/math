"""Independent exact finite sanity checks, Python standard library.
The 20-vertex local model tests the graph/conditioning identities, not large-q unimodality."""
if not __debug__:
    raise RuntimeError("Assertions are required; run python3 independent.py without -O.")

from fractions import Fraction as F
from math import comb
from array import array
from itertools import product
from functools import reduce
from operator import or_
def phase_moments(ks):
    mass=F(1); mean=var=F(0)
    for k in ks:
        ws=[(j,comb(k,j)) for j in range(1,k+1)]
        cnt=sum(w for j,w in ws); mu=F(sum(j*w for j,w in ws),cnt)
        mass*=F(cnt,2**k);mean+=mu
        var+=F(sum(j*j*w for j,w in ws),cnt)-mu*mu
    return mass,mean,var
p,a,va=phase_moments([1,6]);p2,b,vb=phase_moments([2,2,3])
assert p==p2==F(63,128); assert a-F(7,2)==F(23,42) and b-F(7,2)==F(37,42)
q=2**40; B=q*q; D=F(1,65536);r=B//32; N=14*B+6*q*B
# Check powers by finite integer comparisons on their exponents.
assert 7<8 and 3+80-q//256<=-12
assert D*(16+2*7)<=F(1,512)
assert D**2*q==256 and D**2*q>=16**2
assert B//512>=12 and 126*B>=12 and 2*(F(1,4095)+F(1,4096))+F(1,4096)<F(1,100)
assert min(p,p2)>F(1,4)
for var in (va,vb):
    actual=B*(var+F(7,4))+F(6*B*q,4)
    assert actual<=2*B*q and actual/r**2<F(1,100)
mus=[F(N,2)+B*x for x in [F(23,42),F(5,7),F(37,42)]]
def fl(x):return x.numerator//x.denominator
def ce(x):return -fl(-x)
winds=[(ce(x-r),fl(x+r)) for x in mus]
assert 0<=winds[0][0] and winds[-1][-1]<=N and all(winds[i][1]<winds[i+1][0] for i in (0,1))
lengths=[z-y+1 for y,z in winds]
assert all(2*r-1<=v<=2*r+1 for v in lengths)
assert F(99,max(lengths))>F(3,min(lengths))
print('N =',N,'; exact phase mass =',p,'per base position; shifts =',a-F(7,2),b-F(7,2))
print('conditional group variances =',va,vb,'; exact integer window sizes =',lengths)
def incidence_checks(q):  # prime toy fields
    n=q*q; edges=[]
    for P in range(n):
        x,y=divmod(P,q)
        edges.append(sum(1<<(s*q+(y-s*x)%q) for s in range(q)))
    sizes=[i.bit_count() for i in range(2**n)]
    e0=0
    for I in range(1,2**n):
        u=sizes[I]; ids=[i for i in range(n) if I>>i&1]
        adj=reduce(or_,(edges[i] for i in ids),0); g=sizes[adj]
        assert g*(q+u)>=q*q*u
        d=[sum(e>>j&1 for e in (edges[i] for i in ids)) for j in range(n)]
        js=[0]*(2**n)
        for J in range(1,2**n):
            bit=J&-J;v=sizes[J]; e=js[J]=js[J-bit]+d[bit.bit_length()-1]
            assert not u*v>q*e or (u*v-q*e)**2<=q**3*u*v
            e0+=1
    return e0
print('direct finite-field nonempty subset-pair incidence checks:',incidence_checks(2)+incidence_checks(3))
# One base incidence with exactly the cited group sizes. Build all actual graph edges.
C=14; h=6; n=C+h; cm=(1<<C)-1; full=(1<<n)-1
groups=[]; start=0
for k in (1,6,2,2,3):groups.append(((1<<k)-1)<<start);start+=k
left,right=groups[:2],groups[2:]; adj=[cm^(1<<i) for i in range(C)]+[0]*h
for j,(L,R) in enumerate(product(left,right)):
    v=C+j;adj[v]=L|R
    for i in range(C):
        if adj[v]>>i&1:adj[i]|=1<<v
cover=array('I',[0])*(1<<n)
for S in range(1,1<<n):
    bit=S&-S;cover[S]=cover[S^bit]|adj[bit.bit_length()-1]
actual=[0]*(n+1); predicted=[0]*(n+1); variants=[0,0]; phases=[0,0]; patternvisits=0
for X in range(1<<C):
    k=X.bit_count(); lm=[not (g&X) for g in left];rm=[not(g&X) for g in right]
    A=not any(lm);B0=not any(rm)
    e=sum(lm)*sum(rm)
    for j in range(h-e+1):predicted[k+e+j]+=comb(h-e,j)
    for Y in range(1<<h):
        S=X|(Y<<C);dom=(cover[S]|S)==full; tot=cover[S]==full
        conn=False
        if dom:
            reached=S&-S
            while True:
                grow=reached|(cover[reached]&S)
                if grow==reached:break
                reached=grow
            conn=(reached==S)
        assert not (A or B0) or (dom and tot and conn)
        actual[S.bit_count()]+=dom;variants[0]+=tot;variants[1]+=conn
        phases[0]+=A;phases[1]+=B0
        if dom: assert not (X==0) or Y==(1<<h)-1
        patternvisits+=1
assert actual==predicted and patternvisits==2**20 and phases==[p*2**20,p*2**20]
print('all',patternvisits,'direct adjacency subsets checked; phase masses',phases,'; ordinary/total/connected totals',sum(actual),*variants)
print('size histogram for ordinary domination:',actual)
