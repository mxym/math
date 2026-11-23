"""Nine-parameter determination of the true rank-42 Hoffman-axis Jacobi series.
Requires the native helpers in this folder. No optimizer or floating arithmetic.
"""
from fractions import Fraction as F
from functools import cache
from itertools import product
from math import isqrt
from pathlib import Path
import runpy
from collections import defaultdict
from two_type_true_hoffman import basic,orb,move,rows,projections,SHIFTS,moments
from original_site_populations import hp

P=1000003
J=35
params=[(0,0,None),(0,18,None),(0,22,None),(3,33,5),
        (1,23,-3),(1,23,4),(0,24,-7),(3,35,5),(1,27,-3)]

def legal(a,t):
    return basic(a,t) and (abs(a),t)!=(0,14)

def chart():
    base=[]
    for z in rows():
        v=dict(z)
        for target,source,g in [((1,25),(0,16),8),((1,27),(0,18),9),
                ((1,27),(2,26),2),((0,26),(1,21),8)]:
            v[source]=v.get(source,0)-g*z.get(target,0)
        base.append(v)
    keys=set([(0,2*j) for j in range(J+1)]+[(3,2*j+11) for j in range(J+1)])
    for row in base:keys.update(row)
    for sh in [None,*SHIFTS]:
        for i in (1,2,3):keys.update(projections(sh,i))
    by=defaultdict(list); seen={}
    for a,t in sorted(keys):
        if not legal(a,t):continue
        for d in range(-isqrt(22*t),isqrt(22*t)+1):
            if (a,t)==(2,22) and d!=22:continue
            if (a,t)==(0,18) and d!=0:continue
            if (a,t)==(1,27) and d not in (-3,4):continue
            if (d-4*a)%7 or (9*d-22*a)**2>154*(9*t-11*a*a):continue
            o=orb((a,t,d))
            if o not in seen:seen[o]=all(legal(*move(o,k)[:2]) for k in range(-6,7))
            if seen[o]:by[a,t].append((d,o))
    atoms=sorted(o for o,v in seen.items()if v)
    ix={z:i for i,z in enumerate(atoms)};N=len(ix)
    def sel(a,t,d=None):
        out=[0]*N
        for k,z in by[a,t]:
            if d is None or k==d:out[ix[z]]+=1
        return out
    def lin(x):
        out=[0]*N
        for (a,t),v in x.items():
            for k,z in by[a,t]:out[ix[z]]+=v
        return out
    # All equations are homogeneous; the scale is W000, actually 1.
    eq=[lin(r) for r in base]
    eq +=[lin({(2,22):1,(0,0):-1}),lin({(1,27):1,(0,18):-9})]
    dirs=[((0,0,0,0),1),((1,2,3,1),1),((1,-1,1,-2),1),((2,-1,1,2),1)]
    for d in (2,4,6,8,10):eq+=moments(by,ix,[d],dirs)
    return atoms,by,ix,sel,eq

def field(r):
    return (int(r.numerator)*pow(int(r.denominator),-1,P))%P

def ff(v):return [x%P for x in v]

class Span:
    def __init__(self):self.b={}
    def add(self,v):
        v=ff(v)
        for i in sorted(self.b):
            if v[i]:
                c=v[i];v=[(a-c*bb)%P for a,bb in zip(v,self.b[i])]
        if any(v):
            i=next(j for j,n in enumerate(v)if n)
            inv=pow(v[i],-1,P);self.b[i]=[(inv*a)%P for a in v]

form=runpy.run_path(str(Path(__file__).resolve().parents[2] /
                       "maximal-marked-lattice"/"verify.py"))["form"]
@cache
def conv(k,a,l,r):
    f=form(a,l);g=form(k-a,r)
    return [field(sum(f[i]*g[j-i] for i in range(j+1)))for j in range(J+1)]

def modular_forms(d):
    k=22+d;dim=1+2*(k//3);B={}
    for a,l,r in product(range(3,k//2+1,2),(0,1),(0,1)):
        b=k-a
        fac=pow(7,(2*l-1)*((a-1)//2)+(2*r-1)*((b-1)//2)+10+d//2,P)
        v=conv(k,a,l,r)+[(fac*y)%P for y in conv(k,a,1-l,1-r)[:J//7+1]]
        for j in range(dim):
            if not v[j]:continue
            if j not in B:
                inv=pow(v[j],-1,P);B[j]=[a*inv%P for a in v];break
            c=v[j];v=[(a-c*z)%P for a,z in zip(v,B[j])]
        if len(B)==dim:break
    assert sorted(B)==list(range(dim))
    return B


def signed_cuts(atoms,sel,eq):
    # Boolean feasibility or modular rank alone would not prove row membership.
    import sympy as sm
    def X(a,t,d=None):return sm.Matrix([sel(a,t,d)])
    one=X(0,0);s=X(1,23)-99*one;e=X(2,36,-6)
    lower=(e-81*one-6*s-2*X(4,46,2)-2*X(2,34,1)-12*X(1,23,11)
           -2*X(1,29,11)-5*(X(1,23,4)-77*one))
    upper=(3*e+12*X(4,44,9)+12*X(1,23,11)+6*X(1,29,11)
           +3*(X(1,23,4)-77*one)-557*one-8*s)
    r,piv=sm.Matrix(eq).to_DM().rref();v=r.to_Matrix().tolist()
    for p in (lower,upper):
        h=list(p)
        for i,j in enumerate(piv):
            q=h[j]
            if q:h=[w-q*z for w,z in zip(h,v[i])]
        assert not any(h)
    assert [(81+6*j,(557+8*j)//3) for j in (2,5,8,11)]==[(93,191),(111,199),(129,207),(147,215)]
    print("Both signed population identities verified over the rationals.")

def main():
    atoms,by,ix,sel,eq=chart();N=len(atoms)
    assert N==218;sp=Span()
    signed_cuts(atoms,sel,eq)
    for v in eq:sp.add(v)
    def coeff(j,d):
        R=[0]*N
        for a,t in [(0,2*j),(3,2*j+11)]:
            for D,o in by[a,t]:
                v=22*(a//3)-3*D
                assert v%7==0
                R[ix[o]]+=(1 if a==0 else 2)*(1 if j%7==0 else 8)*hp(d,v,308*j,44)
        return ff(R)
    for d in range(0,19,2):
        B=modular_forms(d);n=len(B)
        V=[coeff(j,d)for j in list(range(J+1))+[7*h for h in range(J//7+1)]]
        for j in range(n):
            for h in range(j+1,len(V)):
                c=B[j][h]
                if c:V[h]=[(a-c*b)%P for a,b in zip(V[h],V[j])]
        for v in V[n:]:sp.add(v)
    print("218 angular variables; homogeneous tested row rank mod 1000003 =",len(sp.b))
    for a,t,d in params:sp.add(sel(a,t,d))
    assert len(sp.b)==N
    print("Full rank after the nine stated physical coordinate readings.")
if __name__=="__main__":main()
