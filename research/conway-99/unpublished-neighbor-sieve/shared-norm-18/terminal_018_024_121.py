"""Exact fixed-terminal (018,024,121) signed-class relations and native bounds. Needs SymPy and upstream files."""
from itertools import product, groupby
from fractions import Fraction as F
import sympy as sm
from rank42_u121_residues import B,D,shifts,pairs,group,dot,times,row

# This time allow raw N24, and remove raw G125 (U125=N16=0).
def points(sh):
    den=1 if sh is None else 3
    cos=[((0,)*4,1)] if sh is None else [(tuple(j*v%3 for v in times(B,sh)),3)for j in (-1,0,1)]
    for offs,step in cos:
        m=4*den
        for g in product(*(range(-m+(m+off)%step,m+1,step)for off in offs)):
            b=28*den**2-dot(g,times(D,g))
            if b<0:continue
            for a in ((0,3)if sh is None else ((-dot(sh,g)+4)%9-4,)):
                if a<0:continue
                n,rem=divmod(9*b+11*a*a*den**2,9*den**2)
                if rem or n<11*a or (n-11*a)%2 or (a==0 and 0<n<14) or (a==1 and n<=19) or (a,n)==(2,24):continue
                if (a,n) in ((0,16),(0,20),(1,25),(2,26),(2,28),(2,30),(3,37)):continue
                c=tuple((g[i]+5*g[i+1])*pow(den,-1,7)%7 for i in (0,2))
                yield a,n,g,c,1+(a!=0)

def projected():
    tabs={s:list(points(s))for s in shifts}; rows=[]
    for o in group:
        for s,vs in tabs.items():
            for ij in pairs:
                rows.append({k:v for k,v in row(o,s,ij,vs).items() if v and k[2]!=(0,0)})
    keys=sorted(set().union(*rows))
    for at,it in groupby(keys,key=lambda k:k[:2]):rows.append(dict.fromkeys(it,1))
    L=sm.Matrix([[r.get(k,0)for k in keys]for r in rows]).to_DM().nullspace().to_Matrix().T
    ids=[keys.index(k)for k in ((0,18,(2,3)),(0,18,(2,4)),(0,22,(1,2)),(0,24,(0,1)))]
    assert L.shape==(36,4)
    L=L*L[ids,:].inv()
    ix=lambda a,t:[i for i,k in enumerate(keys)if k[:2]==(a,t)]
    N=L[ix(0,18),:]; U=L[ix(1,21),:]; V=L[ix(4,44),:]; P=L[ix(0,24),:]
    assert N==sm.Matrix([[1,0,0,0],[0,1,0,0],[0,-1,0,0],[-1,0,0,0]])
    assert 55*(U.row(1)-U.row(0))==sm.Matrix([[48,48,0,0]])
    assert 55*(U.row(3)-U.row(2))==sm.Matrix([[48,-48,0,0]])
    assert 55*(V.row(1)-V.row(0))==sm.Matrix([[-516,-516,0,0]])
    assert 55*(V.row(3)-V.row(2))==sm.Matrix([[-516,516,0,0]])
    pre=sm.Matrix([1,1,-1,-1])
    assert P[:,2:]==sm.zeros(4,1).row_join(pre)
    assert U[:,2:]==sm.zeros(4,1).row_join(5*pre)
    assert V[:,2:]==sm.zeros(4,1).row_join(-F(45,2)*pre)
    print("36 projective deviations; dimension four; simultaneous integral differences verified.")

def native():
    from original_site_populations import calc
    from rank36_three_types import UNIT
    o,w,c,g,u,ub,red=calc(42,[],export=True)
    absent=[red(u[k])for k in sorted(UNIT-{(0,18),(0,24),(1,21)})]
    absent += [red(v)for k,v in ub.items()if str(k).startswith('compat')]
    N=sm.Matrix.hstack(*sm.Matrix(absent).nullspace())
    m=w((2,22));f=F(1,2)*w((0,14)); s=w((1,23))-99*o-14*f; r=w((1,21));n=w((0,18))
    test=lambda v:not any(sm.Matrix([red(v)])*N)
    assert test(6*n-291*o+17*r-32*f-5*m-2*s)
    assert test(g((4,44))-216*o+44*r-48*f-32*m-4*s)
    names={str(k):v for k,v in ub.items()};names['S']=s;names['N24W']=w((0,24))
    data=[
      (600*o-g((4,44)),6563445,[('mark((3, 39), 1)',51680),("nonneg('W', (-3, 33, 1))",83782800),("nonneg('W', (-3, 35, -1))",1443812040),("nonneg('W', (-3, 37, 1))",30578240),("nonneg('W', (-2, 34, -1))",91734720),("nonneg('C', (-4, 46, -1))",5116320),("nonneg('C', (0, 14, 0))",8138592),('S',8374200)]),
      (g((0,18))-177*o,71400,[("nonneg('W', (-4, 44, 1))",13685),("nonneg('W', (-4, 46, 2))",215985),("nonneg('W', (-3, 33, 1))",766360),("nonneg('W', (-3, 35, -1))",16833740),("nonneg('W', (-3, 37, 1))",13685),("nonneg('W', (0, 22, 0))",108800),("nonneg('C', (-4, 46, -1))",215985),("nonneg('C', (0, 14, 0))",311311)]),
      (F(943,2)*o-g((0,18)),279116215980,[('w14',1821229785186),("nonneg('W', (-3, 37, 1))",463956008131),("nonneg('W', (-3, 51, 1))",176022),("nonneg('W', (-2, 34, -1))",1391811521331),("nonneg('C', (-4, 46, -1))",3168396),("nonneg('C', (-2, 22, 0))",2162730618072),('S',14883859760),('N24W',1674876)])
    ]
    for target,den,cs in data:
        z=den*target
        for k,h in cs:
            assert h>0;z-=h*names[k]
        assert test(z)
    print("G444<=600, 177<=N18<=943/2, two raw/normalized scalar identities verified.")
if __name__=='__main__':projected();native()
