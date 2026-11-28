"""Exact rational differential and local-point checks; no numerical logarithms or solver."""
from fractions import Fraction as F
from math import prod

def det(B):
    if not B:return F(1)
    return sum((-1)**j*v*det([r[:j]+r[j+1:] for r in B[1:]]) for j,v in enumerate(B[0]))
def lin(B,v):
    A=[r[:]+[z] for r,z in zip(B,v)];n=len(B)
    for i in range(n):
        j=next(j for j in range(i,n) if A[j][i]);A[i],A[j]=A[j],A[i]
        q=A[i][i];A[i]=[z/q for z in A[i]]
        for j in range(n):
            if j!=i:
                q=A[j][i];A[j]=[a-q*b for a,b in zip(A[j],A[i])]
    return [r[-1] for r in A]
def logjets(polys,x):
    # Ordinary x-derivatives of a product, then x*d/dx to logarithmic u.
    z,d,dd=1,0,0
    for a,b,e in polys:
        y=a*x+b
        v=y**e;v1=e*a*y**(e-1);v2=(e*(e-1)*a*a*y**(e-2) if e>=2 else 0)
        z,d,dd=z*v,d*v+z*v1,dd*v+2*d*v1+z*v2
    r=F(d,z);return x*r,x*r+x*x*(F(dd,z)-r*r)
def data(xs,labels,stationary=False):
    # Each tree is a root with two leaves of forms 2x+1 and 6x+1.
    trees=[]
    for j,(i,h) in enumerate(labels):
        slopes=(2 if i%2 else 6,2 if h%2 else 6) if stationary else (2,6)
        assert set(slopes)=={2,6}
        trees.append([(1,0,1,'root'),(slopes[0],1,i,i),(slopes[1],1,h,h)])
    return trees
def check(xs,labels,chosen,force_stationary=False):
    trees=data(xs,labels,force_stationary); t=len(xs);J=[];Hs=[]
    for idx in chosen:
        jets=[logjets([(a,b,e) for a,b,e,gr in tr if gr==idx],x) for tr,x in zip(trees,xs)]
        J.append([v for v,h in jets]);Hs.append([h for v,h in jets])
    w=[(-1)**i*det([r[:i]+r[i+1:] for r in J]) for i in range(t)]
    assert any(w)
    scale=next(v for v in w if v);w=[v/scale for v in w]
    assert all(sum(a*b for a,b in zip(row,w))==0 for row in J)
    hvals=[sum(a*b*b for a,b in zip(row,w)) for row in Hs]
    acc=lin(J+[w],[-z for z in hvals]+[F(0)])
    assert sum(a*b for a,b in zip(w,acc))==0
    gg=[];hg=[]
    for tr,x in zip(trees,xs):
        p,q=logjets([(a,b-1,1) for a,b,e,gr in tr],x)
        r,s=logjets([(a,b,1) for a,b,e,gr in tr],x)
        g,h=p-r,q-s
        assert g==sum(F(a*x,(a*x+b)*(a*x+b-1)) for a,b,e,gr in tr)
        assert h==sum(F(a*x*(b*(b-1)-(a*x)**2),(a*x+b)**2*(a*x+b-1)**2) for a,b,e,gr in tr)
        gg.append(g);hg.append(h)
    dot=sum(a*b for a,b in zip(gg,w)); norm=sum(a*a for a in w)
    sec=(sum(hh*wi*wi for hh,wi in zip(hg,w))+sum(a*b for a,b in zip(gg,acc)))/norm
    assert sec<0
    if force_stationary:assert dot==0
    return dot==0,sec
xs4=(1013,1103,1451,1481);c4=((1,2),(2,3),(3,4),(4,1))
xs5=xs4+(1511,);c5=((1,1),(1,2),(2,3),(3,4),(4,4))
tally=stationary=large=0
for scale in (1,3,9):
    for X,C,rows in ((xs4,c4,(1,2,3)),(xs5,c5,(1,2,3,4))):
        stat,sec=check([v*scale for v in X],C,rows)
        stationary+=stat;tally+=1
for x in (1013,10**400):
    stat,sec=check([x]*4,c4,(1,2,3),True);tally+=1;stationary+=stat
    if x>1013:
        k,A=12,9;trees=data([x]*4,c4,True)
        N=prod((a*x+b)**e for tr in trees for a,b,e,idx in tr)
        Z=k*k*(A+1)**(k+1)*N.bit_length()
        assert x>16*A*k*k*Z**k and sec < -F(1,2*A*x)
        large+=1
# Deficiency two can leave a real interval for the exact positive equations.
D=101*103*107;K=100*102*106;live=0
for shift in range(-5,6):
    x=101+F(shift,100); yz=F(D,x);s=1+yz-F(K,x-1)
    assert s>0 and yz>0 and s*s-4*yz>0;live+=1
print("exact tangent/acceleration fixtures",tally,"strict stationary contacts",stationary,
      "inside explicit large-domain cutoff",large)
print("positive discriminants at deficiency-two rational sample points",live)
