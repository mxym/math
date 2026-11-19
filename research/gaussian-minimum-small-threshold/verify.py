"""Exact finite diagnostics; the analytic theorem does not rely on these ranges."""
from fractions import Fraction as Q
from itertools import combinations,product

def check(cond,msg):
    if not cond:raise ArithmeticError(msg)

def cycle(n,mask):
    active=[bool((mask>>i)&1) for i in range(n)]
    edges=sum(a and active[(i+1)%n] for i,a in enumerate(active))
    comp=sum(a and not active[i-1] for i,a in enumerate(active))
    left=max(sum(active)-1,0); right=edges-int(all(active))
    check(left>=right,'cycle inequality')
    check((left==right)==(comp<=1),'proper cyclic blocks')
nc=0
for n in range(2,16):
    for mask in range(2**n):
        cycle(n,mask);nc+=1

def det(a,b):return a[0]*b[1]-a[1]*b[0]
def sub(a,b):return tuple(i-j for i,j in zip(a,b))
def dot(a,b):return sum(i*j for i,j in zip(a,b))
def hull(p):
    p=sorted(set(p))
    if len(p)<3:return p
    def half(pp):
        s=[]
        for x in pp:
            while len(s)>=2 and det(sub(s[-1],s[-2]),sub(x,s[-1]))<=0:s.pop()
            s.append(x)
        return s
    return half(p)[:-1]+half(p[::-1])[:-1]
def norm(a):return tuple(-j for j in a)
def area_poly(a,b):
    normals=a+[norm(v) for v in a]; sup=[1-x for x in b]+[1+x for x in b]
    pp=[]
    for i,j in combinations(range(len(normals)),2):
        (x,y),(z,w)=normals[i],normals[j];r,s=sup[i],sup[j];d=x*w-y*z
        if not d:continue
        v=((w*r-y*s)/d,(x*s-z*r)/d)
        if all(dot(u,v)<=t for u,t in zip(normals,sup)):pp.append(v)
    p=hull(pp)
    return sum(det(x,p[(i+1)%len(p)]) for i,x in enumerate(p))/2 if len(p)>2 else Q(0)
def dire(q):
    q=Q(q);return ((1-q*q)/(1+q*q),2*q/(1+q*q))
def local_area(a,b):
    normals=a+[norm(v) for v in a];sup=[1-x for x in b]+[1+x for x in b]
    out=0
    for i,u in enumerate(normals):
        j=(i+1)%len(normals);v=normals[j];d=det(u,v);r,s=sup[i],sup[j]
        out+=(r*s-(r*r+s*s)*dot(u,v)/2)/d
    return out
pc=0;layers=0
for ts in ((0,Q(1,3),2),(0,Q(1,3),1,4),(0,Q(1,4),Q(1,2),1,3),(0,Q(1,4),Q(1,2),1,2,4)):
    a=[dire(q) for q in ts]; n=len(a)
    base=area_poly(a,[Q(0)]*n);check(base==local_area(a,[0]*n),'central area')
    gaps=list(zip(a, a[1:]+[norm(a[0])]))
    check(base==2*sum((1-dot(v,w))/det(v,w) for v,w in gaps),'tangent polygon area')
    check(4*sum(1/det(v,w) for v,w in gaps)-base==2*sum((1+dot(v,w))/det(v,w) for v,w in gaps),'cot deficits')
    # A^T b=0 exactly, so every nonzero offset here is transverse.
    for outer in product((-1,0,1),repeat=n-2):
        if not any(outer):continue
        e=tuple(sum(a[i+2][k]*v for i,v in enumerate(outer)) for k in range(2));den=det(a[0],a[1])
        b=[-det(e,a[1])/den,-det(a[0],e)/den,*map(Q,outer)]
        check(all(sum(q*v[k] for q,v in zip(b,a))==0 for k in range(2)),'transverse')
        s0=[q/1000 for q in b];s1=[2*q for q in s0]
        a0=area_poly(a,s0);a1=area_poly(a,s1)
        check(a0==local_area(a,s0) and a1==local_area(a,s1),'exact polygon perturbation')
        check(base>a0 and base-a1==4*(base-a0),'strict and quadratic perturbation')
        vals=[area_poly(a,[q*z for q in b]) for z in [Q(0),Q(1,20),Q(1,4),Q(1,2),Q(1),Q(2),Q(10)]]
        check(all(x>=y for x,y in zip(vals,vals[1:])) and vals[-1]==0,'far ray monotonicity and empty fiber')
        pc+=1;layers+=len(vals)
print(f'PASS: {nc} exact cyclic masks; {pc} rational polygon/offset directions; {layers} exact centered-to-far fiber areas')
