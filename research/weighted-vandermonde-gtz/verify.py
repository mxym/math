"""Exact replay of constructive weighted polynomial selection. Standard library only."""
from fractions import Fraction as F
from itertools import combinations
from math import prod
from random import Random

def need(condition, text):
    if not condition:
        raise ValueError(text)

def select(items,r):
    """item=(id,x,w,p). Inputs rational; in output weights w are unchanged."""
    need(r>=1 and all(w>0 and p>0 for _,_,w,p in items)
         and sum(p for *_,p in items)==1,'invalid input')
    groups={}
    for id0,x,w,p in items:
        if x in groups:
            id1,w1,total=groups[x]
            groups[x]=(id0 if w>w1 else id1, max(w,w1), total+p*w)
        else:
            groups[x]=(id0,w,p*w)
    rows=[(i,x,w,total/w) for x,(i,w,total) in sorted(groups.items())]
    need(len(rows)>=r,'rank lost')
    if r==1:
        return (max(rows,key=lambda row:row[2])[0],)
    while len(rows)>2*r-1:
        chosen=rows[:2*r]
        c=[1/(w*prod(x-y for _,y,_,_ in chosen if x!=y)) for _,x,w,_ in chosen]
        if sum(c)<0:
            c=[-a for a in c]
        t=min(row[3]/a for row,a in zip(chosen,c) if a>0)
        rows=[(i,x,w,p-t*a) for (i,x,w,p),a in zip(chosen,c) if p>t*a]+rows[2*r:]
    q=len(rows);total=sum(row[3] for row in rows)
    need(0<total<=1 and r<=q<=2*r-1,'mass or rank trouble')
    rows=[(i,x,w,p/total) for i,x,w,p in rows]
    if q==r:
        return tuple(sorted(i for i,*_ in rows))
    dual=[]
    for i,x,w,p in rows:
        derivative=prod(x-y for _,y,_,_ in rows if x!=y)
        dual.append((i,x,1/(p*(1-p)*w*derivative**2),p))
    J=set(select(dual,q-r))
    return tuple(sorted(i for i,*_ in rows if i not in J))

def gram_diff(items,I,r):
    return [[sum((int(i in I)-p)*w*x**(k+j) for i,x,w,p in items)
             for j in range(r)] for k in range(r)]

def det(A):
    if not A:return F(1)
    B=[list(r) for r in A];v=F(1)
    for i in range(len(B)):
        j=next((j for j in range(i,len(B)) if B[j][i]),None)
        if j is None:return F(0)
        if i!=j:
            B[i],B[j]=B[j],B[i]; v=-v
        piv=B[i][i];v*=piv
        for t in range(i+1,len(B)):
            fac=B[t][i]/piv
            for k in range(i+1,len(B)):
                B[t][k]-=fac*B[i][k]
    return v

def psd(H):
    for k in range(1,len(H)+1):
        for J in combinations(range(len(H)),k):
            if det([[H[i][j] for j in J] for i in J])<0:
                return False
    return True

def check(items,r):
    I=select(items,r)
    need(len(set(I))==r and len({x for i,x,*_ in items if i in I})==r
         and psd(gram_diff(items,I,r)),'selector does not dominate')
    return I

def test():
    rng=Random(20261118);count=0
    for r in range(1,7):
        for n in [r,r+1,2*r-1,2*r,2*r+4]:
            for seed in range(4):
                nodes=[F(i*(seed+2),1+i%3) for i in range(n)]
                # Ensure rank even when a collision was introduced.
                if len(set(nodes))<r: nodes=list(map(F,range(n)))
                w=[F(rng.randint(1,13),rng.randint(1,9)) for _ in nodes]
                p=[F(rng.randint(1,7),rng.randint(1,7)) for _ in nodes]
                P=sum(p); items=[(i,x,b,a/P) for i,(x,b,a) in enumerate(zip(nodes,w,p))]
                check(items,r);count+=1
    print('exact original-weight Gram PSD by every principal minor:',count,'test cases')

    for r in range(1,6):
        xs=list(map(F,range(r+1))); mult=[1+i%3 for i in range(r+1)]
        n=sum(mult);items=[]
        for j,(x,m) in enumerate(zip(xs,mult)):
            z2=(1-F(m,n))/r; dp=prod(x-y for y in xs if y!=x)
            w=1/(m*z2*dp*dp)
            for _ in range(m):
                items.append((len(items),x,w,F(1,n)))
        check(items,r)
        # All full-rank selections have zero determinant of the difference.
        for I in combinations(range(n),r):
            if len({items[i][1] for i in I})<r: continue
            H=gram_diff(items,I,r)
            need(psd(H) and det(H)==0,'sharp fixture')
    print('all nonsingular selections exactly saturate the repeated-node fixtures, ranks 1–5')

if __name__=='__main__':test()
