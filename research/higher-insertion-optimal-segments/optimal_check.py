"""Exact finite consistency tests for gap formulas and multi-double constructions.
The asymptotic estimates and quantifiers are proved analytically in OPTIMUM.md.
"""
from collections import Counter
from itertools import combinations,product
from math import comb,prod
def require(x,msg):
    if not x: raise ArithmeticError(msg)
def erase(w,s):return ''.join(a for i,a in enumerate(w) if i not in s)
def flip(a):return '1' if a=='0' else '0'
def defs(w):return sum(a==b for a,b in zip(w,w[1:]))
def augmented(x,w):return flip(w[0])+x+flip(w[-1])
def grouped_mask(n,k):
    return (set(s) for s in combinations(range(n),k))
def emb(w,x):
    # Read left to right. The number of skipped sites is bounded along THIS
    # embedding by the final length gap; states outside that range cannot return.
    n=len(w);k=n-len(x);p=[1]+[0]*k
    for i,a in enumerate(w):
        v=[0]*(k+1)
        for h,t in enumerate(p):
            if not t:continue
            j=i-h
            if 0<=j<len(x) and x[j]==a:v[h]+=t
            if h<k:v[h+1]+=t
        p=v
    return p[k]
def seeds(lengths):
    w=''
    for l in lengths:
        a=w[-1] if w else '0'
        w+=((a+flip(a))*((l+1)//2))[:l]
    return w
def gap_basis():
    maxima=rows=0
    for n in range(4,11):
        for z in product('01',repeat=n-1):
            w='0'+''.join(z)
            D=defs(augmented(w,w))
            for k in range(1,min(5,n-1)+1):
                h=Counter(erase(w,s) for s in grouped_mask(n,k))
                for x,v in h.items():
                    d=defs(augmented(x,w))
                    require(d<=D+k,(w,k,x,d,D))
                    if d==D+k:
                        require(v==1,(w,k,x,'nonunique maximal-defect'));maxima+=1
                    if D==0:
                        require((k-d)%2==0,('parity',w,k,x))
                        t=(k-d)//2
                        require(v==comb(n-k+t,t),('alternating stars-and-bars',w,k,x))
                rows+=1
    print('exhaustive (host,radius) rows',rows,'maximal-defect fibers',maxima)
def multi():
    tests=0
    for k in (4,5,6,8):
        for b in (2,3,4):
            ell=140;w=seeds([ell]*b);n=len(w);a=seeds([n])
            bonds=[i for i in range(n-1) if w[i]==w[i+1]]
            require(len(bonds)==b-1,'native count')
            for p in bonds:
                for j in (p,p+1):
                    s={j,*list(range(8,8+5*(k-1),5))}
                    x=erase(w,s);xd=emb(w,x);xa=emb(a,erase(a,s))
                    require((xd,xa)==(2,1),(b,k,'lost',s,xd,xa));tests+=1
            for segment in range(b):
                j=ell*segment+70
                s={j,j+1,*list(range(8,8+5*(k-2),5))}
                x=erase(w,s); val=emb(w,x)
                lo=ell*segment+(segment>0)
                hi=ell*(segment+1)-(segment+1<b)
                keep=hi-lo-sum(lo<=p<hi for p in s)
                require(keep+1<=val<=keep+1+2*(b-1),(b,k,segment,keep,val))
                require(emb(a,erase(a,s))==n-k+1,'reference pair');tests+=1
    print('multi-double pivot-loss and adjacent-pair embedding-DP checks',tests)
def discrete():
    # G(b+1)>G(b) exactly when (b+1)^(k−1)>4 b^(k−1).
    for k in range(4,201):
        crosses=[(i+1)**(k-1)-4*i**(k-1) for i in range(1,2*k+1)]
        require(0 not in crosses,k)
        b=1+sum(x>0 for x in crosses)
        require(2<=b<=k and all(x>0 for x in crosses[:b-1]) and all(x<0 for x in crosses[b-1:]),k)
    print('unique discrete maxima checked exactly for k=4..200')
if __name__=='__main__':gap_basis();multi();discrete()
