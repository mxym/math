"""Check all unlabelled rooted trees through order 13, without external libraries."""
from math import comb,prod
from collections import Counter
def plus(a,b):
    return tuple((a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b))))
def mult(a,b):
    ans=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):ans[i+j]+=x*y
    return tuple(ans)
def choose(n,k):return comb(n,k) if 0<=k<=n else 0
size=[];io=[];slots=[];nb=Counter();instances=Counter()
def add(s,ch):
    P=(0,1);Q=(1,);N=0
    for i in ch:
        p,q=io[i];P=mult(P,q);Q=mult(Q,plus(p,q));N+=slots[i]
    if ch==(0,0,0):N+=1
    Z=plus(P,Q)
    if s>4:
        for k in range(s+1):
            bound=sum(choose(N,j)*choose(s-k-j+1,k-3*j) for j in range(N+1))
            if (Z[k] if k<len(Z) else 0)<bound:raise ValueError((s,ch,N,k,bound,Z))
            nb[s]+=1
    instances[N]+=1;size.append(s);io.append((P,Q));slots.append(N)
def generate(s,left,minid,old,seq):
    if not left:add(s,tuple(seq));return
    for j in range(minid,old):
        if size[j]>left:break
        generate(s,left-size[j],j,old,seq+[j])
if __name__=='__main__':
    for s in range(1,14):
        old=len(size);generate(s,s-1,0,old,[])
    print('Trees by number of slots:',sorted(instances.items()))
    print('Rooted unlabeled trees:',len(size),'coefficient tests at n=5..13:',sum(nb.values()))
    print('Coefficient lower bound on every enumerated tree: PASS')
