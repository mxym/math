#!/usr/bin/env python3
"""Exact controls, not a numerical proof of the asymptotic counting theorem."""
from itertools import combinations, product
from math import gcd,isqrt
from functools import reduce
import hashlib,random

def req(ok,what):
    if not ok: raise ValueError(what)
def signature(x,t):
    vals=[]
    for p in x:
        if p%3: vals.append(p%3)
        else: t=-t%3;vals.append(t)
    return vals+[t]
def schedule(P,Q,t):
    us=signature(P,t); ws=signature(Q,t)
    delta=us.count(1)-ws.count(1)
    req(delta%3==0,'sum sign')
    left=[i for i,a in enumerate(us) if a==(1 if delta>0 else 2)][:abs(delta)]
    # indices in increasing order, so d+1 if present can only be Z
    tri=[tuple(left[i:i+3]) for i in range(0,len(left),3)]
    for a,b,c in tri:req(max(a,b)<len(P),'terminal in head pair')
    V=[(('U',i),u) for i,u in enumerate(us) if i not in left]
    for j,(a,b,c) in enumerate(tri):
        for k in ('T','C','D'):V.append(((k,j),(-us[a])%3))
    ordered=[]
    for w in [ws[-1]]+ws[:-1]:
        i=next(i for i,(_,v) in enumerate(V) if v==w)
        ordered.append(V.pop(i)[0])
    req(not V,'bijection')
    return us,ws,tri,ordered

def sgn_vectors_test():
    n=0;converts=0;max_k=0
    for d in range(3,12):
        sigs=[(3,)*a+(7,)*b+(5,)*(d-a-b) for a in range(d+1) for b in range(d-a+1)]
        for A in sigs:
            for B in sigs:
                if (sum(A)-sum(B))%3:continue
                for t in (1,2):
                    u,w,tri,v=schedule(A,B,t);n+=1
                    converts+=bool(tri);max_k=max(max_k,len(tri))
    return n,converts,max_k

def chart(P,Q,t3):
    d=len(P);n=sum(P);req(n==sum(Q),'integer weights')
    us,ws,tri,order=schedule(P,Q,t3)
    size=d+1+len(tri)+d
    def lin0(b=0):return (b,)+(0,)*size
    def unit(i):a=list(lin0());a[1+i]=1;return tuple(a)
    def add(a,b):return tuple(x+y for x,y in zip(a,b))
    def sub(a,b):return tuple(x-y for x,y in zip(a,b))
    def SUM(arr):return reduce(add,arr,lin0())
    U=[unit(i) for i in range(d+1)]
    ts=sub(SUM(U),lin0(n))
    forms={'t':ts};pairs=[]
    for i,ui in enumerate(U):forms['u'+str(i)]=ui
    R=ts
    for i,p in enumerate(P):
        rr=sub(add(R,lin0(p)),U[i]);pairs.append((R,lin0(p),rr,U[i]));R=rr
        if i+1<d:forms['r'+str(i)]=rr
    req(R==U[-1],'end unpacking')
    coords={('U',i):u for i,u in enumerate(U)}
    for j,(x,y,z) in enumerate(tri):
        c=unit(d+1+j);v=sub(add(lin0(3),U[z]),c);tt=sub(add(U[x],U[y]),lin0(3))
        for k,f in [('T',tt),('C',c),('D',v)]:coords[k,j]=f;forms[k+str(j)]=f
        pairs.extend([(U[x],U[y],lin0(3),tt),(lin0(3),U[z],c,v)])
    V=[coords[key] for key in order]
    F=V[0];S=ts
    for i in range(d):
        w=unit(d+1+len(tri)+i);f=sub(add(F,V[i+1]),w);s=sub(add(S,lin0(Q[i])),w)
        pairs.extend([(F,V[i+1],w,f),(S,lin0(Q[i]),w,s)]);S=s;F=f
        forms['w'+str(i)]=w;forms['f'+str(i)]=f
        if i+1<d:forms['s'+str(i)]=s
    req(F==S,'end matching')
    for a,b,c,e in pairs:req(add(a,b)==add(c,e),'move identity')
    prim=[]
    for name,f in forms.items():
        v=f[1:];h=reduce(gcd,v)
        req(bool(h),'zero form '+name)
        vv=tuple(x//h for x in v)
        if next(x for x in vv if x)!=abs(next(x for x in vv if x)):vv=tuple(-x for x in vv)
        prim.append(vv)
    req(len(prim)==len(set(prim)),'parallel gradients')
    return forms,tri,order,us,ws

def first_mod(ell,bad):
    return next(k for k in range(ell) if k not in {x%ell for x in bad})

def local(P,Q,ell,t,t3,info):
    forms,tri,order,us,ws=info;d=len(P)
    if ell==3:
        req(t==t3,'mod3 anchor')
        U=us[:];C=[-us[x]%3 for x,y,z in tri];W=ws[:-1]
    elif ell==2:U=[1]*(d+1);C=[1]*len(tri);W=[1]*d
    else:
        R=t;U=[];forbid={max(x,y):min(x,y) for x,y,z in tri}
        for i,p in enumerate(P):
            bad=[0,R+p]
            if i in forbid:bad.append(3-U[forbid[i]])
            ui=first_mod(ell,bad);R=(R+p-ui)%ell;U.append(ui)
        U.append(R)
        C=[first_mod(ell,(0,3+U[z])) for x,y,z in tri]
        V={('U',i):v for i,v in enumerate(U)}
        for j,(x,y,z) in enumerate(tri):V['T',j]=U[x]+U[y]-3;V['C',j]=C[j];V['D',j]=3+U[z]-C[j]
        F=V[order[0]];S=t;W=[]
        for i,q in enumerate(Q):
            w=first_mod(ell,(0,F+V[order[i+1]],S+q));W.append(w)
            F=(F+V[order[i+1]]-w)%ell;S=(S+q-w)%ell
    point=(1,*U,*C,*W)
    values={name:sum(v*x for v,x in zip(g,point))%ell for name,g in forms.items()}
    req(values['t']==t and all(values.values()),('local',P,Q,ell,t,t3,values))
def prime(n):return n>=2 and all(n%d for d in range(2,isqrt(n)+1))
def cubic(q,a,b,t):
    req(q+1==a+b and all(map(prime,(q,a,b,t))),'bad cubic inputs')
    for d in range(t//3,2*t//3):
        c=t+1-d
        if not prime(d) or not prime(c):continue
        for u in range(3,min(q+d,t+b),2):
            v=q+d-u;w=t+b-u
            if all(map(prime,(u,v,w))):
                return [(q,c,d),(c,u,v),(u,a,w),(a,b,t)]
    raise ValueError('no fixture')
def main():
    f=sgn_vectors_test()
    tests=0
    for A,B in [((7,7,7),(5,5,11)),((3,3,13),(5,7,7)),((3,3,3,13,19),(5,5,7,11,13)),((7,)*6,(5,5,11)*2),((3,3,13,7,7,7),(5,7,7,5,5,11))]:
        for P,Q in [(A,B),(B,A)]:
            for t3 in (1,2):
                info=chart(P,Q,t3)
                for ell in (2,3,5,7,11,13,17,19,23,29,31):
                    for t in ((t3,) if ell==3 else range(1,ell)):
                        local(P,Q,ell,t,t3,info);tests+=1
    table={(1,1):((1,1),(1,1)),(1,2):((1,1),(2,2)),(2,0):((1,2),(1,1)),(2,1):((1,1),(1,1)),(2,2):((1,1),(1,2))}
    for (q,b),data in table.items():
        for t,(d,u) in enumerate(data,1):req(all(x%3 for x in (d,u,t+1-d,q+d-u,t+b-u)),'cubic mod 3')
    print('signature pairs/with conversions/max triples:',f)
    print('symbolic fixture local checks:',tests)
    for qa in [(5,3,3),(7,3,5),(13,7,7)]:
        path=cubic(*qa,1009)
        for x,y in zip(path,path[1:]):req(sum(x)==sum(y) and set(x)&set(y) and all(map(prime,x+y)),'literal move')
        print('literal cubic:',path)
    print('PASS')
if __name__=='__main__':main()
