#!/usr/bin/env python3
"""Exact colored Delsarte certificates. Standard Python 3, no packages."""
import base64,zlib,json,math,heapq
from fractions import Fraction as Q
from itertools import combinations_with_replacement
DATA=["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"]
SCALAR=[[6,36,50712,999980,[89244,14268999,0,21625814]],[6,37,51373,999980,[179479,14543352,0,22260656]],[7,63,50269,999980,[57732,21525134,0,41399738]],[7,64,50531,999980,[116454,21782810,0,42085048]],[7,65,50781,999980,[174931,22040272,0,42768693]],[6,72,65921,999980,[3138357,14631677,10909408,25808592,0,6053261,0,0,11442181]],[7,126,64406,999980,[2398084,18708904,6444009,52989410,0,39248567,0,0,6193391]]]
def add(p,q):
    return [(p[j] if j<len(p) else 0)+(q[j] if j<len(q) else 0) for j in range(max(len(p),len(q)))]
def mul(p,x):return [a*x for a in p]
def bases(d,D):
    P=[[Q(1)],[Q(0),Q(1)]]
    for j in range(1,D):
        P.append(mul(add([Q(0)]+mul(P[-1],2*j+d-2),mul(P[-2],-j)),Q(1,j+d-2)))
    return P
def bern(p,L,R):
    if not p:return [Q(0)]
    n=len(p)-1
    a=[sum(p[j]*math.comb(j,h)*L**(j-h)*(R-L)**h for j in range(h,n+1)) for h in range(n+1)]
    return [sum(a[h]*Q(math.comb(t,h),math.comb(n,h)) for h in range(t+1)) for t in range(n+1)]
def kids(b):
    l=[b[0]];r=[b[-1]]
    while len(b)>1:
        b=[(a+c)/2 for a,c in zip(b,b[1:])];l.append(b[0]);r.append(b[-1])
    return l,r[::-1]
def cap(p,L,R,tol=Q(1,3000000)):
    b=bern(p,L,R);heap=[(-max(b),0,b)];num=0;low=max(b[0],b[-1])
    while -heap[0][0]>low+tol:
        _,_,a=heapq.heappop(heap)
        for b in kids(a):
            num+=1;low=max(low,b[0],b[-1]);heapq.heappush(heap,(-max(b),num,b))
        assert num<16000
    return -heap[0][0]
def main():
    for d,B,a,c,v in SCALAR:
        pp=bases(d,len(v));f=[Q(c,1000000)]
        for k,cc in enumerate(v,1):
            assert cc>=0
            if cc:f=add(f,mul(pp[k],Q(cc,1000000)))
        hi=cap(f,Q(-a,100000),Q(1,2))
        assert hi<=0 and sum(f)*1000000<c*(B+1)
        print(d,'independent cap',B,'threshold',a)
    for enc in DATA:
        d,N,m,a,den,fac=json.loads(zlib.decompress(base64.b64decode(enc)))
        a=Q(a,100000);s=[N-2*m,m,m];P=bases(d,len(fac));tot=Q(0)
        for i,j in combinations_with_replacement(range(3),2):
            f=[Q(0)]
            for k,X in enumerate(fac,1):
                if X:f=add(f,mul(P[k],Q(sum(u*v for u,v in zip(X[i],X[j])),den**2)))
            if i==j:tot+=s[i]*sum(f)
            hi=cap(f,-a if i==0 and j<2 else Q(-1),Q(1,2))
            tot+=(1+(i!=j))*s[i]*(s[j]-int(i==j))*hi
        print(d,N,'a',a,'matching',m+1,'upper micros',math.ceil(tot*10**6))
        assert tot<0, (d,N,m,a,float(tot))
if __name__=='__main__':main()
