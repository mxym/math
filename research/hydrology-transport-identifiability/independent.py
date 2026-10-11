#!/usr/bin/env python3
"""Independent four-store certificate checker; imports no research module.
Uses direct polynomial convolution and exact quadratic minimization rather
than the main checker's Bernstein-basis certificate and elimination code.
"""
from fractions import Fraction as F
from itertools import permutations
import json


def mm(a,b):
    return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]

def add(a,b): return [[x+y for x,y in zip(ra,rb)] for ra,rb in zip(a,b)]
def sc(s,a): return [[s*x for x in row] for row in a]
def pm(a,b):
    out=[[[F(0)]*len(b[0][0]) for _ in a[0]] for _ in range(len(a)+len(b)-1)]
    for i,x in enumerate(a):
        for j,y in enumerate(b): out[i+j]=add(out[i+j],mm(x,y))
    return out

def pad(a,n): return a+[[[F(0)]*len(a[0][0]) for _ in a[0]] for _ in range(n-len(a))]
def padd(a,b): return [add(x,y) for x,y in zip(pad(a,max(len(a),len(b))),pad(b,max(len(a),len(b))))]
def same(a,b):
    n=max(len(a),len(b))
    if pad(a,n)!=pad(b,n): raise RuntimeError('Polynomial identity rejected')
def ev(c,t):return sum(x*t**j for j,x in enumerate(c))
def det(a):
    n=len(a);s=F(0)
    for p in permutations(range(n)):
        v=F((-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n)))
        for i,j in enumerate(p):v*=a[i][j]
        s+=v
    return s

def run():
    k=[[F(x,100) for x in r] for r in [[-7,3,1,2],[4,-9,3,1],[2,4,-8,3],[1,2,4,-6]]]
    q=[[F(x,100) for x in [8,1,2,4]]];e=[[F(x,100) for x in [8,4,1,0]]]
    dq=[[q[0][i] if i==j else F(0) for j in range(4)] for i in range(4)]
    de=[[e[0][i] if i==j else F(0) for j in range(4)] for i in range(4)]
    a=add(k,sc(-1,dq));b=[[F(int(i==0))] for i in range(4)]
    h=[[F(1)]*4]+q+e;i=[[F(x==y) for y in range(4)] for x in range(4)]
    n=mm([[F(x,5)] for x in [-1,4,-8,5]],[[F(0),F(2),F(1),F(0)]])
    t=[i,n];ti=[i,sc(-1,n)]
    aa=pm(pm(t,[a]),ti)
    k0=padd(aa,[dq]);k1=padd([de],[sc(-1,x) for x in pm(pm(t,[de]),ti)])
    same(pm(t,ti),[i]);same(pm([h],t),[h]);same(pm(t,[b]),[b])
    same(pm(aa,t),pm(t,[a]))
    same(pm(padd(k1,[sc(-1,de)]),t),pm(t,[sc(-1,de)]))
    bounds=(F(-1,10),F(1,8));minima=[]
    for u in [F(0),F(1)]:
        rates=padd(k0,[sc(u,x) for x in k1])
        same(pm([h[:1]],rates),[[[F(0)]*4]])
        for ii in range(4):
            for jj in range(4):
                if ii==jj:continue
                c=[r[ii][jj] for r in rates]
                pts=list(bounds)
                if c[2]>0:
                    vertex=-c[1]/(2*c[2])
                    if bounds[0]<vertex<bounds[1]:pts.append(vertex)
                minimum=min(ev(c,p) for p in pts)
                if minimum<0: raise RuntimeError('Negative physical transfer')
                minima.append(minimum)
    z01=pm(pm(pm([q],k1),aa),[b])
    same(z01,[[[F(0)]],[[F(-2,15625)]]])
    r=[];v=b
    for _ in range(4):r.append([row[0] for row in v]);v=mm(a,v)
    r=list(map(list,zip(*r)));o=[];v=q
    for _ in range(4):o.append(v[0]);v=mm(v,a)
    if det(r)!=F(2197,10**12) or det(o)!=F(-23163231,10**20):
        raise RuntimeError('Independent determinant failure')
    return {'status':'PASS','method':'independent polynomial convolution and exact quadratic minima',
            'research_module_imports':0,'exact_quadratic_minima_checked':len(minima),
            'minimum_transfer_on_rectangle':str(min(minima)),
            'controllability_determinant':str(det(r)),'observability_determinant':str(det(o)),
            'retained_mixed_fingerprint':'-2*theta/15625','scope':'four-store witness only; not a general formal proof'}
if __name__=='__main__': print(json.dumps(run(),indent=2,sort_keys=True))
