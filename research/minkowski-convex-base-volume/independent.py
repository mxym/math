"""Exact tests of two different injections, including degeneracies. Not a proof."""
from fractions import Fraction as F
from itertools import combinations, product
from math import gcd

def need(pred,msg):
    if not pred:raise ArithmeticError(msg)
def add(x,y):return (x[0]+y[0],x[1]+y[1])
def sub(x,y):return (x[0]-y[0],x[1]-y[1])
def dot(x,y):return x[0]*y[0]+x[1]*y[1]
def sq(x):return dot(x,x)
def plus(A,B):return {add(a,b) for a in A for b in B}

class Poly:
    def __init__(self,V,reverse=False):
        self.V=sorted(set(V)); vv=self.V
        normals={(1,0),(0,1),(-1,0),(0,-1)}
        for a,b in combinations(vv,2):
            x,y=sub(a,b); g=gcd(x,y);x//=g;y//=g
            normals.update(((x,y),(-x,-y),(-y,x),(y,-x)))
        self.U=sorted(normals,reverse=reverse)
        self.h=[max(dot(u,v) for v in vv) for u in self.U]
        # Every polygonal boundary edge is listed. For degenerate polytopes
        # the exposed face may be the full segment (or isolated point).
        self.edges=set()
        for u,h in zip(self.U,self.h):
            face=[v for v in vv if dot(u,v)==h]
            self.edges.add((min(face),max(face)))
    def inside(self,x):
        return all(dot(u,x)<=h for u,h in zip(self.U,self.h))
    def project(self,x):
        if self.inside(x):return x
        candidates=[]
        for a,b in self.edges:
            v=sub(b,a)
            t=0 if a==b else min(1,max(0,F(dot(v,sub(x,a)),sq(v))))
            candidates.append(add(a,(t*v[0],t*v[1])))
        return min(candidates,key=lambda v:sq(sub(x,v)))

polys=[[(0,0)],[(1,-1),(-2,2)],[(0,-1),(3,0),(0,2)],[(2,0),(1,2),(-2,1),(-1,-1)]]
shifts=[[(2,1)],[(-1,-1),(0,0),(2,2)],[(-1,-1),(1,-1),(1,1),(-1,1),(0,0)],[(2,-1),(0,2),(-2,0)]]
def main():
    count=ties=different=0
    for V,B,r in product(polys,shifts,(False,True)):
        K=Poly(V,r); Q=Poly(plus(V,B)); images=[set(),set()]
        hb=[max(dot(u,b) for b in B) for u in K.U]
        bs=[next(b for b in B if dot(u,b)==h) for u,h in zip(K.U,hb)]
        for x in product(range(-4,5),repeat=2):
            if K.inside(x):continue
            p=K.project(x); n=sub(x,p); maxval=max(dot(n,b) for b in B)
            sel=[b for b in B if dot(n,b)==maxval]
            b=sel[0]; y=add(x,b); ties+=len(sel)>1
            need(Q.project(y)==add(p,b),'residual')
            need(not Q.inside(y) and y not in images[0],'projection image')
            images[0].add(y)
            i=next(k for k,(u,h) in enumerate(zip(K.U,K.h)) if dot(x,u)>h)
            v=add(x,bs[i])
            j=next(k for k,(u,h,g) in enumerate(zip(K.U,K.h,hb)) if dot(v,u)>h+g)
            need(i==j and not Q.inside(v) and v not in images[1],'support-layer image')
            images[1].add(v)
            count+=1; different+=y!=v
        need(len(images[0])==len(images[1]),'image count')
    need(count>2000 and ties>100 and different>100,'coverage')
    print(f'PASS: {count} exterior point comparisons; {ties} tied support maxima; {different} distinct choices between the two maps.')
if __name__=='__main__':main()
