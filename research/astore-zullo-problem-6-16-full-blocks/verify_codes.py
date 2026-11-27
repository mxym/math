#!/usr/bin/env python3
"""Independent tower-field replay: code weights, duality examples, tangent carriers."""
from collections import Counter
from itertools import combinations, product

if not __debug__:
    raise RuntimeError("Run without -O; assertions are the checks.")

class Tower:
    def __init__(self,q,core):
        self.q,self.m=q,len(core)
        self.Q=q**self.m
        self.E=tuple(range(self.Q))
        self.B=tuple(range(q))
        if q==4:
            T=((0,0,0,0),(0,1,2,3),(0,2,3,1),(0,3,1,2))
            A=lambda x,y:x^y
            M=lambda x,y:T[x][y]
            N=lambda x:x
        else:
            A=lambda x,y:(x+y)%q
            M=lambda x,y:x*y%q
            N=lambda x:(-x)%q
        V=[tuple(i//q**j%q for j in range(self.m)) for i in self.E]
        def encode(v):
            return sum(a*q**i for i,a in enumerate(v))
        self.A=[[encode(A(x,y) for x,y in zip(u,v)) for v in V] for u in V]
        self.N=[encode(N(x) for x in u) for u in V]
        def mul(u,v):
            a=[0]*(2*self.m-1)
            for i,x in enumerate(u):
                for j,y in enumerate(v):
                    a[i+j]=A(a[i+j],M(x,y))
            for j in range(len(a)-1,self.m-1,-1):
                b=N(a[j])
                for i,c in enumerate(core):
                    k=j-self.m+i
                    a[k]=A(a[k],M(b,c))
            return encode(a[:self.m])
        self.M=[[mul(u,v) for v in V] for u in V]
        self.I=[0]+[self.M[x].index(1) for x in self.E[1:]]
        self.frob=[self.power(a,q) for a in self.E]
        self.norm=[self.power(a,(self.Q-1)//(q-1)) for a in self.E]
        assert set(self.norm)==set(self.B)
        assert {a for a in self.E if self.frob[a]==a}==set(self.B)

    def power(self,x,k):
        z=1
        while k:
            if k&1:
                z=self.M[z][x]
            x=self.M[x][x]
            k>>=1
        return z

    def sub(self,x,y):
        return self.A[x][self.N[y]]

    def smul(self,a,v):
        return tuple(self.M[a][x] for x in v)

    def plus(self,u,v):
        return tuple(self.A[x][y] for x,y in zip(u,v))

    def dot(self,u,v):
        a=0
        for x,y in zip(u,v):
            a=self.A[a][self.M[x][y]]
        return a

    def normalize(self,v):
        return self.smul(self.I[next(x for x in v if x)],v)

    def rank(self,values):
        d=0
        S={0}
        for a in values:
            if a in S:
                continue
            d+=1
            S={self.A[x][self.M[c][a]] for x in S for c in self.B}
        assert len(S)==self.q**d
        return d

    def cross(self,u,v):
        return tuple(self.sub(self.M[u[i]][v[j]],self.M[u[j]][v[i]])
                     for i,j in ((1,2),(2,0),(0,1)))

    def points(self,k):
        for i in range(k):
            for tail in product(self.E,repeat=k-i-1):
                yield (0,)*i+(1,)+tail

def lrs_blocks(K):
    a_list=[next(x for x in K.E if K.norm[x]==i) for i in K.B[1:]]
    k=K.m+1
    betas=[K.q**i for i in range(K.m)]
    B=[]
    for a in a_list:
        columns=[]
        for b in betas:
            L=[b]
            for _ in range(k-1):
                L.append(K.M[a][K.frob[L[-1]]])
            columns.append(tuple(L))
        B.append(tuple(columns))
    return B

def distance(K,k,blocks):
    hist=Counter()
    for h in K.points(k):
        d=sum(K.rank([K.dot(h,v) for v in block]) for block in blocks)
        hist[d]+=1
    assert sum(hist.values())==(K.Q**k-1)//(K.Q-1)
    return min(hist),hist

def circle(K,r):
    # A genuine F-basis of the graph of the Mobius-parametrized norm circle.
    theta=K.q
    bar=K.frob[theta]
    assert theta!=bar
    a=next(x for x in K.E if K.norm[x]==r)
    return ((K.N[bar],K.N[K.M[a][theta]]),(1,a))

def triangle_blocks(K,radii):
    out=[]
    for i,r in enumerate(radii):
        B=[]
        for x,y in circle(K,r):
            H=[0]*3
            H[(i+1)%3]=x
            H[(i+2)%3]=y
            B.append(tuple(H))
        out.append(tuple(B))
    return out

def semilinear_on_block(K,B,p):
    u,v=B
    r,s=next((i,j) for i,j in combinations(range(3),2)
             if K.M[u[i]][v[j]] != K.M[u[j]][v[i]])
    x=K.sub(K.M[p[r]][v[s]],K.M[p[s]][v[r]])
    y=K.sub(K.M[u[r]][p[s]],K.M[u[s]][p[r]])
    # Omit the common Cramer denominator; it drops out on normalization.
    return K.normalize(K.plus(K.smul(K.frob[x],u),K.smul(K.frob[y],v)))

def carrier_check(K,B):
    points=[set(K.normalize(K.plus(K.smul(a,u),K.smul(b,v)))
                for a,b in product(K.B,repeat=2) if a or b) for u,v in B]
    supports=[K.normalize(K.cross(*x)) for x in B]
    assert all(len(S)==K.q+1 for S in points)
    assert len(set.union(*points))==12
    hits=0
    T=[]
    for i,S in enumerate(points):
        outside=set.union(*(x for j,x in enumerate(points) if i!=j))
        for p in S:
            unused={h for h in K.points(3) if not K.dot(h,p) and
                    all(K.dot(h,x) for x in outside)}
            assert len(unused)==2 and supports[i] in unused
            tau=next(iter(unused-{supports[i]}))
            assert all(K.dot(tau,x) for x in (S-{p}))
            for j,block in enumerate(B):
                if j==i:
                    continue
                Q=K.normalize(K.cross(supports[i],supports[j]))
                R=semilinear_on_block(K,block,Q)
                assert R!=Q and K.dot(tau,R)==0 and K.dot(supports[i],R)!=0
                hits+=1
            T.append(tau)
    assert hits==24
    allpts=set.union(*points)
    line_sizes=Counter(sum(K.dot(h,x)==0 for x in allpts) for h in K.points(3))
    assert line_sizes=={0:28,1:12,2:48,4:3}
    assert len(set(T))==12
    print("q=3 triangle: 12 tangents, 24 independent Frobenius carrier checks PASS")

def main():
    for q,core in ((3,(2,1)),(4,(2,1)),(5,(3,0)),(3,(2,2,0))):
        K=Tower(q,core)
        B=lrs_blocks(K)
        d,h=distance(K,K.m+1,B)
        assert d==(q-1)*K.m-K.m
        print(f"q={q}, m={K.m}: {sum(h.values())} rays; "
              f"t={len(B)}, d_SR={d}; weight histogram {sorted(h.items())}")
    K=Tower(3,(2,1))
    for r in product((1,2),repeat=3):
        B=triangle_blocks(K,r)
        d,_=distance(K,3,B)
        good=(r[0]*r[1]*r[2])%3==2
        assert (d==4)==good
    carrier_check(K,triangle_blocks(K,(2,2,2)))
    print("q=3 all eight radius triples: four positive, four negative controls PASS")
    print("PASS direct code and projection checks")

if __name__=="__main__":
    main()
