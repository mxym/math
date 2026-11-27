#!/usr/bin/env python3
"""Finite-field recurrence, cyclic monodromy, and independent curve arithmetic."""
from math import comb, isqrt


class QuadraticField:
    # Encoded residue a+p*b means a+b*u, u^2=ns.
    def __init__(self, p):
        self.p = p
        self.q = p*p
        squares = {i*i % p for i in range(p)}
        self.ns = p-1 if p-1 not in squares else next(i for i in range(2,p) if i not in squares)
        self.invtab = [0]*self.q
        self.sqroots = [[] for _ in range(self.q)]
        for s in range(self.q):
            a, b = self.coords(s)
            if s:
                c = pow((a*a-self.ns*b*b) % p,-1,p)
                self.invtab[s] = self.encode(a*c,-b*c)
                assert self.mul(s,self.invtab[s]) == 1
            self.sqroots[self.mul(s,s)].append(s)

    def coords(self, x):
        return x % self.p, x // self.p

    def encode(self, a, b=0):
        return a % self.p + self.p*(b % self.p)

    def add(self, x, y):
        a, b = self.coords(x)
        c, d = self.coords(y)
        return self.encode(a+c,b+d)

    def sub(self, x, y):
        a, b = self.coords(x)
        c, d = self.coords(y)
        return self.encode(a-c,b-d)

    def mul(self, x, y):
        a, b = self.coords(x)
        c, d = self.coords(y)
        return self.encode(a*c+self.ns*b*d,a*d+b*c)

    def div(self, x, y):
        assert y
        return self.mul(x,self.invtab[y])

    def pow(self, x, n):
        s = 1
        for i in range(n):
            s = self.mul(s,x)
        return s


def verify(p, depth):
    f = QuadraticField(p)
    c,A,S,M,D,P = f.encode,f.add,f.sub,f.mul,f.div,f.pow

    def jval(v):
        z = P(v,4)
        bz = S(P(z,2),z)
        return D(M(c(256),P(A(bz,1),3)),P(bz,2))

    pool = {v for v in range(1,f.q) if P(v,4)!=1}
    adj = {v: tuple(w for w in f.sqroots[D(A(v,f.invtab[v]),c(2))] if w in pool) for v in pool}
    jvals = {v:jval(v) for v in pool}
    tallies = [0]*(depth+1)
    j3 = t5 = torsion = 0
    triangle103 = set()

    def on_curve(a,b,Q):
        if Q is None:
            return True
        x,y=Q
        return P(y,2)==M(x,M(S(x,P(a,2)),S(x,P(b,2))))

    def add_curve(a,b,Q,R):
        if Q is None:
            return R
        if R is None:
            return Q
        x,y=Q
        u,v=R
        a2, b2 = P(a,2),P(b,2)
        if x!=u:
            slope=D(S(v,y),S(u,x))
        elif A(y,v)==0:
            return None
        else:
            slope=D(A(S(M(c(3),P(x,2)),M(c(2),M(A(a2,b2),x))),M(a2,b2)),M(c(2),y))
        xx = S(S(A(P(slope,2),A(a2,b2)),x),u)
        return xx,S(M(slope,S(x,xx)),y)

    def iso(a,b,Q):
        if Q is None or Q[0]==0:
            return None
        x,y=Q
        ab=M(a,b)
        return D(P(A(x,ab),2),M(c(4),x)),D(M(y,S(P(x,2),P(ab,2))),M(c(8),P(x,2)))

    def handoff(seq,w):
        aa=1
        bb=f.invtab[P(seq[0],2)]
        b0=bb
        chain=[]
        for i,v in enumerate(seq):
            chain.append((aa,bb))
            aa,bb=D(A(aa,bb),c(2)),D(aa,v)
            nxt=seq[(i+1)%len(seq)]
            assert D(bb,aa)==f.invtab[P(nxt,2)]
        assert aa==w and bb==M(w,b0)
        a1,b1=chain[-1]
        d0=D(D(S(a1,b1),c(2)),w)
        assert P(d0,2)==S(1,P(b0,2))

        def scale(Q):
            if Q is None:
                return None
            return D(Q[0],P(w,2)),D(Q[1],P(w,3))

        def end(Q):
            for i,(a,b) in enumerate(chain):
                Q=iso(a,b,Q)
                aa,bb=chain[i+1] if i+1<len(chain) else (w,M(w,b0))
                assert on_curve(aa,bb,Q)
            return scale(Q)

        q=(A(1,d0), M(d0,A(1,d0)))
        assert on_curve(1,b0,q) and q[1]
        assert add_curve(1,b0,q,q)==(1,0)
        assert add_curve(1,b0,(1,0),(1,0)) is None
        q2=add_curve(1,b0,q,(0,0))
        assert q2==(S(1,d0),M(S(0,d0),S(1,d0)))
        assert end(q)==end(q2)==q
        assert end((0,0)) is None

    tr={}
    for n in range(1,depth+1):
        val=1<<n
        lim=isqrt(4*val)
        tr[n]={c(t) for t in range(-lim,lim+1) if (t-1-val) % 4 == 0}

    for start in sorted(pool):
        def walk(seq,w):
            nonlocal j3,t5,torsion
            n=len(seq)
            tail=seq[-1]
            if start in adj[tail]:
                tallies[n]+=1
                tau=A(M(c(1<<n),w),f.invtab[w])
                assert tau in tr[n]
                js=tuple(jvals[v] for v in seq)
                if n==3:
                    if tau==c(5):
                        assert len(set(js))<3
                        t5+=1
                    if len(set(js))==3:
                        j3+=1
                        assert tau in {c(1),c(-3)}
                        if p==103 and set(js)=={c(34),c(61,36),c(61,67)}:
                            triangle103.add((js,f.coords(w),tau))
                if torsion<60:
                    handoff(seq,w)
                    torsion+=1
            if n<depth:
                for v in adj[tail]:
                    walk(seq+(v,),M(w,v))
        walk((start,),start)

    if p==7:
        # Hasse polynomial degree three; all its roots are already over F_7.
        hp=lambda z: sum(comb(3,k)**2*pow(z,k,p) for k in range(4)) % p
        roots=[z for z in range(p) if hp(z)==0]
        assert roots==[2,4,6] and all(
            D(M(c(256),P(A(S(P(z,2),z),1),3)),P(M(z,S(z,1)),2))==c(1728)
            for z in roots)
        assert (5*5-4*8) % p == 0 and t5>0
    if p==103:
        assert len(triangle103)==6  # ordered, rooted triangle in the source Figure 4
    return sum(tallies),j3,t5,torsion,len(triangle103)

cases=[(3,7),(5,7),(7,7),(11,7),(19,7),(31,7),(43,7),(103,3)]
results = [verify(p,d) for p,d in cases]
total,simple,t5,torsion,tri = map(sum,zip(*results))
assert simple and t5 and tri
print(f"finite fields PASS: {len(cases)} quadratic fields, {total} rooted recurrence cycles, "
      f"{simple} simple rooted triangles, {t5} trace-5 tripled/non-simple cases")
print(f"finite fields PASS: {torsion} actual 4-torsion monodromies, p=7 Hasse roots and repeated-root check, "
      f"{tri} rooted orientations of the printed p=103 triangle")
