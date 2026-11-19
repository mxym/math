#!/usr/bin/env python3
"""Replay the table and count cycles in literal simple graphs. Python 3, stdlib."""
from itertools import combinations
from math import isqrt

def require(test, msg):
    if not test:
        raise ArithmeticError(msg)

# Row order is r=20,21,...,41 in the proof, not optimized.
ROWS=list(zip(
    [2,7,0,3,8,1,4,9,0,5,10,1,6,11,2,7,0,3,8,1,4,9],
    [1,0,0,1,0,0,1,0,2,1,0,2,1,0,2,1,1,2,1,1,2,1],
    [0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,0]))

class Graph:
    def __init__(self):
        self.adj=[]
    def new(self):
        self.adj.append(set())
        return len(self.adj)-1
    def edge(self,a,b):
        require(a!=b and b not in self.adj[a] and a not in self.adj[b],"not simple")
        self.adj[a].add(b); self.adj[b].add(a)
    def coin(self,c):
        v=[self.new() for _ in range(4 if c==0 else 6)]
        edges=(list(combinations(range(4),2)) if c==0 else
               [(0,1),(1,2),(0,2),(3,4),(4,5),(3,5),(0,3),(1,4),(2,5)])
        st=(0,1) if c!=2 else (0,3)
        edges.remove(st)
        for i,j in edges: self.edge(v[i],v[j])
        return v[st[0]],v[st[1]]
    def join(self,ab,cd=None):
        a,b=ab
        x,y=self.new(),self.new()
        self.edge(x,a); self.edge(y,b)
        if cd is None: self.edge(x,y)
        else:
            c,d=cd
            self.edge(x,c); self.edge(y,d)
        return x,y
    def spanning(self,omit):
        live=set(range(len(self.adj)))-{omit}
        todo=[min(live)]
        live.remove(todo[0])
        while todo:
            for w in self.adj[todo.pop()].intersection(live): live.remove(w); todo.append(w)
        return not live
    def count_paths(self,s,t,taken):
        # Enumerate exactly the paths that can still reach t. Feasibility
        # pruning prevents exponential exploration of dead partial paths.
        if s==t: return 1
        if t in taken: return 0
        todo=[t]; seen=taken|{s,t}
        while todo:
            for w in self.adj[todo.pop()]-seen:
                seen.add(w); todo.append(w)
        total=0
        for v in self.adj[s]-taken:
            if v in seen:
                total+=self.count_paths(v,t,taken|{s})
        return total
    def count_cycles(self):
        # Distinguished least vertex and its UNORDERED pair of cycle neighbors.
        total=0
        for s,nb in enumerate(self.adj):
            used=set(range(s+1))
            for i,j in combinations(sorted(nb-used),2):
                total+=self.count_paths(i,j,used)
        return total

def params(k):
    require(k>=2679,"outside theorem")
    J=lambda p:p*(p+7)//2
    p=(isqrt(8*(k+17)+49)-7)//2
    if J(p)<k+17:p+=1
    e=J(p)+3-k
    r=20+(e-20)%22
    a,b,c=ROWS[r-20]; c+=(e-r)//22
    cost=4*a+7*b+8*c
    require(3*a+14*b+22*c==e and 0<cost<=p and p>=71,"cost")
    require(20<=e<=p+22 and J(p-1)+3-k<20,"choice of p")
    return (a,b,c),p-cost,p,e

def construct(k):
    (a,b,c),wraps,p,e=params(k)
    G=Graph()
    pieces=[G.coin(typ) for typ,count in enumerate((a,b,c)) for _ in range(count)]
    while len(pieces)>1:
        L=pieces.pop(); R=pieces.pop(); pieces.append(G.join(L,R))
    H=pieces[0]
    for _ in range(wraps): H=G.join(H)
    s,t=G.coin(0)
    G.edge(H[0],s); G.edge(H[1],t)
    return G

def main():
    for r,(a,b,c) in enumerate(ROWS,20):
        require(3*a+14*b+22*c==r and 4*a+7*b+8*c<=44,"row")
    print("22 literal deficit rows (20..41) verified; maximum path cost 44.")
    for k in range(2679,100001): params(k)
    for k in [10**20,10**100]: params(k)
    print("97,322 consecutive parameter checks (2679..100000); 10^20 and 10^100 also pass.")
    for typ,(p,c) in enumerate([(4,3),(7,7),(8,6)]):
        G=Graph(); s,t=G.coin(typ)
        require(G.count_paths(s,t,set())==p and G.count_cycles()==c,"seed")
    print("Direct seed counts (paths,cycles): (4,3), (7,7), (8,6).")
    for k in [2679,2680,3000,4001]:
        G=construct(k); n=len(G.adj)
        require(all(len(ns)==3 for ns in G.adj),"not cubic")
        require(all(G.spanning(v) for v in range(n)),"cut vertex")
        cycles=G.count_cycles()
        require(cycles==k,"wrong number of cycles: "+str((k,cycles)))
        print(f"Witness: k={k}, vertices={n}, edges={3*n//2}, cycles={cycles}; vertex deletions connected.")
    print("PASS")
if __name__=="__main__": main()
