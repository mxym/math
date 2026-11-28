#!/usr/bin/env python3
"""Exact verification of the color-preserving six-orbit dyadic cutoff."""
import json
from itertools import combinations, permutations, product
from pathlib import Path


def require(test, msg):
    if not test:
        raise AssertionError(msg)


def normal_form(rows,n):
    # A row Hermite basis using only unimodular pair moves.
    a = [list(x) for x in rows]
    k = 0
    for j in range(n):
        i = next((i for i in range(k,len(a)) if a[i][j]),None)
        if i is None:
            continue
        a[k],a[i] = a[i],a[k]
        for i in range(k+1,len(a)):
            while a[i][j]:
                q = a[k][j]//a[i][j]
                a[k],a[i] = a[i],[x-q*y for x,y in zip(a[k],a[i])]
        if a[k][j] < 0:
            a[k] = [-x for x in a[k]]
        for i in range(k):
            q = a[i][j]//a[k][j]
            a[i] = [x-q*y for x,y in zip(a[i],a[k])]
        k += 1
    require(not any(any(row) for row in a[k:]), 'Hermite zero remainder')
    return tuple(map(tuple,a[:k]))


def belongs(R,d):
    d = list(d)
    for row in R:
        j = next(i for i,x in enumerate(row) if x)
        q,rem = divmod(d[j],row[j])
        if rem:
            return False
        d = [x-q*y for x,y in zip(d,row)]
    return not any(d)



def quotient_census():
    matrices=[]
    for a in product(range(3),repeat=9):
        rows=[a[3*i:3*i+3] for i in range(3)]
        cols=list(zip(*rows))
        if any(sum(row)<3 or row.count(2)>1 for row in (*rows,*cols)):
            continue
        matrices.append(a)
        if sum(0 not in row for row in rows)>=2:
            continue
        ds=[sum(row) for row in rows]
        es=[sum(col) for col in cols]
        b=list(a)
        if max(ds)>3:
            ii=[i for i,d in enumerate(ds) if d>3]
            jj=[j for j,d in enumerate(es) if d>3]
            require(len(ii)==len(jj)==1 and b[3*ii[0]+jj[0]]>0,"excess matching deletion")
            b[3*ii[0]+jj[0]]-=1
        require(all(sum(b[3*i:3*i+3])==3 for i in range(3)) and
                all(sum(b[j::3])==3 for j in range(3)),"balanced cube skeleton")
        require(b.count(0) in (2,3) and b.count(0)==b.count(2),"two cubic templates")
        reps=((0,2,1,2,0,1,1,1,1),(0,2,1,1,0,2,2,1,0))
        require(any(tuple(b[3*i+j] for i in p for j in q) in reps
                    for p in permutations(range(3)) for q in permutations(range(3))),
                "cubic template relabeling")
    print("PASS bipartite quotient census",len(matrices))


def graph(kind):
    if kind=="glue":
        # vertices U,V,A,B,C,D; two half-theta long paths share UV
        edges=((0,1,0,0),(1,2,0,0),(0,3,0,0),(1,4,0,0),(0,5,0,0),
               (2,3,1,0),(2,3,2,0),(4,5,0,1),(4,5,0,2))
        arrows=[]
        for u,v,x,y in edges:
            i=len(arrows)
            arrows.extend(((u,v,x,y,i+1,1),(v,u,-x,-y,i,1)))
        return arrows,6,((1,0),(0,1))
    # long path is represented by one weighted edge, with its own distinct internal layers.
    arrows=[]
    for i,(x,y) in enumerate(((0,0),(1,0),(0,1))):
        j=2*i
        cost=int(kind) if i==2 else 1
        arrows.extend(((0,1,x,y,j+1,cost),(1,0,-x,-y,j,cost)))
    return arrows,2,((1,0),)


def exceptional(kind,R):
    if kind=="3":
        return belongs(R,(-2,1)) or belongs(R,(1,1))
    if kind=="5":
        return belongs(R,(0,2)) or belongs(R,(2,-2))
    return False


def certify(kind,raw):
    data={tuple(map(tuple,json.loads(k))):v for k,v in raw.items()}
    A,m,required=graph(kind)
    depth={}
    all_leaves=[]
    def visit(R):
        if any(belongs(R,v) for v in required):
            return 0
        if R in depth:
            return depth[R]
        require(R in data,("missing collision state",kind,R))
        W=data[R]
        if not W:
            require(exceptional(kind,R),"unproved exceptional condition")
            all_leaves.append(R)
            depth[R]=0
            return 0
        if kind!="glue":
            require(len(W)%2==0 and all(c in "012" for c in W),"theta word format")
            W=[2*int(c)+(i%2) for i,c in enumerate(W)]
        require(all(type(i) is int and 0<=i<len(A) for i in W),"valid arrows")
        S=[A[i] for i in W]
        require(sum(a[5] for a in S) in (4,8,16,32),"dyadic weighted length")
        require(all(a[1]==b[0] and a[4]!=k for a,b,k in zip(S,S[1:]+S[:1],W[1:]+W[:1])),
                "closed and cyclically nonbacktracking")
        seen=[[] for _ in range(m)]
        x=y=0
        for u,v,p,q,rev,w in S:
            seen[u].append((x,y))
            x+=p; y+=q
        require(belongs(R,(x,y)),"total voltage closes")
        di={(x-u,y-v) for P in seen for (x,y),(u,v) in combinations(P,2)}
        h=0
        for d in sorted(di):
            require(not belongs(R,d),"candidate simple over current lattice")
            M=normal_form((*R,d),2)
            require(M!=R,"strict collision child")
            if not any(belongs(M,v) for v in required):
                h=max(h,1+visit(M))
        depth[R]=h
        return h
    h=visit(())
    require(set(depth)==set(data),"no unreachable rows")
    return len(depth),len(all_leaves),h


def main():
    data=json.loads(Path(__file__).with_name("erdos_gyarfas_bipartite_six_certificate.json").read_text())
    check_data(data)


def check_data(data):
    quotient_census()
    info={k:certify(k,data[k]) for k in ("3","5","glue")}
    require(info=={"3":(38,2,3),"5":(25,6,3),"glue":(3,0,1)},"frozen certificate census")
    print("PASS",info)


if __name__=="__main__":
    main()
