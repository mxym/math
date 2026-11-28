#!/usr/bin/env python3
"""Exact same-window comparison of separate and disjoint lattice-ray tests."""
from collections import deque
from sys import argv
D=((1,0),(0,1),(-1,0),(0,-1))

def status(S):
    # 0 neither two individual escapes, 1 only individual, 2 joint
    a,b=S[0],S[-1]
    bx=min(x for x,y in S)-1; ex=max(x for x,y in S)+1
    by=min(y for x,y in S)-1; ey=max(y for x,y in S)+1
    def edge(u):
        x,y=u
        return x in (bx,ex) or y in (by,ey)
    def exposed(u):
        x,y=u
        return x in (bx+1,ex-1) or y in (by+1,ey-1)
    aa,bb=exposed(a),exposed(b)
    if aa and bb:return 2
    F=set(S)
    def escape(origin, w=None, path=False):
        Q=deque([origin]);P={origin:None}
        while Q:
            u=Q.popleft()
            if edge(u):
                if not path:return True
                p=[]
                while u is not None: p.append(u);u=P[u]
                return p[:-1]
            x,y=u
            for j,k in D:
                v=(x+j,y+k)
                if v!=w and v not in F and v not in P:
                    Q.append(v);P[v]=u
        return False
    if aa:return 2 if escape(b) else 0
    if bb:return 2 if escape(a) else 0
    p=escape(a,path=True)
    if not p or not escape(b):return 0
    return 1 if any(not escape(a,w) and not escape(b,w) for w in p) else 2

def graphs(m):
    stay={};blocks=[];count=[0,0,0];witness=[]
    P=[(0,0),(1,0)];used=set(P);steps=[0]
    def visit(k,code):
        if k==m-1:
            stay[code]=len(stay)
        elif k==m:
            st=status(P);count[st]+=1
            if st==1:witness.append(tuple(P))
            if st:
                tail=0;d=steps[1]
                for j in steps[2:]: tail=4*tail+((j-d)%4)
                blocks.append((code//4,tail,st))
            return
        x,y=P[-1]
        for i,(h,j) in enumerate(D):
            t=(x+h,y+j)
            if t not in used:
                used.add(t);P.append(t);steps.append(i)
                visit(k+1,4*code+i)
                used.remove(t);P.pop();steps.pop()
    visit(1,0)
    A=[[]for k in stay];B=[[]for k in stay]
    for c,d,st in blocks:
        A[stay[c]].append(stay[d])
        if st==2:B[stay[c]].append(stay[d])
    return A,B,count,witness

def component(A):
    def reach(G):
        Q=deque([0]); seen={0}
        while Q:
            for v in G[Q.popleft()]:
                if v not in seen: Q.append(v);seen.add(v)
        return seen
    inv=[[]for a in A]
    for k,row in enumerate(A):
        for l in row: inv[l].append(k)
    return reach(A)&reach(inv)


S=10**20; DISP=10**9
def interval(G, itr=72):
    V=[S]*len(G)
    for k in range(itr):
        Z=[sum(V[j] for j in row) for row in G]
        vmax=max(Z)
        V=[100 + z*S//vmax for z in Z]
    Z=[sum(V[j] for j in row) for row in G]
    C=component(G)
    L=min(sum(V[j] for j in G[i] if j in C)*DISP//V[i] for i in C)
    U=max((DISP*z+v-1)//v for v,z in zip(V,Z))
    return (len(C),L,U)


def main():
    if not __debug__:
        raise RuntimeError("run without -O")
    if len(argv) != 1:
        raise SystemExit("usage: python3 verify_factor_saw_disjoint_arms.py")
    # A one-edge segment has two opposite exterior rays.
    assert all(graphs(m)[2][1] == 0 for m in range(2, 10))
    expected = {
        10: (4067, [120, 4, 10901], (4015, 2724751333, 2724751334),
             (4015, 2724612788, 2724612789)),
        12: (30073, [1280, 46, 79907], (29551, 2711148714, 2711148715),
             (29551, 2710913857, 2710913858)),
    }
    for m in sorted(expected):
        A, B, count, w = graphs(m)
        a, b = interval(A), interval(B)
        assert (len(A), count, a, b) == expected[m]
        assert a[1] > b[2]
        if m == 10:
            assert all(sum(map(abs, h[-1])) == 2 for h in w)
            assert len({min(h, tuple((x, -y) for x, y in h)) for h in w}) == 2
        print(m, len(A), count, a, b, flush=True)
    print("PASS exact disjoint-arm comparison")

if __name__ == "__main__":
    main()
