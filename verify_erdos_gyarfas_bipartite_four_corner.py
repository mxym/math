#!/usr/bin/env python3
"""Recheck the four-vertex bipartite corner case with one existing voltage tree."""
import json
from itertools import combinations

from verify_erdos_gyarfas_six_layer_extremal_independent import hnf, contains, need

# Prior four-orbit certificate, template 0000012210. Each key is a row-Hermite
# lattice; each word lists global oriented dart indices.
DATA=json.loads(r'''{"[]":[0,7,8,1,2,5,2,5,0,9,6,1,4,3,4,3],"[[1,-1,0]]":[0,7,8,1,2,11,6,1,2,5,0,9,10,3,4,3],"[[1,0,-1],[0,1,-1]]":[0,7,10,5],"[[1,-1,0],[0,0,1]]":[0,7,10,3],"[[1,0,1],[0,1,1]]":[0,7,8,7,8,7,10,5],"[[1,0,1],[0,1,1],[0,0,2]]":[0,7,10,5],"[[1,1,0],[0,2,0]]":[2,5,2,5],"[[1,1,-1],[0,2,-1]]":[0,9,10,5],"[[2,-1,0]]":[0,7,8,1,2,5,2,5],"[[2,0,0]]":[2,5,2,5],"[[2,1,0]]":[0,7,8,1,4,3,4,3],"[[1,1,0]]":[0,7,8,1,2,5,2,11,6,1,4,3,0,9,10,3],"[[1,1,0],[0,2,-1]]":[0,9,6,9,6,9,10,5],"[[1,1,0],[0,2,0],[0,0,1]]":[0,7,10,3],"[[1,0,1],[0,1,-1]]":[0,9,10,3],"[[1,1,0],[0,0,1]]":[0,7,10,3],"[[1,0,-1],[0,1,1]]":[0,7,10,5]}''')
DARTS=[]
for a,b,k in ((0,2,-1),(0,3,-1),(0,3,0),(1,2,-1),(1,2,1),(1,3,2)):
    i=len(DARTS)
    DARTS.extend(((a,b,k,1,i+1),(b,a,k,-1,i)))
CELLS={tuple(map(tuple,json.loads(s))):path for s,path in DATA.items()}
NONZERO=((1,0,0),(0,1,0))


def replay():
    visited={}
    def visit(R):
        if any(contains(R,v) for v in NONZERO):
            return -1
        if R in visited:
            return visited[R]
        need(R in CELLS,"missing unresolved relation lattice")
        word=CELLS[R]
        need(len(word) in (4,8,16) and all(0<=d<12 for d in word),"bad word")
        seq=[DARTS[d] for d in word]
        need(all(a[1]==b[0] and a[4]!=j
                 for a,b,j in zip(seq,seq[1:]+seq[:1],word[1:]+word[:1])),
             "not a cyclic nonbacktracking walk")
        prefixes=[]; voltage=[0]*3
        for u,v,k,sign,j in seq:
            prefixes.append((u,tuple(voltage)))
            if k!=-1:
                voltage[k]+=sign
        need(contains(R,tuple(voltage)),"no forced closure")
        depth=0
        for (u,a),(v,b) in combinations(prefixes,2):
            if u!=v:continue
            d=tuple(y-x for x,y in zip(a,b))
            need(not contains(R,d),"collision already in lattice")
            depth=max(depth,1+visit(hnf(R+(d,),3)))
        visited[R]=depth
        return depth
    d=visit(())
    need(set(visited)==set(CELLS) and len(CELLS)==17,"corner proof census")
    print("PASS: four-fiber bipartite corner,",len(visited),"states, depth",d)


if __name__=="__main__":
    replay()
