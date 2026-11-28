#!/usr/bin/env python3
"""Independent row-Hermite proof replay for the three frozen voltage trees."""
from collections import Counter
from copy import deepcopy
from itertools import combinations, permutations, product
from pathlib import Path
import json
import sys


def need(ok, info):
    if not ok:
        raise AssertionError(info)


def hnf(rows, r):
    rows=[list(v) for v in rows if any(v)]
    k=0
    for j in range(r):
        candidate=next((i for i in range(k,len(rows)) if rows[i][j]),None)
        if candidate is None:
            continue
        rows[k],rows[candidate]=rows[candidate],rows[k]
        for i in range(k+1,len(rows)):
            while rows[i][j]:
                q=rows[k][j]//rows[i][j]
                new=[a-q*b for a,b in zip(rows[k],rows[i])]
                rows[k],rows[i]=rows[i],new
        if rows[k][j]<0:
            rows[k]=[-a for a in rows[k]]
        for i in range(k):
            q=rows[i][j]//rows[k][j]
            rows[i]=[a-q*b for a,b in zip(rows[i],rows[k])]
        k+=1
    need(all(not any(v) for v in rows[k:]),"nonzero row outside HNF")
    return tuple(tuple(v) for v in rows[:k])


def contains(R,v):
    for row in R:
        j=next(i for i,a in enumerate(row) if a)
        q,rem=divmod(v[j],row[j])
        if rem: return False
        v=tuple(a-q*b for a,b in zip(v,row))
    return not any(v)


def verify_tree(record):
    matrix, edges, r = record["matrix"],record["edges"],record["rank"]
    need([len(row) for row in matrix]==[3,3,3],"matrix size")
    need(len(edges)==6 and sum(map(sum,matrix))-5==r,"rank")
    zeros=[set() for _ in edges]; check=[[0]*3 for _ in range(3)]
    used=Counter()
    for u,row in enumerate(edges):
        for e,entry in enumerate(row):
            a,v,k,s,j=map(int,entry)
            need(u==a and 0<=v<6 and (u<3)!=(v<3),"dart ends")
            need(-1<=k<r and s==(1 if u<3 else -1),"voltage label")
            need(0<=j<len(edges[v]) and edges[v][j]==[v,u,k,-s,e],"inverse dart")
            if k==-1: zeros[u].add(v)
            if u<3:
                check[u][v-3]+=1
                used[k]+=1
    need(check==matrix and used==Counter({-1:5,**{j:1 for j in range(r)}}),
         "quotient matching count")
    reached={0}
    for _ in range(6):
        reached|=set().union(*(zeros[v] for v in reached))
    need(len(reached)==6,"zero edge tree disconnected")

    data=set()
    occurrences=Counter()
    def visit(node):
        R=hnf(node["R"],r)
        need(all(len(row)==r and all(isinstance(x,int) for x in row)
                 for row in node["R"]),"nonintegral relations")
        data.add(R)
        length,steps,u=node["len"],node["steps"],node["start"]
        need(length in (2,4,8,16) and length==len(steps) and 0<=u<6,"witness shape")
        prefix=[]; vec=[0]*r; forbidden_dart=-1
        for dart in steps:
            need(0<=dart<len(edges[u]) and dart!=forbidden_dart,"backtracking")
            prefix.append((u,tuple(vec)))
            _,v,k,s,j=edges[u][dart]
            if k!=-1: vec[k]+=s
            u=v; forbidden_dart=j
        need(u==node["start"] and forbidden_dart!=steps[0],"noncyclic projection")
        need(contains(R,tuple(vec)),("endpoint voltage not forced",R,vec))
        implied=set()
        for (a,v),(b,w) in combinations(prefix,2):
            if a!=b: continue
            difference=tuple(y-x for x,y in zip(v,w))
            need(not contains(R,difference),("prior collision",R,difference))
            implied.add(hnf(R+(difference,),r))
        represented=[hnf(k["R"],r) for k in node["kids"]]
        need(len(set(represented))==len(represented) and
             set(represented)==implied,("wrong forced-collision successors",R,
                                        implied,represented))
        occurrences[length]+=1
        for k in node["kids"]:
            visit(k)           # replay every occurrence, not just distinct bases
    need(record["tree"]["R"]==[],"not the free root")
    visit(record["tree"])
    return len(data),sum(occurrences.values()),dict(sorted(occurrences.items()))


def small_quotients():
    perms=list(permutations(range(3)))
    covered=set()
    count=0
    for M in product(range(3),repeat=9):
        row=[M[i:i+3] for i in (0,3,6)]
        col=[M[i::3] for i in range(3)]
        if any(sum(q)<3 or q.count(2)>1 for q in row+col): continue
        count+=1
        # Deterministically remove a matching at any pair of excess indices.
        a=[list(q) for q in row]
        while True:
            i=next((i for i in range(3) if sum(a[i])>3),None)
            if i is None: break
            j=next(j for j in range(3) if sum(q[j] for q in a)>3)
            need(a[i][j]>0,"no permissible decrement")
            a[i][j]-=1
        need(all(sum(q)==3 for q in a)
             and all(sum(q[j] for q in a)==3 for j in range(3)),"noncubic endpoint")
        covered.add(min(tuple(a[i][j] for i in pi for j in pj) for pi in perms for pj in perms))
    expect={(1,)*9,(0,1,2,1,1,1,2,1,0),(0,1,2,1,2,0,2,0,1)}
    need(covered==expect,("cubic quotient types",covered))
    print("quotient classification: input matrices",count,"cubic types",len(covered))


def read_records(filename):
    text=Path(filename).read_text(encoding="utf-8")
    return json.loads(text.split("const certificates = ",1)[1].split(";\nconst report = ",1)[0])


def main(records):
    expected=[(6,7,{2:3,4:1,8:2,16:1}),
              (31,57,{2:31,4:5,8:14,16:7}),
              (6,7,{2:3,4:1,8:2,16:1})]
    got=[verify_tree(r) for r in records]
    print("Independent HNF checks:",got)
    need(got==expected,"voltage tree census")
    for rec in records:
        for j in range(len(rec["tree"]["kids"])):
            omitted=deepcopy(rec)
            omitted["tree"]["kids"].pop(j)
            try:
                verify_tree(omitted)
            except AssertionError as e:
                need("wrong forced-collision successors" in str(e),"unrelated mutation failure")
            else:
                raise AssertionError("omitted collision branch accepted")
    small_quotients()
    print("PASS: all proof-tree occurrences and root-branch mutations")


if __name__=="__main__":
    name=sys.argv[1] if len(sys.argv)>1 else Path(__file__).with_name(
        "verify_erdos_gyarfas_six_layer_extremal.mjs")
    main(read_records(name))
