from pathlib import Path
from itertools import product
from tempfile import TemporaryDirectory
from subprocess import run
import os
from field import gm as M,iv,testconics,check
from models import models
root=Path(__file__).resolve().parent
def norm(P):
    k=next(x for x in P if x)
    return tuple(M[z][iv[k]]for z in P)
def smooth_independent(meta):
    a,c,d,b,f=meta['coeff'];T=meta['T']
    if T is None:
        return [(x,y,1)for x,y in product(range(64),repeat=2)if (M[y][y]^M[M[a][x]^c][y]^M[M[x][x]][x]^M[d][M[x][x]]^M[b][x]^f)==0]+[(0,1,0)]
    u,v=T;w=v^M[a][u]^c
    # implicit cubic: (X+uH)Y^2+(aX+cH)YH+X^2H+(d+u)XH^2+(b+aw+ud+u^2)H^3
    A=b^M[a][w]^M[u][d]^M[u][u]
    return [(x,y,1)for x,y in product(range(64),repeat=2)if (M[x^u][M[y][y]]^M[M[a][x]^c][y]^M[x][x]^M[d^u][x]^A)==0]+[(0,1,0),(1,0,0)]
rg=range(64)
def nodes():
    dirs=[(1,t)for t in rg]+[(0,1)]
    allp=[(x,y,1)for x,y in product(rg,repeat=2)]+[(x,y,0)for x,y in dirs]
    models=[];raw=[]
    for a,b in dirs:
        p=[(0,0,1)]
        for x,y in dirs:
            q=M[x][x]^M[x][y]^M[32][M[y][y]]
            check(q!=0,"nonsplit tangent cone")
            c=M[M[y][y]][M[a][x]^M[b][y]]
            p.append((x,y,M[c][iv[q]]))
        r=[(x,y,z)for x,y,z in allp if M[z][M[x][x]^M[x][y]^M[32][M[y][y]]]==M[M[y][y]][M[a][x]^M[b][y]]]
        check(len(p)==len(r)==66 and {norm(t)for t in p}=={norm(t)for t in r},"node implicit equation")
        models.append(p);raw.append(r)
    return models,raw
def serial(curves):
    return ''.join(' '.join(map(str,[len(C)]+[z for t in C for z in t]))+'\n' for C in curves)
testconics()
cs,meta=models();rs=[smooth_independent(m)for m in meta]
for c,r in zip(cs,rs):
    check(len(c)==len(r) and {norm(t)for t in c}=={norm(t)for t in r},"explicit RR embedding vs independent implicit equation")
check(len(cs)==40 and sum(m['T'] is not None for m in meta)==24,"smooth family")
ns,rn=nodes();print("smooth, isolated-node representative counts",len(cs),len(ns),flush=True)
with TemporaryDirectory() as d:
    for typ in ('pairs','quads'):
        exe=str(Path(d)/typ);run([os.environ.get('CXX','g++'),'-O3','-march=native','-std=c++17',str(root/(typ+'.cpp')),'-o',exe],check=True)
        output=run([exe]+(['66']if typ=='pairs' else []),input=serial(cs+ns if typ=='pairs' else rs+rn),text=True,capture_output=True,check=True).stdout.splitlines()
        check(len(output)==105,"one row per model / no survivors")
        stats=[]
        for i,line in enumerate(output):
            t=line.split()
            if typ=='pairs':
                check(len(t)==12 and t[0]=='MODEL' and int(t[1])==i and int(t[5])==4161 and int(t[9])==0 and int(t[11])<0 and int(t[11])%3==0,"pair certificate")
                stats.append([int(t[7]),-int(t[11])//3])
            else:
                check(len(t)==3 and int(t[0])==i and int(t[2])>0,"quad certificate")
                stats.append(list(map(int,t[1:])))
        print(typ,"smooth:",sum(q[0]for q in stats[:40]),min(q[1]for q in stats[:40]),"nodal:",sum(q[0]for q in stats[40:]),min(q[1]for q in stats[40:]),flush=True)
        if typ=='pairs':reference=stats
        else:check(stats==reference,"exact per-model maximum margins and eligible counts agree")
check([sum(q[0]for q in stats[:40]),min(q[1]for q in stats[:40]),sum(q[0]for q in stats[40:]),min(q[1]for q in stats[40:])]==[148673,18,87360,150],"totals")
print("PASS: smooth cubics and isolated-node cubics never contain a 66-point Sidon set; conic+nucleus attains the cubic maximum.",flush=True)
