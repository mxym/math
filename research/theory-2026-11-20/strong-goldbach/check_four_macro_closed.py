#!/usr/bin/env python3
"""Exact row/column coverage, first-return and terminal-rank certificates. Standard library."""
from collections import Counter
from fractions import Fraction as F
from functools import reduce
from hashlib import sha256
from itertools import combinations_with_replacement, product
import json
from math import gcd
from pathlib import Path
import sys

ROWS=range(6); MAC=(2,3,4,5)
def require(test,msg):
    if not test: raise RuntimeError(msg)
def rank(cols):
    """Column basis over Q via fraction-free elimination on integral column vectors."""
    basis={}
    for col in cols:
        x=list(col)
        for p,y in sorted(basis.items()):
            if x[p]:
                a,b=y[p],x[p]
                x=[a*t-b*u for t,u in zip(x,y)]
                g=reduce(gcd,x,0)
                if g:x=[t//g for t in x]
        if any(x):
            p=next(i for i,t in enumerate(x) if t)
            basis[p]=x
    return len(basis)
def key(row):
    return tuple(''.join('XYZH'[j-2] for j in seq) or '-' for seq in row)
def baseok(r,bd):
    if not r[0] or not r[1]:return False
    if any(i in r[i] for i in ROWS):return False
    if any(not any(t in seq for seq in r) for t in MAC):return False
    if any(sum(j in r[i] for i in range(j))>1 for j in MAC):return False
    # q input: p-column negligible, own q absent, so total macro weight exactly 1.
    weight=(0,0,2,2,2 if bd else 3,4) # times four, interior representative gamma=3/4
    if sum(weight[j] for j in r[1])!=4:return False
    if bd:
        # common macro prime powers divide input difference
        for i in ROWS:
            for j in range(i):
                if sum(min(r[i].count(t),r[j].count(t))*weight[t] for t in MAC)>max(weight[i],weight[j]):return False
    return True
def row_generate(bd):
    half=(2,3,4) if bd else (2,3)
    pool=[()]+[(t,) for t in MAC]+list(combinations_with_replacement(half,2))
    opts=[[s for s in pool if i not in s and (i>1 or s) and (i!=1 or s==(5,) or len(s)==2)] for i in ROWS]
    return {r for r in product(*opts) if baseok(r,bd)}
def col_generate(bd):
    """Different construction, append one whole macro column at a time, using exact per-row capacities."""
    w={2:2,3:2,4:2 if bd else 3,5:4}
    r=[[] for _ in ROWS];cap=[4]*6;res=set()
    def rec(j):
        if j==6:
            z=tuple(tuple(t) for t in r)
            # Presence, loops, upward uniqueness and capacity were built into column recursion.
            if not z[0] or cap[1]!=0:return
            if bd:
                for i in ROWS:
                    for h in range(i):
                        m=sorted(set(z[i])&set(z[h]))
                        if sum(w[t]*min(z[i].count(t),z[h].count(t)) for t in m)>max(w.get(i,0),w.get(h,0)):return
            res.add(z);return
        # Choose the sole smaller predecessor or none. Each larger predecessor makes an independent choice.
        higher=list(range(j+1,6))
        for below in range(-1,j):
            active=([below] if below>=0 else [])+higher
            rng=[range(1 if i==below else 0,cap[i]//w[j]+1) for i in active]
            for ns in product(*rng):
                if not any(ns):continue
                for i,n in zip(active,ns):r[i].extend([j]*n);cap[i]-=w[j]*n
                rec(j+1)
                for i,n in zip(active,ns):
                    if n:del r[i][-n:]
                    cap[i]+=w[j]*n
    rec(2);return res
def bplus(x,y):return (x[0]+y[0],x[1]+y[1])
def bval(x,g):return x[0]+x[1]*g
def return_forms(r,V,bd):
    """None: cyclic/unused test; False: ruled out; else integer linear mass forms, primitive rank-one column."""
    R=(0,1,V);O=set(ROWS)-set(R)
    dag={}; color=set()
    def path(i):
        if i in color: raise ValueError
        if i in dag:return dag[i]
        color.add(i)
        n=r[i].count(V);sig=1;visits=[0]*6;visits[i]=1
        for j in r[i]:
            if j in O:
                nn,ss,xx=path(j);n+=nn;sig+=ss
                visits=[a+b for a,b in zip(visits,xx)]
        color.remove(i);dag[i]=(n,sig,visits);return dag[i]
    try:
        for j in O:path(j)
        dat=[path(i) for i in R]
    except ValueError:
        if not bd:raise RuntimeError('gamma interior exterior cycle: must use affine lemma to reject chart')
        return None
    if any(not any(j in O for j in r[i]) for i in R):return False
    v=[n-int(i==V) for i,(n,_,_) in zip(R,dat)]
    if min(v)<=0:return False
    g=reduce(gcd,v);a=tuple(x//g for x in v)
    # W^a are signs mod N at all retained rows; Bezout gives W itself a sign.
    if bd and not any(all((ai*t-sg)%2==0 for ai,(_,sg,_) in zip(a,dat)) for t in (0,1)):return False
    # Doubled masses 2 sum visits*(1-w_i) as affine functions of gamma.
    d=[(2,0),(2,0),(1,0),(1,0),(1,0) if bd else (2,-2),(0,0)]
    mass=[(sum(vis[i]*d[i][0] for i in ROWS),sum(vis[i]*d[i][1] for i in ROWS)) for _,_,vis in dat]
    return a,mass
def acyclic(r,V):
    left=set(ROWS)-{0,1,V}
    while left:
        dead={i for i in left if not(set(r[i])&left)}
        if not dead:return False
        left-=dead
    return True
def compatible(forms,bd):
    eq=[];ineq=[]
    for a,m in forms:
        for j in [1,2]:eq.append(tuple(m[j][t]*a[0]-m[0][t]*a[j] for t in range(2)))
        ineq.append((m[0][0]-2*a[0],m[0][1]))
    if bd:return all(x==0 for x,y in eq) and all(x>=0 for x,y in ineq)
    # Affine signs are constant within intervals; include isolated admissible roots.
    roots={F(1,2),F(1)}
    for x,y in eq+ineq:
        if y and F(1,2)<F(-x,y)<1:roots.add(F(-x,y))
    g=sorted(roots)
    test=set(g)|{(l+h)/2 for l,h in zip(g,g[1:])}
    return any(F(1,2)<t<1 and all(bval(z,t)==0 for z in eq) and all(bval(z,t)>=0 for z in ineq) for t in test)
def run(bd):
    one=row_generate(bd);two=col_generate(bd);require(one==two,'independent candidate sets disagree')
    cnt=Counter(base=len(one));led=[]
    for r in sorted(one):
        if not bd and any(not acyclic(r,V) for V in (2,3)):
            cnt['cycle_reject']+=1;continue
        forms=[return_forms(r,V,bd) for V in (MAC if bd else (2,3))]
        if any(f is False for f in forms):continue
        cnt['return_structure']+=1
        if not compatible([f for f in forms if f is not None],bd):continue
        cnt['return_mass']+=1
        if not bd:raise RuntimeError('interior chart survives')
        A=[tuple(r[i].count(j) for i in ROWS) for j in MAC]
        B=[tuple(int(i==j)-r[i].count(j) for i in ROWS) for j in MAC]
        if rank(B)!=4 or rank(B+[(2,2,1,1,1,0)])!=4:continue
        cnt['rank_mass']+=1
        deficit=tuple(2-sum(2 if j==5 else 1 for j in r[i]) for i in ROWS)
        require(all(d in (0,1) for d in deficit),'unhandled cofactor magnitude')
        dirty=[i for i,d in enumerate(deficit) if d]
        require(not dirty or (dirty[0]==0 and len(dirty)<=2),'unhandled dirty rows')
        col=lambda i:tuple(int(j==i) for j in ROWS)
        if len(dirty)==2:require(rank(B+[col(dirty[1])])==5,'moving p-column unhandled')
        # An integral c kills these columns and has c_H nonzero iff e_H is NOT in their rational span.
        ext=A+[deficit]
        require(rank(ext+[col(5)])>rank(ext),'odd rational gap not obtained')
        cnt['parity_'+str(len(dirty))]+=1
        led.append({'rows':key(r),'dirty':dirty,'rank_aug':rank(ext)})
    return dict(cnt),sorted(led,key=lambda z:z['rows'])
def main():
    g,_=run(False);h,led=run(True)
    print('gamma interior',g);print('half boundary',h)
    raw=json.dumps(led,indent=2,sort_keys=True)+'\n'
    path=Path(__file__).with_name('four_macro_boundary_ledger.json')
    if sys.argv[1:]==['--write-ledger']:path.write_text(raw)
    else:require(path.read_text()==raw,'frozen ledger mismatch')
    require(h['base']==12500 and h['return_mass']==230 and h['rank_mass']==33 and (h['parity_0'],h['parity_1'],h['parity_2'])==(22,1,10),'historical count mismatch')
    print('PASS: no charts; terminal ledger sha256',sha256(raw.encode()).hexdigest())
if __name__=='__main__':main()
