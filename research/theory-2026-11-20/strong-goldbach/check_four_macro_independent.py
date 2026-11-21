#!/usr/bin/env python3
"""Independent support generation, affine feasibility and rational-rank replay."""
from fractions import Fraction as Q
from itertools import product, combinations
from math import gcd
import json
from pathlib import Path

def fail(m): raise RuntimeError(m)
def cols_rank(vv):
    if not vv: return 0
    rr=[list(map(Q,row)) for row in zip(*vv)]; k=0
    for i in range(len(vv)):
        cand=next((j for j in range(k,6) if rr[j][i]),None)
        if cand is None: continue
        rr[k],rr[cand]=rr[cand],rr[k]
        d=rr[k][i]; rr[k]=[x/d for x in rr[k]]
        for j in range(k+1,6):
            d=rr[j][i]; rr[j]=[a-d*b for a,b in zip(rr[j],rr[k])]
        k+=1
    return k
def gen(boundary):
    w=[0,0,2,2,2 if boundary else 3,4]
    options=[]
    for i in range(6):
        opts=[]
        for counts in product(range(3), repeat=4):
            weight=sum(a*b for a,b in zip(counts,w[2:]))
            if weight>4 or (i>=2 and counts[i-2]) or (i==0 and not weight) or (i==1 and weight!=4): continue
            opts.append(counts)
        options.append(opts)
    def rows(curr,used,upwards):
        i=len(curr)
        if i==6:
            if used==15: yield curr
            return
        for row in options[i]:
            hit=sum((1<<j) for j,v in enumerate(row) if v)
            up=sum((1<<j) for j,v in enumerate(row) if v and i<j+2)
            if up & upwards: continue
            if boundary and any(sum(min(a,b)*wt for a,b,wt in zip(row,r,w[2:]))>w[i] for r in curr): continue
            yield from rows(curr+(row,),used|hit,upwards|up)
    return rows((),0,0)

def unfold(chart,ret):
    outside=set(range(6))-set(ret)
    order=[]
    while outside:
        sub=[i for i in outside if not any(chart[i][j-2] for j in outside)]
        if not sub:return 'cycle'
        order.extend(sub)
        outside.difference_update(sub)
    known={}
    for i in order+list(ret):
        v=[int(i==j) for j in range(6)]
        for j in order:
            if not chart[i][j-2]:continue
            for h in range(6):v[h]+=chart[i][j-2]*known[j][h]
        known[i]=v
    if any(sum(known[i])==1 for i in ret):return 'bad'
    col=[sum(chart[j][ret[-1]-2]*known[i][j] for j in range(6))-int(i==ret[-1]) for i in ret]
    if min(col)<=0:return 'bad'
    gg=gcd(*col);aa=[x//gg for x in col]
    sign=[sum(known[i])%2 for i in ret]
    return aa, [known[i] for i in ret], sign

def mass_check(forms,boundary):
    val=None
    low,high=Q(1,2),Q(1)
    if boundary:val=Q(1,2)
    for a,v,sg in forms:
        if boundary and not(all(x==0 for x in sg) or all(i%2==j for i,j in zip(a,sg))):return False
        # Time (1-w) on each visit; coefficient of gamma comes only from visit to Z.
        c=[row[0]+row[1]+Q(row[2]+row[3],2)+row[4] for row in v]
        dg=[-row[4] for row in v]
        for j in (1,2):
            x,y=c[j]*a[0]-c[0]*a[j],dg[j]*a[0]-dg[0]*a[j]
            if not y and x:return False
            if y:
                t=-x/y
                if val is not None and val!=t:return False
                val=t
        # All slopes of the >=1 constraints nonpositive.
        if not dg[0]:
            if c[0]<a[0]:return False
        else:high=min(high,(c[0]-a[0])/-dg[0])
    if boundary:return val<=high
    if val is None:return high>low
    return low<val<1 and val<=high

all_ledger=[]
for bd in (False,True):
    counts=[0,0,0,0,0]
    for ch in gen(bd):
        counts[0]+=1
        forms=[unfold(ch,(0,1,V)) for V in (range(2,6) if bd else (2,3))]
        if not bd and 'cycle' in forms:
            counts[1]+=1;continue
        if 'bad' in forms:continue
        counts[2]+=1
        if not mass_check([f for f in forms if not isinstance(f,str)],bd):continue
        counts[3]+=1
        if not bd:fail('interior survivor')
        A=list(zip(*ch))
        B=[tuple(int(j+2==i)-a for i,a in enumerate(cc)) for j,cc in enumerate(A)]
        if cols_rank(B)!=4 or cols_rank(B+[(2,2,1,1,1,0)])!=4:continue
        counts[4]+=1
        def unit(i):return tuple(int(k==i) for k in range(6))
        ds=[2-sum((1,1,1,2)[j]*v for j,v in enumerate(r)) for r in ch]
        dirty=[i for i,d in enumerate(ds) if d]
        if any(d not in (0,1) for d in ds) or (dirty and (dirty[0]!=0 or len(dirty)>2)):fail('dirty chart')
        if len(dirty)==2 and cols_rank(B+[unit(dirty[1])])!=5:fail('second dirty row')
        ext=A+[ds]
        if cols_rank(ext+[unit(5)])==cols_rank(ext):fail('even-v-odd condition not established')
        name=lambda r:''.join(c*v for c,v in zip('XYZH',r)) or '-'
        all_ledger.append({'rows':list(map(name,ch)),'dirty':dirty,'rank_aug':cols_rank(ext)})
    print(bd,counts)
exp=json.loads(Path(__file__).with_name('four_macro_boundary_ledger.json').read_text())
if sorted(all_ledger,key=lambda z:z['rows'])!=exp:fail('ledger disagreement')
print('independent generator, affine interval and Gaussian rank check all match exact frozen ledger')
