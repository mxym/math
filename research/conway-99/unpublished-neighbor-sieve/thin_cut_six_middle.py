from itertools import product,combinations
from two_fano_core import labeled,sides
from collections import Counter
N=labeled(15)
V=set(range(24))
def pair(x,y):return tuple(sorted((x,y)))
def choices(f,g):
    F=sides[f]|sides[f^1];G=sides[g]|sides[g^1]
    for ap,an,bfp,bfn,bgp,bgn,cp,cn in product(sides[f]-G,sides[f^1]-G,sides[f],sides[f^1],sides[g],sides[g^1],sides[g]-F,sides[g^1]-F):
        if (an in N[ap] or bfn in N[bfp] or bfp not in N[an] or bfn not in N[ap]):continue
        if (cn in N[cp] or bgn in N[bgp] or bgp not in N[cn] or bgn not in N[cp]):continue
        A={ap,an};B={bfp,bfn,bgp,bgn};C={cp,cn}
        if len(B&G&sides[g])!=1 or len(B&G&sides[g^1])!=1 or len(B&F&sides[f])!=1 or len(B&F&sides[f^1])!=1:continue
        if A&B or B&C:continue
        blocks=[A,B,C];a=A|B|C
        if any(len(N[i]&B1)>2-(i in B1) for B1 in blocks for i in V):continue
        if any(len(N[i]&N[j])+sum(i in t and j in t for t in blocks)>2-(j in N[i]) for i,j in combinations(V,2)):continue
        if any(len(N[i]&t)>1 for t in blocks for i in a):continue
        Fp={ap,bfp};Fn={an,bfn};Gp={cp,bgp};Gn={cn,bgn}
        if Fp&(Gp|Gn) or Gp&Fn:continue
        regions=[Fn|Gn,Fp,Gp]; allowed={pair(ap,bfn),pair(an,bfp),pair(cp,bgn),pair(cn,bgp)}
        if any(j in N[i] and pair(i,j) not in allowed for r,s in combinations(regions,2) for i in r for j in s):continue
        yield blocks,regions
def cwords():
    res=[]
    for n in (2,3,4):
     for ss in combinations(V,n):
        s=set(ss);h=[len(s&a) for a in sides]
        if h not in ([1,1,1,1],[0,0,1,1],[1,1,0,0]):continue # Z_f and Z_g disjoint
        if any(len(N[i]&s)>2-(i in s) for i in V):continue
        if any(len(N[i]&N[j])>=2-(j in N[i]) for i,j in combinations(s,2)):continue
        res.append(s)
    return res
def centers(f,g):
  allw=cwords();out=Counter();first=None
  for blk,reg in choices(f,g):
    near=set.union(*blk);far=V-near;F,Fm,G,Gm=sides[f],sides[f^1],sides[g],sides[g^1]
    if len(near)!=7:continue
    a,=reg[0]&blk[0];b,=reg[0]&blk[1];c,=reg[0]&blk[2]
    # inner mate additions a',b',c' at 24,25,26, then triangle parents 27,28,29
    targ={x:1+int(x in F)+int(x in G)-int(x in Fm)-int(x in Gm)-len(N[x]&reg[0]) for x in far}
    if min(targ.values())<0 or max(targ.values())>3:continue
    for ac in (1,):
      if int(c in N[a])!=ac:continue
      wnear=[{a}|({c} if not ac else set()),{b},{c}|({a} if not ac else set())]
      choices3=[[s for s in allw if s&near==req and all(targ[x]>0 for x in s&far)] for req in wnear]
      out['chart']+=1
      for X,Y,Z in product(*choices3):
        if any(sum(x in s for s in (X,Y,Z))!=targ[x] for x in far):continue
        out['marg']+=1
        R=[set(N[i]) if i<24 else set() for i in range(30)]
        def add(i,j):R[i].add(j);R[j].add(i)
        for i,j in ((24,25),(25,26),(27,28),(27,29),(28,29)):add(i,j)
        if ac:add(24,26)
        for ii,ss in enumerate((X,Y,Z)):
            for i in ss:add(24+ii,i)
            add(24+ii,27+ii)
        for ii,ss in enumerate(blk):
            for i in ss:add(27+ii,i)
        p,=sides[f]&sides[g]
        assert p in N[b] and p in Y and b in Y
        assert b in blk[1] and 25 in R[b] and R[b]&R[25]>={p,28}
        if any(len(R[i]&R[j])>2-(j in R[i]) for i,j in combinations(range(30),2)):continue
        out['surv']+=1
        if first is None:first=(blk,reg,ac,X,Y,Z)
  return out,first
if __name__=='__main__':
    ct,first=centers(0,2)
    assert ct=={'marg':4,'chart':4} and first is None
    print("Four labeled middle charts, four far-contact triples; all four give a second cap on the same mate edge.")
