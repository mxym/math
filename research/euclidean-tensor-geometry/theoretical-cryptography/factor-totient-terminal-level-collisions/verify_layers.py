"""Known supported factorizations; verify exact leaf products and certified whole-component removal."""
from itertools import product, permutations
from math import gcd, prod, isqrt
from collections import Counter
def prime(n): return n>1 and all(n%z for z in range(2,isqrt(n)+1))
def layers(N,T):
    if N==1:return {},1,1,1
    g=gcd(N,T); D=N//g; U=T//g; K=N.bit_length()
    G=[1]+[gcd(N,pow(D,j,N)) for j in range(1,K+2)]
    H=[G[j]//G[j-1] for j in range(1,len(G))]
    d={j+1:H[j]//H[j+1] for j in range(K) if H[j]!=H[j+1]}
    assert prod(d.values())==D
    return d,D,U,N//G[-1]
def powers(exp):
    return prod(p**e for p,e in exp.items()),prod(p**(e-1)*(p-1) for p,e in exp.items())
def cert(N,ns,edges,j,d,expected=None):
    if not ns or len(set(ns))!=len(ns) or not all(prime(q) and N%q==0 for q in ns):return False
    if expected is not None and any(N%q**expected[q]!=0 or N%q**(expected[q]+1)==0 for q in ns):return False
    parents={v:[p for p,q in edges if q==v] for v in ns}
    if sum(not a for a in parents.values())!=1 or any(len(a)>1 for a in parents.values()):return False
    for q,a in parents.items():
        if gcd(N,q-1)!=(a[0] if a else 1):return False
    leaves=[p for p in ns if not any(a==p for a,q in edges)]
    return prod(leaves)==d and all(N%p**j==0 and N%p**(j+1)!=0 for p in leaves)

opts=[[(23,),(23,47),(23,139),(23,47,139),(23,47,283),(23,47,139,283)],
      [(29,),(29,59)],[(41,),(41,83)],[(53,),(53,107)]]
labels=sorted(set(permutations((1,1,2,3)))|set(permutations((1,1,2,2)))|{(1,2,3,4)})
covered=Counter(); rejections=Counter(); rows=0
for first in product(*opts):
 for extra in ((),((31,),),((19,191),)):
  trees=first+extra
  ss=tuple(p for tr in trees for p in tr)
  ed={(p,q) for p in ss for q in ss if (q-1)%p==0}
  tr_edges=[{(p,q) for p,q in ed if p in tr and q in tr} for tr in trees]
  assert len(ed)==sum(map(len,tr_edges)) and all(len(e)==len(tr)-1 for tr,e in zip(trees,tr_edges))
  for idx,lab0 in enumerate(labels):
   lab=lab0+tuple(5+i for i in range(len(extra)))
   exp={p:(1+(idx+p)%4 if any(a==p for a,q in ed) else j) for tr,j in zip(trees,lab) for p in tr}
   N,T=powers(exp);d,D,U,V=layers(N,T)
   assert d=={j:prod(p for tr,jj in zip(trees,lab) if jj==j for p in tr if not any(a==p for a,q in ed)) for j in lab}
   single=[i for i,j in enumerate(lab) if lab.count(j)==1]
   for i in single:
    tr,e,j=trees[i],tr_edges[i],lab[i]
    assert cert(N,tr,e,j,d[j],exp)
    nonleaf=next((p for p in tr if any(a==p for a,q in e)),None)
    if nonleaf is not None:
     bad=dict(exp);bad[nonleaf]+=1
     assert not cert(N,tr,e,j,d[j],bad);rejections["wrong nonleaf exponent"]+=1
    root=next(p for p in tr if not any(q==p for a,q in e))
    if len(tr)>1:
     rest=tuple(p for p in tr if p!=root)
     e2={(a,q) for a,q in e if a in rest}
     assert not cert(N,rest,e2,j,d[j]);rejections["missing root"]+=1
    if len(e)>1 and len([q for a,q in e if a==root])>1:
     leaf=next(p for p in tr if p!=root and not any(a==p for a,q in e))
     rest=tuple(p for p in tr if p!=leaf);e2={(a,q) for a,q in e if q!=leaf}
     assert not cert(N,rest,e2,j,d[j]);rejections["missing branch"]+=1
   to_peel={p for i in single for p in trees[i]}
   np,tp=powers({p:e for p,e in exp.items() if p in to_peel})
   nr,trp=powers({p:e for p,e in exp.items() if p not in to_peel})
   assert N==np*nr and T==tp*trp
   dr,Dr,Ur,Vr=layers(nr,trp)
   pairs=[j for j in set(lab) if lab.count(j)==2]
   assert dr=={j:d[j] for j in pairs}
   assert Vr==prod(p**exp[p] for p in ss if p not in to_peel and any(a==p for a,q in ed))
   if len(pairs)==2:
    types=sorted(sum(len(trees[i])>1 for i in range(len(trees)) if lab[i]==j) for j in pairs)
    typ=("A" if types[-1]==2 else "B" if types==[1,1] else "C" if types==[0,1] else "excluded")
    for j in pairs:
     ii=[i for i in range(len(trees)) if lab[i]==j]
     assert not cert(N,trees[ii[0]],tr_edges[ii[0]],j,d[j])
     rejections["false singleton"]+=1
   else:
    typ="zero" if not pairs else "one"
   covered[typ]+=1;rows+=1
assert all(covered[key]>0 for key in ("zero","one","A","B","C","excluded"))
print("layer and peeling fixtures",rows,"by case",sorted(covered.items()))
print("rejected subtree/singleton tests",sorted(rejections.items()))

# The counterexample's only nontrivial component is peeled.
s=(19,191,101,103,107,109)
assert all(prime(p) for p in s) and {(p,q) for p in s for q in s if (q-1)%p==0}=={(19,191)}
N,T=powers(dict(zip(s,(1,5,2,2,3,3))))
assert layers(N,T)[0]=={2:101*103,3:107*109,5:191}
