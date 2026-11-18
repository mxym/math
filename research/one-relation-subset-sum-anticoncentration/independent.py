"""Check true cosets by integer walks, not saturated real lines or a projected hash."""
from itertools import product
from math import comb,prod
from collections import Counter
def need(ok):
    if not ok:raise ValueError('failed')
def Kmass(n,h):
    """Reflect all negative coordinates; starting at each unvisited point, walk forward."""
    lens=tuple(k+1 for k in n)
    # Lex order along first nonzero component points upward after reflection.
    w=tuple(abs(x) for x in h);d=len(h);need(any(w))
    seen=set();M=0;K=0;total=0
    bs=[tuple(comb(k,i) for i in range(k+1)) for k in n]
    for z in product(*(range(t) for t in lens)):
        if z in seen:continue
        K+=1;A=0
        while all(z[i]<lens[i] for i in range(d)):
            if z in seen:raise ValueError('overlap')
            seen.add(z)
            A+=prod(bs[i][j] for i,j in enumerate(z))
            z=tuple(z[i]+w[i] for i in range(d))
        total+=A;M=max(M,A)
    need(total==1<<sum(n) and len(seen)==prod(lens))
    return K,M
cnt=Counter()
for n,m in product(range(1,17),repeat=2):
 for b in range(1,10):
  for a in range(1,b+1):
    k,v=Kmass((n,m),(b,-a))
    need(k==(m+1)*(n+1)-max(0,m-a+1)*max(0,n-b+1))
    need(9*k*v*v<=8*4**(n+m))
    key='singleton fiber' if (n<b or m<a) else 'a=b=1' if b==1 else 'both >=2' if a>=2 else 'a=1 b=2' if b==2 else 'a=1 b>=3'
    cnt[key]+=1
print('PASS: 2D exact line mass:',sum(cnt.values()),dict(cnt))
sets=Counter()
for d in (3,4):
 for n in product((1,2,3),repeat=d):
  for l in product((1,2),repeat=d):
    k,v=Kmass(n,l)
    V=prod(i+1 for i in n)
    K=V-prod(max(0,n[i]+1-l[i]) for i in range(d));need(k==K)
    need(k*v*v<=4**sum(n))
    sets[n.count(1)]+=1
# zero outside active coordinates, nonprimitive, varied signs, boundary n_i<|h_i|
for n,h in [((2,1,5,1),(2,0,-2,0)),((1,6,5),(0,-5,4)),((4,3,2),(4,-2,2)),((1,1,1,1,1),(1,1,-1,1,2)),((1,1,1,1,1),(1,1,-1,1,-1))]:
 k,v=Kmass(n,h)
 need(k==prod(x+1 for x in n)-prod(max(0,x+1-abs(y)) for x,y in zip(n,h)))
 need(k*v*v<=4**sum(n))
print('PASS: 3D/4D boxes',sum(sets.values()),'by number of multiplicity-one types',dict(sorted(sets.items())), '+ 5 edge cases')
for d in range(3,501):
 a=comb(2*d,d)+2
 need(8*d*a*a<=3*16**d)
print('PASS: improved squared cyclic-peak bound at modulus 3..500 by exact coefficients')
