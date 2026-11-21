from itertools import combinations,combinations_with_replacement
from math import isqrt
from collections import Counter
def ck(v,m):
    if not v:raise ValueError(m)
def prime(x):return x>=2 and all(x%j for j in range(2,isqrt(x)+1))
def move(a,b):
    x=list((Counter(a)-Counter(b)).elements());y=list((Counter(b)-Counter(a)).elements())
    return len(x)==len(y)==2 and sum(x)==sum(y)
def main():
    rail=[(3,3,3,3,17,17),(3,3,3,3,5,29),(3,3,3,5,13,19),(3,3,5,5,13,17),(3,3,3,5,13,19),
      (3,3,5,5,11,19),(3,5,5,5,11,17),(3,5,5,5,5,23),(5,5,5,5,13,13)]
    ck(all(x!=7 and prime(x) for state in rail for x in state),'genuine')
    ck(all(move(x,y) for x,y in zip(rail,rail[1:])),'rail')
    P=[i for i in range(3,24) if i!=7 and prime(i)];cub=[s for s in combinations_with_replacement(P,3) if sum(s)==23]
    ck(all(not move((3,3,17),s) for s in cub),'not isolated')
    print('complete thinned weight23 fiber',cub,'square zero path',len(rail)-1,'moves')
    counts=0
    for ell in [2,3,5,7,11,13,17,19,23,29,31]:
      for s in ([1] if ell==2 else [0] if ell==3 else range(ell)):
        if ell==3:a,b,p,y=1,1,2,1
        elif ell==2:a,b,p,y=1,1,1,1
        else:
         a=1;b=next(i for i in range(1,ell) if (s-a-i)%ell);c=s-a-b
         p=next(i for i in range(1,ell) if (3+a-i)%ell)
         y=next(i for i in range(1,ell) if (b+p-i)%ell and (i+c-3)%ell)
        c=s-a-b;q=3+a-p;u=b+p-y;d=y+c-3
        ck(all(z%ell for z in (a,b,c,p,q,y,u,d)),'local');counts+=1
    print('local bridge charts',counts)
    s=10005;P=[p for p in range(1000,6250) if prime(p)]
    ok=False
    for a in [a for a in P if a%3==1 and 4000<a<4800]:
      for b in [b for b in P if b%3==1 and 2400<b<3000]:
       c=s-a-b
       if not prime(c):continue
       for p in [p for p in P if p%3==2 and 1850<p<2400 and prime(3+a-p)]:
        q=3+a-p
        for y in [r for r in P if r!=b and r%3==1 and 2400<r<3000]:
         u=b+p-y;d=y+c-3
         if prime(u) and prime(d):
          rail=[(3,a,b,c),(p,q,b,c),(u,q,y,c),(3,u,q,d)]
          if all(move(x,y) for x,y in zip(rail,rail[1:])):
           print('literal x3 bridge',rail);ok=True;break
        if ok:break
       if ok:break
      if ok:break
    ck(ok,'no witness');print('PASS')
if __name__=='__main__':main()
