from math import comb
from itertools import product,combinations
from collections import Counter,defaultdict
from fractions import Fraction as F

def ep4(z,p,q):
 # real part of [t^4](1+t)^z(1+w t)^p(1+w^2 t)^q
 return sum(F(2 if (i-j)%3==0 else -1,2)*comb(p,i)*comb(q,j)*comb(z,4-i-j)
    for i in range(min(4,p)+1)for j in range(min(4-i,q)+1)if 4-i-j<=z)
M=1023
def add(a,b):
 l=a&M;h=a>>10;v=b&M;w=b>>10
 a0=M^(l|h);b0=M^(v|w)
 return (a0&v|b0&l|h&w)|((a0&w|b0&h|l&v)<<10)
def neg(a):return (a>>10)|((a&M)<<10)
def maskg(v):
 s=[v[i]*v[j]%3 for i in range(4)for j in range(i,4)]
 return sum(1<<i for i,x in enumerate(s)if x==1)+sum(1<<(10+i)for i,x in enumerate(s)if x==2)
def pro(v):return min(tuple(v),tuple(-i%3 for i in v))
def ip(u,v):return sum(a*b for a,b in zip(u,v))%3
def part(gs,k=9):
 def rec(start,sz,p,t):
  yield sz,p,t
  if sz==k:return
  for j in range(start,len(gs)):yield from rec(j+1,sz+1,p|1<<j,add(t,gs[j]))
 yield from rec(0,0,0,0)
def ids(m):
 while m:b=m&-m;m-=b;yield b.bit_length()-1
def proper(cols,X):return all(sum(ip(a,b)==1 for a in cols)in(6,9) for b in X)
def blocks(cols):
 B=defaultdict(set)
 for i,j in combinations(range(22),2):B[tuple((x+y)%3 for x,y in zip(cols[i],cols[j]))].add((i,j))
 F=set()
 for s,E in B.items():
  for i,j in E:
   for k,l in B.get(tuple(-x%3 for x in s),()):
    if j<k:F.add((i,j,k,l))
 return sorted(F)
def solve(z):
 e1,e2,e3=(1,0,0,0),(0,1,0,0),(0,0,1,0)
 sing=[e1,e2,(2,2,0,0)] if z else [e1,e2,e3,(2,2,2,0)]
 P=[v for v in product(range(3),repeat=4)if any(v) and v==pro(v)];U=[v for v in P if v not in list(map(pro,sing))];X=[v for v in product(range(3),repeat=4)if any(v)]
 gram=[maskg(v)for v in U];target=0
 for v in sing:target=add(target,maskg(v))
 L=len(U)//2;H=defaultdict(list)
 for sz,p,t in part(gram[:L]):H[sz,t].append(p)
 stats=Counter();hist=Counter();full=[]
 for sz,p,t in part(gram[L:]):
  for a in H.get((9-sz,add(target,neg(t))),()):
   stats['gram']+=1; Pts=[U[i]for i in ids(a|(p<<L))]
   C=[(0,0,0,0)]*z+sing+Pts+[tuple(-x%3 for x in v)for v in Pts]
   # each projective functional test both orientations
   if not proper(C,X):continue
   stats['code']+=1;F=blocks(C)
   E=Counter(e for B in F for e in combinations(B,2));mn=min(E.get(ij,0)for ij in combinations(range(22),2));hist[mn]+=1
   if mn>=2:full.append(C)
 expected=({0:162,1:324} if z==0 else {1:648})
 assert hist==expected and not full
 print('zero columns:',z,'normalized self-orthogonal candidates:',stats['gram'],'minimum pair counts:',dict(sorted(hist.items())))


def profiles():
    res=[]
    for z in range(3):
        for u,h,g in product(range(5),range(2),range(2)):
            # The full cost budget; (1,1) directions cost zero.
            if z*z+u+3*h+4*g!=4:continue
            n11,rem=divmod(22-z-u-3*h-4*g,2)
            if rem or n11<0:continue
            seq=[(1,0)]*u+[(1,1)]*n11+[(2,1)]*h+[(2,2)]*g
            n=22-z; pp=sum(comb(a+b,2)for a,b in seq)
            m1=F(2*n*81,3);m2=F((4*n*n+2*n+4*pp)*81,9)
            a18=(m2-27*m1+180*80)/18
            a15=(m1-12*80-6*a18)/3;a12=80-a18-a15
            N=(comb(22,4)+a12*ep4(10,6,6)+a15*ep4(7,9,6)+a18*ep4(4,9,9))/81
            assert N.denominator==1
            contrib=[comb(z,2)]+[a*b for a,b in seq]
            H=sum(contrib)
            T=sum(x*y for x,y in combinations(contrib,2))+comb(z,4)+sum(comb(a,2)*comb(b,2)for a,b in seq)
            key=(z,u,n11,h,g);res.append((key,int(N-T+H)))
    assert sorted(res)==[((0,0,9,0,1),55),((0,1,9,1,0),68),((0,4,9,0,0),80),((1,0,9,1,0),70),((1,3,9,0,0),82),((2,0,10,0,0),71)]
    print('six upper capacities:',sorted(res))

if __name__=='__main__':
 profiles()
 solve(0)
 solve(1)
