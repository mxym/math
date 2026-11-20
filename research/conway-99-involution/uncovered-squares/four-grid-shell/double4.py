from itertools import product,permutations,combinations
import functools
E=list(combinations(range(4),2))
def dsolve():
 seen=set();by=[]
 for k in range(4096):
  words=[]
  for i,j in permutations(range(3),2):
   ji=j-(j>i);ii=i-(i>j);ph=((k>>i)&1)^ji;pf=(k>>(3+j)&1)^ii;fl=(k>>(6+i*2+ji)&1)
   for z in range(2):words.append((i*2+z,i*2+(z^ph),j*2+(z^fl),j*2+(z^fl^pf)))
  canon=tuple(sorted(words))
  if canon in seen:continue
  # group sym to enumerate reps without assuming actual automorphisms in original G: only 4fixed relaxed array.
  for pr in permutations(range(3)):
   for sw1,sw2,swe in product(range(2),repeat=3):
    p=[sw1,1-sw1,2+sw2,3-sw2];p=p[2:]+p[:2]if swe else p
    x=[tuple(2*pr[w[t]//2]+w[t]%2 for t in p)for w in words]
    for fls in product(range(2),repeat=4):seen.add(tuple(sorted(tuple(y^f for y,f in zip(w,fls))for w in x)))
  by.append(words)
 assert len(seen)==4096;return by
if __name__=='__main__':
 B=dsolve();print(len(B));print(B[0][:3]);open('double.dat','w').writelines(' '.join(str(sum(v*6**i for i,v in enumerate(w)))for w in bs)+'\n'for bs in B)
