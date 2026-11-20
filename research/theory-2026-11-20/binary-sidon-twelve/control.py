from itertools import combinations
from functools import reduce
from operator import xor
from check import data,ROOT,ck
S=list(map(int,(ROOT/'control66.txt').read_text().split()))
ck(len(S)==len(set(S))==66 and len({a^b for a,b in combinations(S,2)})==2145,'control Sidon')
# Explicit coordinate direction pair so that an even layer XOR is nonzero.
def split(j,k):
    rem=[i for i in range(12)if i not in (j,k)];A=[[] for _ in range(4)]
    for x in S:
        v=sum((x>>b&1)<<a for a,b in enumerate(rem));A[(x>>j&1)+2*(x>>k&1)].append(v)
    return A
for j,k in combinations(range(12),2):
    A=split(j,k);N=tuple(map(len,A));ii=[i for i in range(4)if N[i]%2==0]
    E=[reduce(xor,A[i],0)for i in ii]
    if max(E,default=0):break
else:raise ValueError('control must test nonzero XOR')
coords={0:0};basis=[]
for h in E:
    if h not in coords:
        b=1<<len(basis);basis.append(h);coords.update({x^h:y^b for x,y in list(coords.items())})
g=tuple(coords[v]for v in E);M=1<<len(basis)
ex=data(N,N,1,ii,g,0,True);s=[0]*len(ex)
direct=[{x^y for x,y in combinations(a,2)}for a in A]
tagset=set()
for t in range(1024):
    tag=sum(((t&h).bit_count()%2)<<b for b,h in enumerate(basis));tagset.add(tag)
    w=[sum(1-2*((x&t).bit_count()%2)for x in a)for a in A]
    ck(all(((N[i]-abs(w[i]))//2)%2==((g[b]&tag).bit_count()%2)for b,i in enumerate(ii)))
    row=data(N,list(map(abs,w)),-1 if w[0]*w[1]*w[2]*w[3]<0 else 1,ii,g,tag,False)
    s=[x+y for x,y in zip(s,row)]
ck(len(tagset)==M and M>=2,'sign must vary');off=16+M
ck(s[:off]==ex[:off] and all(x<=y for x,y in zip(s[off:],ex[off:])))
for ix,d in enumerate(range(1,M)):
    h=reduce(xor,(v for i,v in enumerate(basis)if d>>i&1),0)
    v=[2048*int(h in ds)for ds in direct]
    ck(s[off+9*ix:off+9*(ix+1)]==sum(([-x,x]for x in v),[])+[sum(v)],'actual signed second moments')
print(f'66-point positive control: axes {j},{k}; layers {N}; even XOR span rank {len(basis)}; both signs verified. PASS')
