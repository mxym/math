"""Exact integer checks for the planar example and parity exclusions."""
from itertools import product,combinations,combinations_with_replacement
from collections import Counter
from math import prod,comb

def require(c,msg):
    if not c:raise ValueError(msg)
def main():
    v=((0,1),(1,-1),(1,-1),(1,-1),(2,1));n=len(v)
    E=sum(sum(x*x for x in u) for u in v);sg=list(product((1,-1),repeat=n))
    D=Counter(sum(sum(s*u[t] for s,u in zip(x,v))**2 for t in (0,1)) for x in sg)
    require(E==12 and D=={2:6,10:20,26:4,34:2},'wrong length distribution')
    require(sum(k*c for k,c in D.items())==32*E,'wrong expectation')
    require(sum(c for k,c in D.items() if k>=E)==6 and E not in D,'wrong outer tail')
    require([[sum(u[i]*u[j] for u in v) for j in range(2)] for i in range(2)]==[[7,-1],[-1,5]],'covariance')
    counts=[]
    for n,exceptions in ((4,1),(5,2)):
        sg=list(product((1,-1),repeat=n));cl=[x for x in sg if x[0]==1]
        cand=list(combinations(range(n),4));ct=0
        for bad in combinations_with_replacement(cl,exceptions):
            cover=False
            for s in cand:
                chi=lambda x:prod(x[k] for k in s)
                forbidden={chi(x) for x in bad}
                if len(forbidden)!=1:continue
                clean=[x for x in sg if chi(x) not in forbidden]
                require(len(clean)==len(sg)//2,'wrong halfcube')
                require(all(sum(x[i]*x[j] for x in clean)==0 for i,j in combinations(range(n),2)),
                    'uncentered quadratic character')
                require(all(x not in clean and tuple(-a for a in x) not in clean for x in bad),
                    'included forbidden representative or antipode')
                cover=True;break
            require(cover,'missing orthogonal witness');ct+=1
        require(ct==comb(len(cl)+exceptions-1,exceptions),'incomplete orbit coverage');counts.append(ct)
    print('PASS: 32 integer sign sums; histogram 2:6, 10:20, 26:4, 34:2; 6/32 >=12; 0 ties.')
    print(f'PASS: parity witnesses for all {counts[0]} one-class choices at n=4 and {counts[1]} two-class multisets at n=5.')
if __name__=='__main__':main()
