"""Exact finite adversarial tests; all logarithmic score signs are compared via integers."""
from itertools import combinations_with_replacement
from collections import Counter
from math import comb,prod

def need(b,msg):
    if not b:raise ArithmeticError(msg)

def sides(n,tt,r):
    m=n-1;d=2*r;cnt=Counter({n*r:1})
    for x in tt:
        nxt=Counter()
        for k,v in cnt.items():nxt[k+x]+=v;nxt[k-x]+=v
        cnt=nxt
    K=Counter();on=0;exp=Counter();q=2**n
    for s,num in cnt.items():
        k,j=divmod(s,d)
        if j==0:
            on+=num;exp[comb(n,k)]+=num*q
            if tt[0]!=r:K[k-1]+=num;K[k]+=num
        else:
            exp[comb(m,k)]+=num*q
            if tt[0]!=r:K[k]+=2*num
    for k in range(n+1):exp[comb(n,k)]-=on*comb(n,k)
    for k in range(m+1):exp[comb(m,k)]-=(q-on)*comb(m,k)*2
    if tt[0]!=r:
        need(sum(K.values())==2*q and min(K)>=0 and max(K)<=m,('K range',tt))
        for j in range(1,m//2+1):
            need(sum(v for k,v in K.items() if j<=k<=m-j)>=4*sum(comb(m,k) for k in range(j,m-j+1)),('middle',n,tt,j))
    # exp is log(Z_hi/Z_lo) scaled by 2^(2n).
    if n<=6:
        pos=prod(b**a for b,a in exp.items() if a>0)
        neg=prod(b**(-a) for b,a in exp.items() if a<0)
        need(pos>=neg,('actual score',tt))
        if tt[0]==r:need(pos==neg,('all-full',tt))
    return (0<on<q,on==0)

def main():
    a=b=c=0
    for n in range(1,9):
        r=6
        for tt in combinations_with_replacement(range(r+1),n):
            mixed,off=sides(n,tt,r);a+=1;b+=mixed;c+=off
    # Verify the integer tie-score certificate crudely by the binomial largest-posterior bound.
    for n in range(2,15):
        m=n-1
        num=prod(comb(n,k)**comb(n,k) for k in range(n+1))
        den=prod(comb(m,k)**(2*comb(m,k)) for k in range(m+1))
        need(num<=(2**(2**n))*den,('mu increment',n))
        for k in range(1,n):
            need(4*k*(n-k)<=n*n and n*comb(m,k-1)==k*comb(n,k) and n*comb(m,k)==(n-k)*comb(n,k),('ties',n,k))
    print(f'PASS: {a} sorted amplitude vectors, n=1..8, mesh 1/6; {b} mixed tie/off-grid, {c} fully off-grid. Exact score signs for all n<=6 and tie coefficients n<=14.')
if __name__=='__main__':main()
