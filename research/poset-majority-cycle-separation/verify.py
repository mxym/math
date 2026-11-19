"""No dependencies. Exact two-chain shuffle counts and beta-median signs."""
from fractions import Fraction as F
from math import comb

def check(ok, label):
    if not ok:
        raise ValueError(label)

def pair(a, i, b, j):
    # Fix positions of all 'a' letters. I-th precedes j-th iff first i+j-1 positions have at least i of 'a'.
    k=i+j-1
    return F(sum(comb(k,h)*comb(a+b-k,a-h) for h in range(max(i,k-b),min(k,a)+1)),comb(a+b,a))

def tail(a,i,t): # Pr[U_(i)>t]
    return sum(comb(a,h)*t**h*(1-t)**(a-h) for h in range(i))

def main():
    M=1_000_000
    L,R=F(12947,100000),F(2591,20000)
    l,r=int(L*M),int(R*M)
    check(l==129470 and r==129550 and r-l+3==83, "ranks/length")
    x=pair(28,4,5,1)
    y=pair(5,1,M,l)
    z=1-pair(28,4,M,r)
    check(x==F(1365,2728),"first pair")
    for label,v in [('A4 before B1',x),('B1 before C_l',y),('C_r before A4',z),
                    ('B1 below L',1-tail(5,1,L)),('A4 above R',tail(28,4,R))]:
        print(label, 'excess above 1/2 exceeds', (v-F(1,2))*1_000_000//1,'parts per million')
        check(v-F(1,2)>F(5,100000),label)
    for label,value in [('B1 before C1295',pair(5,1,10000,1295)),('C1296 before A4',1-pair(28,4,10000,1296))]:
        print('M=10000:',label,'excess above 1/2 exceeds',(value-F(1,2))*1_000_000//1,'parts per million')
        check(value-F(1,2)>F(3,100000),label)
    print('cycle 83 versus restricted upper bound',2*(28+5))
if __name__=='__main__': main()
