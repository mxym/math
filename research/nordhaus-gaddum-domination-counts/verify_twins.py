"""Independent exact finite tests of the three quantitative twin-cube steps."""
from fractions import Fraction as F
from itertools import combinations
from verify import check,rows,comp,cubes

def constants():
    n=160
    check(F(62*n,n-5)<=64)
    check(F(n,2)-F(67,2)>=F(93,2));check(F(93,2)/5>9)
    check(2*11**2*(1<<72)<(1<<(n//2)))
    check(9*F(1,2**14)+6*F(1,64)<F(1,8))
    for epsilon in (0,1):
        values=[F(63,64)*F(2)**(j+1)+F(2)**(epsilon-j-1) for j in range(-2,3)]
        check(min(values)==(F(2)-F(1,64) if epsilon==0 else F(3)-F(1,32)))
    check(F(2,32)+F(1,64)<F(1,8))
    check(F(1,128)+F(1,32)+F(1,64)<F(1,8))
    return True

def shadows():
    num=0
    for n in range(1,7):
        for s in range(n+1):
            pool=[i for i in range(1<<n) if i.bit_count()==s]
            for k in range(1,min(4,len(pool))+1):
                for sets in combinations(pool,k):
                    check(cubes(sets).bit_count()*(1<<k) >= (1<<(s+1))*((1<<k)-1))
                    num+=1
    return num

def cohorts():
    count=0
    for n in range(2,7):
        for g in range(1<<(n*(n-1)//2)):
            A=rows(n,g); B=comp(A)
            for s in {a.bit_count() for a in A}:
                R=[i for i,a in enumerate(A) if a.bit_count()==s]
                a={A[i] for i in R};b={B[i] for i in R};r=len(R)
                check(len(a)+len(b)>=r+1)
                if len(a)==1:
                    T=next(iter(a)); check(cubes(b).bit_count()==(1<<(n-s))-(1<<(n-s-r)))
                if len(b)==1:
                    T=next(iter(b));t=T.bit_count()
                    check(cubes(a).bit_count()==(1<<(n-t))-(1<<(n-t-r)))
                count+=1
    return count
if __name__=='__main__':
    constants();print('PASS n=160/r=10/k=6 and all normalized budgets as integer comparisons.')
    print(f'PASS {shadows()} antichain subcube families (up to 4 equal-size subsets of a 6-set).')
    print(f'PASS {cohorts()} degree cohorts (all labelled graphs through n=6): duplicate-count sum and exact twin closures.')
