"""Finite rational algebra checks only.  Run under Python 3, also with -O."""
from fractions import Fraction as F
from itertools import combinations_with_replacement as comb, product

def main():
    if -F(1,2)**2/2+F(1,24)!=-F(1,12):
        raise ArithmeticError("log cosine")
    count=0
    for n in range(1,8):
        for u in comb(range(4),n):
            if not any(u):
                continue
            sums=[sum(i*j for i,j in zip(u,w)) for w in product((-1,1),repeat=n)]
            v=sum(i*i for i in u)
            if F(sum(z*z for z in sums),2**n)!=v or F(sum(z**4 for z in sums),2**n)!=3*v*v-2*sum(i**4 for i in u):
                raise ArithmeticError(("Rademacher moment",u))
            count+=1
    # Positive rational quadrature lower bound on log 2: subdivide [1,2] in two.
    lower=(F(4,5)+F(4,7))/2
    if lower-F(2,3)!=F(2,105):
        raise ArithmeticError("midpoint slack")
    print("Exact sign-sum second/fourth moments:",count,"coefficient lists")
    print("Cosine logarithm quartic coefficient: -1/12")
    print("Two-cell midpoint lower bound for log(2) - 2/3:",lower-F(2,3))
    print("PASS finite identities only; inequality for all lists/exponents is analytic.")

if __name__=="__main__":
    main()
