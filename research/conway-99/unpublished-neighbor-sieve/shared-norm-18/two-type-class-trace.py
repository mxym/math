"""Exact raw and class-centered trace lower bounds on intersecting 18-support pairs."""
from fractions import Fraction as Q
from math import ceil
from itertools import combinations
def main():
    residues=[(1,0),(0,1),(2,2),(2,-2)]
    def dot(x,y):return 4*sum(a*b for a,b in zip(x,y))%7
    assert all(dot(v,v)==4 for v in residues)
    dots=[dot(x,y)for x,y in combinations(residues,2)]
    assert dots.count(0)==2 and all(x in (0,1,6)for x in dots)
    for m,k0,end,raw,cen in [
        (1,50,54,[611,648,687,726,766],[810,855,901,948,997]),
        (3,51,53,[804,849,895],[978,1029,1081])]:
        d=44-m
        for i,n in enumerate(range(k0,end+1)):
            rhs=Q((72*n)**2,d)-(1296*n+64*n*(n-1)+8*n*n)
            assert ceil(rhs/98)==raw[i]
            mu=Q(2*(144+d),4+d)
            def bound(u):
                return Q(n*n,98)*((72-u)**2/d-48-u+u*u/4-Q(1176,n))
            assert 2*(mu-72)/d-1+mu/2==0
            assert ceil(bound(mu))==cen[i]
            print("M, per-class, raw, centered:",m,n,raw[i],cen[i])
    assert 50*810//2==20250 and (978-810)//2==84
    assert Q(8*(50-6*7),4)==16
if __name__=="__main__":main()
