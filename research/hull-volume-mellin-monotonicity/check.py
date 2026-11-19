"""Exact finite illustration of the endpoint obstruction for planar n=4; not the general proof."""
from fractions import Fraction as Q
from itertools import product

def wedge(a,b,c):
    return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])

def hull(points):
    def half(P):
        H=[]
        for p in P:
            while len(H)>=2 and wedge(H[-2],H[-1],p)<=0:H.pop()
            H.append(p)
        return H
    P=sorted(set(points))
    if len(P)<=1:return P
    return half(P)[:-1]+half(P[::-1])[:-1]

def area(points):
    P=hull(points)
    return abs(sum(P[i][0]*P[(i+1)%len(P)][1]-P[i][1]*P[(i+1)%len(P)][0] for i in range(len(P))))*Q(1,2)

def req(test,msg):
    if not test:raise ArithmeticError(msg)

def main():
    S=[(Q(x),Q(y)) for x,y in [(-1,0),(1,0),(1,1),(-1,1)]]
    tip=(Q(0),-Q(1,8))
    L=S+[tip]
    # Horizontal cut y=-7/64 intercepts both edges adjacent to tip at x=+-1/8.
    cut=[(-Q(1,8),-Q(7,64)),(Q(1,8),-Q(7,64))]
    K=S+cut
    R=[tip]+cut
    M=max(area(P) for P in product(L,repeat=4))
    out=max(area((t,)+P) for t in R for P in product(L,repeat=3))
    ratio=area(K)/area(L)
    req(M==2 and out==Q(107,64) and area(L)==Q(17,8) and ratio==Q(1087,1088), (M,out,area(K),area(L),ratio))
    print('Planar n=4: exact common maximum',M,'and upper bound with any exterior sample',out)
    print('Volumes K, L:',area(K),area(L),' ; high-tail ratio =',ratio,'to the fourth power')
    print('PASS: 625 all-generator and 375 cap-vertex triples checked; illustration only.')
if __name__=='__main__':main()
