from fractions import Fraction as F
from itertools import permutations

def need(x):
    if not x: raise ValueError('rational certificate failed')
def det(M):
    return sum((-1)**sum(k>l for i,k in enumerate(p) for l in p[i+1:]) *
               prod(M[i][k] for i,k in enumerate(p)) for p in permutations(range(len(M))))
def prod(items):
    a=1
    for x in items:a*=x
    return a
def trace_inv(M):
    return sum(det([[M[i][j] for j in range(len(M)) if j!=k] for i in range(len(M)) if i!=k]) for k in range(len(M)))/det(M)
def val(X,Y):
    n=len(X)
    M=[[int(i==j)+(X[i][j]+Y[i][j])/2 for j in range(n)] for i in range(n)]
    for k in range(1,n+1):need(det([r[:k] for r in M[:k]])>0)
    return trace_inv(M)
def gap(X,Y):return (val(X,X)+val(Y,Y))/2-val(X,Y)
def matrix(rows):return [[F(x) for x in row] for row in rows]
def main():
    A=matrix([[1,-2,0],[-2,31,0],[0,0,47]])
    B=matrix([[1,0,0],[0,23,0],[0,0,55]])
    C=matrix([[1,2,0],[2,31,0],[0,0,47]])
    for M in [A,B,C]:
        need(sum(M[i][i] for i in range(3))==79)
        for k in (1,2,3):need(det([r[:k] for r in M[:k]])>0)
    a,b,c=gap(A,B),gap(B,C),gap(A,C)
    need(a==b==F(23,2640)+F(1,8736))
    need(c==F(17,480)); g=c-4*a
    need(g==F(1,1760)-F(1,2184)>0)
    print(f'PASS: full 3x3 inverse/cofactor exact: equal short squared distances {a}, long squared distance {c}, square-test surplus {g}>0.')
if __name__=='__main__':main()
