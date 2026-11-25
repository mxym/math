from itertools import permutations, product
from math import prod
from sympy import Matrix

def pair(a, b):
    return [tuple(minor if j == i else major for j in range(3))
            for major, minor in ((a, b), (b, a)) for i in range(3)]

def excess(u, v):
    return sum(int(v[i] != u[i]) + int(v[i] != u[(i+1)%3])
               - int(u[i] != u[(i+1)%3]) for i in range(3))

def block(rows, cols, h):
    return Matrix([[int(excess(u, v) == h) for v in cols] for u in rows])

X, T = pair(0, 1), list(permutations(range(3)))
Z = Matrix([[-1,-1],[1,0],[0,1],[-1,-1],[1,0],[0,1]])
M = block(X, X, 0)
assert M.rank() == 4 and Z.rank() == 2
assert M*Z == Matrix.zeros(6, 2) and Z.T*M == Matrix.zeros(2, 6)
assert Z.T*block(X, [(i,)*3 for i in range(3)], 0) == Matrix.zeros(2, 3)
H = Matrix([[2,-2],[4,2]])
for pair_labels in [(0,1), (0,2), (1,2)]:
    Y = pair(*pair_labels)
    C = Z.T*(block(X,Y,1) - block(X,T,1)*block(T,T,0).inv()*block(T,Y,0))*Z
    assert C == (-H if pair_labels == (0,1) else H)

K = [[1,1,1],[1,2,3],[1,4,5]]
words = list(product(range(3), repeat=4))
assert words.pop(79) == (2,2,2,1)
p = 101
M = [[prod(K[u[j]][v[j]] * K[v[j]][u[(j+1)%4]] for j in range(4))%p
      for v in words] for u in words]
det = 1
for j in range(len(M)):
    i = next(i for i in range(j,len(M)) if M[i][j])
    M[j], M[i] = M[i], M[j]
    a = M[j][j]
    det = det*a*(-1 if i != j else 1)%p
    for i in range(j+1,len(M)):
        b = M[i][j]*pow(a,-1,p)%p
        for k in range(j,len(M)):
            M[i][k] = (M[i][k]-b*M[j][k])%p
assert det == 94
print("Six-cycle blocks and eight-cycle minor verified.")
