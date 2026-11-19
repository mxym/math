from itertools import product
q=11; qr={x*x%q for x in range(1,q)}
U=[[1]*(q+1)]+[[1]+[(1 if (i-j)%q in qr else -1) for j in range(q)] for i in range(q)]
A=list(product(range(12),repeat=2))
S=[[U[i][l]*U[k][j] for k,l in A] for i,j in A]
def unit_rows(H):
    n=len(H)
    return all(sum(u*v for u,v in zip(H[i],H[j]))==n*(i==j)
       for i in range(n) for j in range(i+1))
def need(b):
    if not b:raise ArithmeticError('failed')
need(unit_rows(U));need(unit_rows(S)); need(all(S[i][j]==S[j][i] and S[i][i]==1 for i,j in product(range(144),repeat=2)))
print('144 vertices, symmetric sign table with positive diagonal, S S^T=144 I, Forster lower bound 12; edges',sum(S[i][j]==1 for i in range(144) for j in range(i)))
