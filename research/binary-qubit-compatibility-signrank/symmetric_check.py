"""Exact independent checks for the 144-vertex complement to the parity example."""
def require(v,desc):
    if not v:raise ValueError(desc)
N=11
residues={i*i%N for i in range(1,N)}
require(residues=={1,3,4,5,9},'quadratic character')
U=[[1 if i==N or j==N or (j-i)%N in residues else -1 for j in range(N+1)] for i in range(N+1)]
V=[(i,j) for i in range(12) for j in range(12)]
def check_g(A,n):
    require(len(A)==n and all(len(r)==n for r in A),'shape')
    for x,row in enumerate(A):
        for y in range(x,n):
            require(sum(s*t for s,t in zip(row,A[y]))==n*(x==y),'Gram')
check_g(U,12)
S=[[U[i][l]*U[k][j] for k,l in V] for i,j in V]
require(all(S[i][i]==1 and all(S[i][j]==S[j][i] for j in range(i)) for i in range(144)),'symmetric positive diagonal')
check_g(S,144)
require(144//12==12>11,'rank gap')
print('Seed 12x12; S 144x144 symmetric, diagonal +1, SS^T=144I; strict sign-rank >=12.')
print('vertices=144; edges='+str(sum(S[i][j]==1 for i in range(144) for j in range(i))))
