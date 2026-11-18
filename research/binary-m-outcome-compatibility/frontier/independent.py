"""Exact arithmetic illustrations of the equality and label-count arguments.
Not a proof of unrestricted dimension. Standard library; no assertions disabled by -O.
"""
from fractions import Fraction as Q
def ck(ok, name):
    if not ok: raise ArithmeticError(name)
def mat(f,n): return tuple(tuple(Q(f(i,j)) for j in range(n)) for i in range(n))
def ident(n): return mat(lambda i,j:i==j,n)
def pr(n,indices): return mat(lambda i,j: i==j and i in indices,n)
def mul(A,B):
    cols=list(zip(*B)); return tuple(tuple(sum(x*y for x,y in zip(row,col)) for col in cols) for row in A)
def prod(*A):
    M=A[0]
    for N in A[1:]: M=mul(M,N)
    return M
def tr(A): return sum(A[i][i] for i in range(len(A)))
def trans(A): return tuple(zip(*A))
def lin(*pairs):
    return mat(lambda i,j:sum(a*M[i][j] for a,M in pairs),len(pairs[0][1]))
def chkmodel(S,Ps):
    n,m=len(S),len(Ps); I=ident(n); Z=pr(n,[])
    ck(trans(S)==S and mul(S,S)==I,'reflection')
    ck(lin(*[(1,P) for P in Ps])==I,'decomposition')
    for j,P in enumerate(Ps):
        ck(P==trans(P) and mul(P,P)==P and prod(P,S,P)==Z,'neutral projection')
        for k in range(j): ck(mul(P,Ps[k])==Z,'nonorthogonal labels')
    for a,c in [(0,3),(1,1),(1,2),(2,3),(3,7),(5,13)]:
        z=(m-1)*a*a+c*c
        b=Q(c*c-a*a,z); f=Q((m-2)*a*a+2*a*c,z)
        ck(0<=b<=1 and f==1-Q((c-a)**2,z),'visibilities')
        total=0
        for P in Ps:
            W=lin((a,I),(c-a,P))
            L=prod(W,S,W)
            R=prod(S,P,S)
            D=lin((a*a,I),(a*(c-a),P),(a*(c-a),R))
            # D >= 0 is a positive combination of known projections.
            ck(mul(L,L)==mul(D,D),'modulus square')
            total+=tr(D)
        ck(Q(total,z)==n*f,'witness trace norm')
def conn(S):
    v={0}
    while True:
        n={j for i in v for j,w in enumerate(S[i]) if w} | v
        if n==v:return len(v)==len(S)
        v=n
# m=4 true irreducible; any reducing projector for all coordinate projectors is diagonal.
S4=((0,0,Q(3,5),Q(4,5)),(0,0,Q(-4,5),Q(3,5)),(Q(3,5),Q(-4,5),0,0),(Q(4,5),Q(3,5),0,0))
ck(conn(S4),'irreducible')
for m in (4,5,9):
    chkmodel(S4,[pr(4,[j]) for j in range(m)])
# m=3: all three unordered pairs occur, conjugated inside each coarse outcome.
n=6; I=ident(n); Z=pr(n,[])
pairs=[(0,2),(1,4),(3,5)]
S0=mat(lambda i,j:(i,j) in pairs or (j,i) in pairs,n)
V=mat(lambda i,j: ((3,-4),(4,3))[i%2][j%2]*Q(1,5) if i//2==j//2 else 0,n)
S=prod(V,S0,trans(V))
P=[pr(n,[2*i,2*i+1]) for i in range(3)]
chkmodel(S,P)
for (i,j) in pairs:
    H=prod(V,pr(n,[i,j]),trans(V))
    ck(tr(H)==2 and H==mul(H,H) and mul(S,H)==mul(H,S),'qubit plane')
    for E in P: ck(mul(E,H)==mul(H,E),'plane does not reduce all labels')
# Projector onto ran(S_ij) is exactly S_ij S_ji.
for E in P:
    Vj=[prod(E,S,F,S,E) for F in P if F!=E]
    ck(all(mul(T,T)==T and tr(T)==1 for T in Vj),'row range')
    ck(mul(*Vj)==Z and lin((1,Vj[0]),(1,Vj[1]))==E,'row resolution')
# m=2 and extreme b=0,1; also verify exact rational chord slack at several x.
chkmodel(((0,1),(1,0)),[pr(2,[i]) for i in range(2)])
grid=[Q(i,31) for i in range(32)]
for a,c in [(1,2),(3,7),(2,9)]:
    for x in grid:
        gap=a*a+(c*c-a*a)*x-(a+(c-a)*x)**2
        ck(gap==(c-a)**2*x*(1-x) and (gap==0)==(x in (0,1)),'strict chord')
        for y in grid:
            target=a*a+a*(c-a)*(x+y)
            v=(a*a+(c*c-a*a)*x)*(a*a+(c*c-a*a)*y)-target**2
            ck(v>=0 and (v==0)==((x,y) in ((0,0),(0,1),(1,0))),'strict corners')
print('PASS: sharp witness on 5 models incl. irreducible dimension 4, 6 noise settings each (both endpoints)')
print('PASS: all 3 hidden qubit planes and three row resolutions in a non-coordinate 3-label family')
print('PASS: 96 rational chord tests and 3072 strict joint-corner tests; exact arithmetic')
