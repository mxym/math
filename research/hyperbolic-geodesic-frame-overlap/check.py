from fractions import Fraction as Q

def check(v):
    if not v:
        raise ArithmeticError("algebraic identity")

cases=0
for i in range(1,60):
    c=Q(i,60)
    t=c*c
    for j in range(41):
        A=1+Q(j,19)
        check((1/(A-c)-1/(A+c))/c == 2/(A*A-t))
        check((A-1)/(A+1) < 1)
        if j:
            B=A*A-1
            tangent=2*Q(1)/(1-(A-1)/(A+1))
            check(tangent*tangent*(A-1)/(A+1)==B)
        cases+=1
print("resolvent difference quotients and tangent doubling:",cases)

pairs=0
for n in range(3,21):
    d=n-1
    G=[[Q(1) if i==j else Q(-1,d) for j in range(n)] for i in range(n)]
    for i in range(n):
        check(sum(G[i])==0)
        for j in range(n):
            check(sum(G[i][k]*G[k][j] for k in range(n))==Q(n,d)*G[i][j])
            if i!=j:
                check(G[i][j]**2==Q(n-d,d*(n-1)))
                pairs+=1
print("ordered simplex Gram/off-diagonal checks:",pairs)
