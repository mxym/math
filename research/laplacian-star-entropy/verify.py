'''No imports outside stdlib, no asserts or floats. Elementary constants and independent small threshold cases.'''
from itertools import combinations
from math import prod
def check(x, msg):
    if not x: raise ArithmeticError(msg)
check(2**16>3**10,"x=1/3")
check(32**9>4*27**9,"k>=8")
ratios=[]
for k in range(1,8):
    u=k*(k+1)//2
    a,b=6*u*32**(3*u),2**(3*k)*27**(3*u)
    check(a>b,"small k")
    ratios.append(a//b)
check(ratios==[1,1,1,2,5,21,126],"floors")
cases=0
for N in range(1,14):
 for k in range(N):
  for J in combinations(range(1,N),k):
   s=sum(J); M=2*(s+N)
   mu=[sum(int(j>i)+(j+1)*(i==j) for j in J) for i in range(1,N)]
   q=[N+1,*[1+v for v in mu]]
   check(sum(q)==M,"trace")
   if not s:continue
   # Exact endpoint inequality (3), log-free
   check(prod(z**z for z in mu)<=(2*s)**s*2**k,"endpoint bound")
   # (5), exponentiated and denominators cleared
   check(prod((1+v)**((1+v)*N) for v in mu)*N**(M*N)<
         (N+s)**(M*N)*(N+1)**(s*(N+1)),"Shannon star")
   cases+=1
print("PASS: 9 strict integer comparisons; small-k floors",ratios)
print("PASS: exact endpoint and strict Shannon checks on",cases,"nonstar cone birth lists (N<=13).")
