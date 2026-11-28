#!/usr/bin/env python3
from fractions import Fraction

def require(x,msg):
    if not x: raise AssertionError(msg)

rows=[]
for k in range(3,13):
    alpha={m:Fraction(1,2**(k-m)) for m in range(2,k+1)}
    require(alpha[k]==1,"far scale")
    for m in range(2,k):
        require(2*alpha[m]+sum(alpha[s] for s in range(m+1,k+1))==2,
                "profile exponent")
    total=sum(alpha.values())
    require(total==2-Fraction(1,2**(k-2)),"geometric sum")
    shell=(1+total)/k
    old=Fraction(3,k)-Fraction(2,k*k)
    rows.append((k,str(alpha[2]),str(shell),shell>old))
require(rows[1][0]==4 and rows[1][2]=="11/16","k=4 shell")
print("multiscale shell exponent checker")
print("k alpha_2 shell_exponent beats_uniform_shell_lower_bound")
for row in rows:
    print(*row)
print("profile_equalities = PASS")
print("geometric_sum = PASS")
print("k4_shell_exponent_11_over_16 = PASS")
print("standard_library_only = PASS")
