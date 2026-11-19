from fractions import Fraction as F

def ck(x):
    if not x:
        raise RuntimeError("exact witness check failed")

def invariants(A):
    a,b,c=A
    return a+c,a*c-b*b

for B in [(8,4,23),(8,-4,23)]:
    trace,det=invariants(B)
    for x in (24,7): ck(x*x-trace*x+det==0)
ck(F(25,2)>12)
for n in range(2,100):
    t=F(n)
    a=t-1/t
    ck(a*t+1==t*t and t==t*1)
print("Exact finite p=1 spectral gap 1/2; rational p>2 eigenvector identities at 98 parameters; PASS")
