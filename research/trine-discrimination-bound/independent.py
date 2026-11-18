from fractions import Fraction
from math import lcm
from pathlib import Path
from itertools import permutations
import json,re
d=json.loads((Path(__file__).with_name('certificate.json')).read_text())
g=[[Fraction(0) for _ in range(24)] for _ in range(24)]
for i,row in enumerate(d['gram']):
    for j,v in enumerate(row,i):
        g[j][i]=g[i][j]=Fraction(v)
for i in range(24):g[i][i]-=Fraction(1,10**6)
scale=lcm(*(x.denominator for row in g for x in row))
M=[[int(x*scale) for x in row] for row in g]
last=1
for k in range(24):
    a=M[k][k]
    if a<=0: raise ArithmeticError(('leading principal minor',k))
    for i in range(k+1,24):
        for j in range(k+1,24):
            M[i][j],rem=divmod(a*M[i][j]-M[i][k]*M[k][j],last)
            if rem:raise ArithmeticError('nonexact Bareiss division')
    last=a
# Integer polynomial after clearing all denominators.
g=[[Fraction(0) for _ in range(24)] for _ in range(24)]
for i,row in enumerate(d['gram']):
    for j,v in enumerate(row,i):g[j][i]=g[i][j]=Fraction(v)
forms=[[( ''.join(chr(65+i) for i in a)+''.join(chr(97+i) for i in b),Fraction(c),len(b)) for a,b,c in u] for u in d['forms']]
scale=6*lcm(4,*(v.denominator for row in g for v in row))*lcm(*(v.denominator for f in forms for _,v,_ in f))**2
def reduce(s):
    s=''.join(filter(str.isupper,s))+''.join(filter(str.islower,s))
    while (t:=re.sub(r'(.)\1','',s))!=s:s=t
    return s
def reg(s,p):
    w='';sgn=1
    for c in s:
        if c.isupper():w+=chr(65+p[ord(c)-65]);continue
        i=ord(c)-97; a=p[i]; b=p[(i+1)%3]
        forward=(b-a)%3==1
        w+=chr(97+(a if forward else b))
        if not forward:sgn=-sgn
    return reduce(w),sgn
P={}
for i,f in enumerate(forms):
    for j,h in enumerate(forms):
        for u,a,s in f:
            for v,b,t in h:
                key=(reduce(u[::-1]+v),(s+t)%2)
                c=g[i][j]*a*b*3**((s+t)//2)*scale/6
                if c.denominator!=1:raise ArithmeticError('nonintegral coefficient')
                P[key]=P.get(key,0)+c.numerator
out={}
for p in permutations(range(3)):
    for (s,k),v in P.items():
        w,sgn=reg(s,p);key=(w,k)
        out[key]=out.get(key,0)+sgn*v
target={('',0):9*scale}
for i in range(3):
    target[chr(65+i),0]=3*scale//4
    target[chr(65+i)+chr(97+i),1]=-scale
    target[chr(65+(i+1)%3)+chr(97+i),1]=scale
if {k:v for k,v in out.items() if v}!=target:raise ArithmeticError('polynomial mismatch')
print('PASS: 24 strict leading principal minors by integer Bareiss; independent integer group-algebra expansion.')
