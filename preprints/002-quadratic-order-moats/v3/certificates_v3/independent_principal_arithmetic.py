"""Bounded exact arithmetic stress test, independent of either checker.
Run without -O. Checks supplement the membership and period proof.
"""
from math import gcd
import json

if not __debug__:
    raise RuntimeError('Run this test without Python optimization flags')

results=[]
for u,v in [(0,-1),(0,2),(1,1),(1,-1),(0,8)]:
    count=0
    for a in range(-3,4):
        for b in range(-3,4):
            D=abs(a*a+u*a*b-v*b*b)
            if not 2<=D<=50:
                continue
            image={((a*x+v*b*y)%D,(b*x+(a+u*b)*y)%D)
                   for x in range(D) for y in range(D)}
            congruences={(x,y) for x in range(D) for y in range(D)
                         if ((a+u*b)*x-v*b*y)%D==0 and (-b*x+a*y)%D==0}
            assert image==congruences
            period=next(t for t in range(1,D+1)
                        if (t%D,0) in image and (0,t%D) in image)
            assert period==D//gcd(a,b)
            count+=1
    results.append({'u':u,'v':v,'tested_generators':count})
assert sum(r['tested_generators'] for r in results)==184
print(json.dumps({'total':184,'models':results},indent=2))
