#!/usr/bin/env python3
"""Untrusted deterministic producer for an explicit classical Schinzel H family.

Constructs an affine *one-variable* family of 197 quadratic norm forms,
whose product has no fixed prime divisor. The independent verifier does not
import this file. NO ACTUAL CLAIM of prime values is made here.
"""
import json
from math import isqrt
from pathlib import Path

HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]/'sqrt-minus-two-universal-sieve-barrier'/'code'
S=[tuple(z) for z in json.loads((BASE/'connected_shape.json').read_text())]
OLD=json.loads((BASE/'local_shifts.json').read_text())


def prime(n):
    return n>=2 and all(n%d for d in range(2,isqrt(n)+1))


def valid_shift(p,u,v):
    return all(((a+u)**2+2*(b+v)**2)%p != 0 for a,b in S)


if __name__=='__main__':
    assert len(S)==197
    x=y=0
    modulus=1
    pairs=[]
    for p in range(2,2*len(S)+1):
        if not prime(p):continue
        if str(p) in OLD:
            u,v=OLD[str(p)]
        else:
            u=v=None
            for test_x in range(p):
                for test_y in range(p):
                    if valid_shift(p,test_x,test_y):
                        u,v=test_x,test_y
                        break
                if u is not None:break
        if u is None or not valid_shift(p,u,v):
            raise RuntimeError(f'nonadmissible pattern at p={p}')
        pairs.append((p,u,v))
        inv=pow(modulus,-1,p)
        x+=modulus*(((u-x)*inv)%p)
        y+=modulus*(((v-y)*inv)%p)
        modulus*=p
    y+=modulus     # Makes every vertical shift strictly positive.
    cert={
        'source_shape':'../sqrt-minus-two-universal-sieve-barrier/code/connected_shape.json',
        'number_of_forms':len(S),
        'small_prime_cutoff':2*len(S),
        'modulus':str(modulus),
        'horizontal_offset':str(x),
        'vertical_offset':str(y),
        'prime_local_shifts':[[p,u,v] for p,u,v in pairs],
    }
    path=HERE/'schinzel_affine_family.json'
    path.write_text(json.dumps(cert,sort_keys=True,separators=(',',':'))+'\n')
    print('family built, forms',len(S),'primes used',len(pairs),
          'modulus decimal digits',len(str(modulus)),
          'offsets decimal digits',len(str(x)),len(str(y)))
