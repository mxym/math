#!/usr/bin/env python3
"""Check the exact real-axis restrictions in FactorSqrtMinusTwoAxialPrimeGap.md."""
from argparse import ArgumentParser
from fractions import Fraction
from hashlib import sha256
from math import isqrt, prod
import json

OLD = (2, 3, 5, 11, 17, 19, 41, 43, 59, 67)
Q = 742840526010
H = 455654487618
A0 = 389
FIRST = (7, 73, 83, 89, 97, 107, 113)
MIDDLE = (131, 137)
MASKED = (139, 179, 163, 193, 211, 227, 233, 251, 241)
RADIUS = 10**33
SHAPE_TEXT = "[[369, -29], [369, -28], [369, 28], [369, 29], [371, -30], [371, -27], [371, 27], [371, 30], [373, -30], [373, -27], [373, -21], [373, 21], [373, 27], [373, 30], [375, -34], [375, -32], [375, -31], [375, -28], [375, -20], [375, -19], [375, -17], [375, -16], [375, 16], [375, 17], [375, 19], [375, 20], [375, 28], [375, 31], [375, 32], [375, 34], [377, -33], [377, -27], [377, -18], [377, 18], [377, 27], [377, 33], [379, -33], [379, -30], [379, -27], [379, -21], [379, -18], [379, 18], [379, 21], [379, 27], [379, 30], [379, 33], [381, -34], [381, -32], [381, -31], [381, -26], [381, -25], [381, -23], [381, -22], [381, -20], [381, -19], [381, -14], [381, -13], [381, 13], [381, 14], [381, 19], [381, 20], [381, 22], [381, 23], [381, 25], [381, 26], [381, 31], [381, 32], [381, 34], [383, -33], [383, -27], [383, -24], [383, -21], [383, -18], [383, -15], [383, -12], [383, 12], [383, 15], [383, 18], [383, 21], [383, 24], [383, 27], [383, 33], [385, -27], [385, -18], [385, -15], [385, -12], [385, 12], [385, 15], [385, 18], [385, 27], [387, -26], [387, -17], [387, -16], [387, -13], [387, -11], [387, -2], [387, -1], [387, 1], [387, 2], [387, 11], [387, 13], [387, 16], [387, 17], [387, 26], [389, -18], [389, -12], [389, -3], [389, 0], [389, 3], [389, 12], [389, 18], [391, -18], [391, -15], [391, -6], [391, -3], [391, 3], [391, 6], [391, 15], [391, 18], [393, -22], [393, -20], [393, -19], [393, -17], [393, -16], [393, -14], [393, -13], [393, -5], [393, -4], [393, 4], [393, 5], [393, 13], [393, 14], [393, 16], [393, 17], [393, 19], [393, 20], [393, 22], [395, -21], [395, -12], [395, -6], [395, 6], [395, 12], [395, 21], [397, -12], [397, -6], [397, -3], [397, 3], [397, 6], [397, 12], [399, -14], [399, -13], [399, -5], [399, -4], [399, -2], [399, 2], [399, 4], [399, 5], [399, 13], [399, 14], [401, -12], [401, -3], [401, 3], [401, 12], [403, -12], [403, -3], [403, 3], [403, 12], [405, -11], [405, -10], [405, -5], [405, -4], [405, 4], [405, 5], [405, 10], [405, 11], [407, -9], [407, -6], [407, 6], [407, 9], [409, -9], [409, -6], [409, 6], [409, 9], [411, -13], [411, -11], [411, -10], [411, -8], [411, -7], [411, 7], [411, 8], [411, 10], [411, 11], [411, 13], [413, -12], [413, -6], [413, 6], [413, 12]]"
SHAPE = {tuple(z) for z in json.loads(SHAPE_TEXT)}
POS = sorted((a,b) for a,b in SHAPE if b>0)
STEPS = [(x,y) for x in range(-2,3) for y in range(-1,2) if x or y]


def check(condition, desc):
    if not condition:
        raise ValueError(desc)


def primes(n):
    return [p for p in range(2,n+1) if all(p%d for d in range(2,isqrt(p)+1))]


def literal_shape():
    check(sha256(SHAPE_TEXT.encode()).hexdigest() ==
          "b8036dcfa082e1329126041d8c7992139da6121e4ebf71599458619e7af93df0", "input SHA")
    check(len(SHAPE)==197 and len(POS)==98 and
          SHAPE == {(A0,0)} | set(POS) | {(a,-b) for a,b in POS}, "mirror symmetry")
    check((min(a for a,b in SHAPE),max(a for a,b in SHAPE),max(b for a,b in SHAPE))==
          (369,413,34), "coordinate extents")
    queue = [(A0,0)]
    seen = set(queue)
    for x,y in queue:
        for dx,dy in STEPS:
            z = x+dx,y+dy
            if z in SHAPE and z not in seen:
                queue.append(z)
                seen.add(z)
    check(seen==SHAPE, "not connected")
    check(prod(OLD)==Q, "period")
    check(min((a+H,b) for a,b in SHAPE)==(455654487987,-29), "prior anchor")
    def sift(a,b):
        return all(((a+H)**2+2*b*b)%p for p in OLD)
    for a,b in SHAPE:
        check(sift(a,b), (a,b))
        for dx,dy in STEPS:
            x,y=a+dx,b+dy
            check((x,y) in SHAPE or not sift(x,y), ("open boundary",x,y))


def horizontal_rows(p):
    # Norm zeroes computed directly, treating the real-axis norm via
    # its linear prime rather than its square.
    literal = {r for r in range(p) if (r+A0)%p and
               all(((r+a)**2+2*b*b)%p for a,b in POS)}
    roots = [r for r in range(p) if (r*r+2)%p==0]
    forbidden = {(-A0)%p}
    for a,b in POS:
        if b%p==0:
            forbidden.add((-a)%p)
        else:
            forbidden.update((t*b-a)%p for t in roots)
    via_roots = set(range(p))-forbidden
    check(literal==via_roots and bool(literal), ("local row",p))
    return literal


def at_k(t):
    return H+Q*t


def inert_ok(h):
    return abs(h+A0)%8 in (5,7)


def distance(t):
    h = at_k(t)
    check(h+369>0 or h+413<0, ("axis sign",t))
    return h+369 if h>0 else -h-413


def by_k(rows):
    return {
        p:{((u-H)*pow(Q,-1,p))%p for u in us}
        for p,us in rows.items() if Q%p
    }


def lift(residues,m,rows,p):
    inv=pow(m,-1,p)
    return [r+m*((t-r)*inv%p) for r in residues for t in sorted(rows[p])],m*p


def closest_small(rows):
    K=by_k({p:s for p,s in rows.items() if p<=197})
    residues,m=[0],1
    for p in FIRST:
        residues,m=lift(residues,m,K,p)
    check((len(residues),m)==(28350,4427136928039),"small CRT size")
    rest=sorted((p for p in K if p not in FIRST),key=lambda p:Fraction(len(K[p]),p))
    found=[]
    tested=0
    for r in residues:
        for k in (r-m,r):
            if inert_ok(at_k(k)):
                tested+=1
                if all(k%p in K[p] for p in rest):
                    found.append(k)
    check(tested==28525 and found==[4049216723139], ("nearest admissible",found,tested))
    k,=found
    d=distance(k)
    check(min(distance(-m-1),distance(m))>d,"unsearched tail could improve")
    check(d==3007922280545518952833377, ("wrong distance",d))
    print("through 197: first congruence candidate", k, d, "| tested",tested,flush=True)


def masked_exclusion(rows, radius):
    K = by_k(rows)
    prefixes,m=[0],1
    for p in (*FIRST,MIDDLE[0]):
        prefixes,m=lift(prefixes,m,K,p)
    p=MIDDLE[1]
    inv=pow(m,-1,p)
    additions=tuple(tuple(sorted((t-r)*inv%p for t in K[p])) for r in range(p))
    M=m*p
    check((len(prefixes),m,M)==(595350,579954937573109,79453826447515933),
          "large CRT seed")
    # ceil((-RADIUS-H-413)/Q), not floor of the negative numerator.
    lo=-((radius+H+413)//Q)
    hi=(radius-H-369)//Q
    j0=lo//M
    j1=hi//M
    num=j1-j0+1

    masks=[]
    for p in MASKED:
        pat=[sum(1<<i for i in range(z,num,p)) for z in range(p)]
        inv=pow(M,-1,p)
        y0=M*j0%p
        vals=tuple(sum(pat[(t-r-y0)*inv%p] for t in K[p]) for r in range(p))
        # Direct test for every position and several residues, including both
        # boundaries of the bit interval. The math justification is modular.
        for r in (0,p//2,p-1):
            check(all(bool((vals[r]>>i)&1)==((r+M*(j0+i))%p in K[p])
                      for i in range(num)), ("invalid masks",p,r))
        masks.append((p,vals))
    remaining=sorted((p for p in K if p not in (*FIRST,*MIDDLE,*MASKED)),
                     key=lambda p:Fraction(len(K[p]),p))
    p0,val0=masks[0]
    tail=masks[1:]
    congruences=visited=inside=oriented=survivors=0
    for r in prefixes:
        for v in additions[r%MIDDLE[1]]:
            k0=r+m*v
            congruences+=1
            bits=val0[k0%p0]
            for p,vals in tail:
                bits &= vals[k0%p]
                if not bits:
                    break
            while bits:
                bit=bits & -bits
                k=k0+M*(j0+bit.bit_length()-1)
                bits ^= bit
                visited+=1
                if not lo<=k<=hi:
                    continue
                inside+=1
                if not inert_ok(at_k(k)):
                    continue
                oriented+=1
                if all(k%p in K[p] for p in remaining):
                    survivors+=1
    result=(congruences,visited,inside,oriented,survivors)
    print("through 997 on the real axis:",(lo,hi),(j0,j1),result,flush=True)
    expected={10**29:(12502350,1146,978,489,0),
              10**33:(12502350,9230230,9230213,4617134,0)}[radius]
    check(result==expected, ("wrong exact finite range result",result))
    check(survivors==0, ("surviving candidate",survivors))


def main():
    parser=ArgumentParser()
    parser.add_argument('--short',action='store_true',help='replay the smaller 10^29 window')
    args=parser.parse_args()
    literal_shape()
    rows={p:horizontal_rows(p) for p in primes(997)}
    check(all(H%p in rows[p] for p in OLD), "base residues")
    check([(p,len(rows[p])) for p in (7,73,83,89,97,107,113,131,137)]==
          [(7,1),(73,1),(83,3),(89,7),(97,9),(107,10),(113,15),(131,21),(137,21)],
          "CRT row sizes")
    closest_small(rows)
    masked_exclusion(rows,10**29 if args.short else RADIUS)
    print("PASS")


if __name__=="__main__":
    main()
