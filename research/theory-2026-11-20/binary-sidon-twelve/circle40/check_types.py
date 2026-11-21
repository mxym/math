"""Additional exact affine-type comparison; use published sections.txt."""
from pathlib import Path
from collections import Counter
rows = [tuple(map(int,line.split())) for line in
        Path(__file__).with_name("sections.txt").read_text().splitlines()]
if len(rows) != 4 or [len(x) for x in rows] != [40,26,40,26]:
    raise ValueError("unexpected section file")
e = []
for a in rows[::2]:
    e.append(tuple(sorted(Counter(abs(sum(1-2*((h&x).bit_count()%2)
                 for x in a)) for h in range(1,2048)).items())))
want = [
    ((0,222),(2,437),(4,423),(6,351),(8,273),(10,205),(12,105),(14,31)),
    ((0,252),(2,432),(4,378),(6,360),(8,291),(10,200),(12,102),(14,32)),
]
if e != want:
    raise ValueError(e)
print("PASS: zero-Walsh counts 222 and 252 distinguish the two affine section types.")

# Check the full affine stabilizer independently in an absolute polynomial basis.
powers=[]
x=1
for i in range(4095):
    powers.append(x)
    x <<= 1
    if x & 4096:
        x ^= 0x1053
if x != 1 or len(set(powers)) != 4095:
    raise ValueError("field generator")
S = [0] + powers[::63]
C = S[1:]
H = [h for h in range(1,4096)
     if sum(1-2*((h&x).bit_count()%2) for x in S) == 14]
inc=[sum(1<<i for i,h in enumerate(H) if not ((h&x).bit_count()%2))
     for x in C]
if len(H)!=390 or any(u.bit_count()!=234 for u in inc):
    raise ValueError("characteristic family")
n=len(C)
W=[[(a&b).bit_count() for b in inc] for a in inc]
nodes=0

def stabilize(source,dest):
    global nodes
    nodes+=1
    if len(source)==n:
        return 1
    targets=set(range(n))-set(dest)
    chosen=None
    for v in set(range(n))-set(source):
        valid=[w for w in sorted(targets) if
               all(W[v][a]==W[w][b] for a,b in zip(source,dest))]
        if not valid:
            return 0
        if chosen is None or len(valid)<len(chosen[1]):
            chosen=(v,valid)
    v, valid=chosen
    return sum(stabilize(source+[v],dest+[w]) for w in valid)

if stabilize([0],[0]) != 12:
    raise ValueError("unexpected colored graph stabilizer")
print("PASS: weighted norm-circle point stabilizer has order 12;",nodes,"nodes.")
