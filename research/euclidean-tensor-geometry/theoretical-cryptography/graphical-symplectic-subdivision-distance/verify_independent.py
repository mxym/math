"""Log-table GF(8); explicit word fibers, literal syndromes, full basis census."""
from collections import Counter, defaultdict
from itertools import combinations, product

# Powers of alpha, in the public 1,alpha,alpha^2 coordinate encoding.
POWER = (1,2,4,3,6,7,5)
LOG = {a:i for i,a in enumerate(POWER)}
def pm(a,b):
    return POWER[(LOG[a]+LOG[b])%7] if a and b else 0
def inv(a):
    return POWER[-LOG[a]%7]

def xdot(a,b):
    x = 0
    for i,j in zip(a,b):
        x ^= pm(i,j)
    return x

def linear(rows):
    for c in product(range(8), repeat=len(rows)):
        yield tuple(xdot(c,row) for row in zip(*rows))

def small_word(a,b,c,d):
    # Port first, then the three physical sites, ordered (x,z) per site.
    return (b^c^d,a), ((b,a^pm(4,c)^pm(2,d)),
                       (c,a^pm(4,b)^d),
                       (d,a^pm(2,b)^c))

fibers = defaultdict(list)
inverse = {}
for abc in product(range(8), repeat=4):
    label, word = small_word(*abc)
    assert word not in inverse
    inverse[word] = label
    fibers[label].append(word)
assert len(fibers)==64 and all(len(l)==64 for l in fibers.values())

def wt(w):
    return sum(x != (0,0) for x in w)

for omitted in range(3):
    supported = Counter(l for l,words in fibers.items() for w in words if w[omitted]==(0,0))
    assert len(supported)==64 and set(supported.values())=={1}
assert all(min(map(wt,words))==2 for l,words in fibers.items() if l!=(0,0))
assert Counter(map(wt,fibers[0,0]))=={0:1,3:63}
print("independent: 4096 module words; every one of 63 nonzero port labels has distance 2 on any two sites")

# Build the base from a differently rooted incidence matrix.
E = list(combinations(range(4),2))
flow = (1,2,3,3,2,1)
H = [[(int(u==i or v==i),flow[j] if u==i or v==i else 0)
      for j,(u,v) in enumerate(E)] for i in (0,1,2)]
H.append([(0,z) for z in flow])
def syndromes(h):
    return [[sum((pm(a,z)^pm(b,x))<<(3*j) for j,r in enumerate(h) for x,z in [r[i]])
             for a,b in product(range(8),repeat=2)] for i in range(len(h[0]))]
def muladd(a,r,b,s):
    return tuple(tuple(pm(a,v)^pm(b,w) for v,w in zip(x,y)) for x,y in zip(r,s))

r0 = next(w for w in fibers[0,0] if wt(w))
r0line = {muladd(a,r0,0,r0) for a in range(8)}
r1 = next(w for w in fibers[0,0] if w not in r0line)
basis = (r0,r1)
liftx,liftz = (min(fibers[p]) for p in ((1,0),(0,1)))
zero = ((0,0),)*3

def concatenate(outer):
    local = [tuple(p for j in range(6) for p in (b if i==j else zero))
             for i in range(6) for b in basis]
    lifted = [tuple(p for a,b in r for p in muladd(a,liftx,b,liftz)) for r in outer]
    return local+lifted

C = concatenate(H)
S6, S18 = syndromes(H), syndromes(C)
def syndrome(S,w):
    v=0
    for i,(a,b) in enumerate(w):
        v ^= S[i][8*a+b]
    return v
assert all(syndrome(S6,r)==0 for r in H)
assert all(syndrome(S18,r)==0 for r in C)
base_stabilizers = set(linear([tuple(a for pair in row for a in pair) for row in H]))
assert len(base_stabilizers)==8**4

# Compare the independently chosen root/kernel basis/logical representatives
# against the polynomial-basis checker's construction by actual row reduction.
def pivots(vectors, length):
    piv={}
    for r in vectors:
        r=list(r)
        for j in range(length):
            if not r[j]:
                continue
            if j in piv:
                r=[a^pm(r[j],b) for a,b in zip(r,piv[j])]
            else:
                piv[j]=tuple(pm(inv(r[j]),x) for x in r)
                break
    return piv
def unpack(h):
    return [tuple(a for pair in r for a in pair) for r in h]
def in_span(r,piv):
    r=list(r)
    for j in range(len(r)):
        if r[j]:
            if j not in piv:
                return False
            r=[a^pm(r[j],b) for a,b in zip(r,piv[j])]
    return True

oldroot = [[(int(u==i or v==i),flow[j] if u==i or v==i else 0)
            for j,(u,v) in enumerate(E)] for i in (1,2,3)] + [H[-1]]
ref_ker = [small_word(0,1,1,0)[1],small_word(0,1,0,1)[1]]
ref_x,ref_z = small_word(0,1,0,0)[1],small_word(1,0,0,0)[1]
ref = [tuple(p for j in range(6) for p in (b if i==j else zero))
       for i in range(6) for b in ref_ker]
ref += [tuple(p for a,b in r for p in muladd(a,ref_x,b,ref_z)) for r in oldroot]
piv = pivots(unpack(C),36)
assert len(piv)==16 and len(pivots(unpack(ref),36))==16
assert all(in_span(row,piv) for row in unpack(ref))

# Whole basis census. For every choice of missing sites, compute local-pivot
# reductions from actual columns. Group by those outputs and graph-sign parity;
# weights of the groups count every original signing with multiplicity.
def local_column(i,j,s):
    return tuple(r[3*i+j][s] for r in (C[2*i], C[2*i+1], *C[12:]))
def reduce_block(i,tags):
    rows = [local_column(i,j,s-1) for j,s in enumerate(tags) if s]
    lead, trailing = {}, []
    for row in rows:
        for j in (0,1):
            if not row[j]:
                continue
            if j not in lead:
                lead[j]=tuple(pm(inv(row[j]),x) for x in row)
                break
            row=tuple(x^pm(row[j],y) for x,y in zip(row,lead[j]))
        else:
            tail=row[2:]
            if not any(tail):
                trailing.append(tail)
            else:
                trailing.append(tuple(pm(inv(next(x for x in tail if x)),y) for y in tail))
    return len(lead),tuple(trailing)

def signed_forest_rule(tags):
    # Union-find with parity to the root, and at most one odd cycle per root.
    roots=list(range(16))
    parity=[0]*16
    used=[0]*16
    def find(i):
        x=0
        while roots[i]!=i:
            x^=parity[i]
            i=roots[i]
        return i,x
    for (a,b),s in zip(subedges,tags):
        if not s:
            continue
        u,x=find(a)
        v,y=find(b)
        p=x^y^(s-1)
        if u==v:
            if used[u] or not p:
                return False
            used[u]=1
        else:
            if used[u]+used[v]>1:
                return False
            roots[u]=v
            parity[u]=p
            used[v]+=used[u]
    return True

subedges=[]
for j,(a,b) in enumerate(E):
    c=4+2*j
    subedges.extend(((a,c),(c,c+1),(c+1,b)))
tables={}
for i in range(6):
    for mask in product(range(2),repeat=3):
        tab={}
        for t in product(*[(1,2) if m else (0,) for m in mask]):
            rank, tail=reduce_block(i,t)
            # The omitted signs can affect no cycle. If it is complete, the
            # parity does affect Chow's test, so retain it in the group key.
            par=sum(s==2 for s in t)%2 if all(mask) else None
            key=(rank,tail,par)
            if key in tab:
                tab[key]=(tab[key][0],tab[key][1]+1)
            else:
                tab[key]=(t,1)
        tables[i,mask]=[(r,tail,t,k) for (r,tail,_),(t,k) in tab.items()]
census = bases = groups = 0
for holes in combinations(range(18),2):
    key=[(i,tuple(int(3*i+j not in holes) for j in range(3))) for i in range(6)]
    for blocks in product(*(tables[k] for k in key)):
        r=sum(b[0] for b in blocks)
        tails=[v for b in blocks for v in b[1]]
        t=tuple(s for b in blocks for s in b[2])
        mass=1
        for b in blocks:
            mass*=b[3]
        actual=r+len(pivots(tails,4))==16
        assert actual==signed_forest_rule(t)
        groups+=1
        census+=mass
        bases+=mass*actual
assert (census,bases)==(10027008,4423680)
print(f"independent: same 16-dimensional concatenated row space; {groups} exact groups cover all {census} size-16 admissible sets, {bases} bases")

# Direct enumeration of low-weight zero syndromes. A genuine weight-three
# stabilizer is not erroneously counted in the distance.
def small_syndromes(S):
    singles=defaultdict(list)
    counts=[0]*4
    triples=set()
    for i,row in enumerate(S):
        for a,v in enumerate(row[1:],1):
            singles[v].append((i,a))
            counts[1]+=v==0
    for i,j in combinations(range(len(S)),2):
        for a,x in enumerate(S[i][1:],1):
            for b,y in enumerate(S[j][1:],1):
                w=x^y
                counts[2]+=w==0
                if w in singles:
                    for k,c in singles[w]:
                        # Count each triple once, ordered by its site labels.
                        if k>j:
                            triples.add(((i,a),(j,b),(k,c)))
    counts[3]=len(triples)
    return counts,triples

def word(n,small):
    w=[(0,0)]*n
    for i,a in small:
        w[i]=divmod(a,8)
    return tuple(w)
def bound_test(w):
    assert syndrome(S18,w)==0
    outer=tuple(inverse[w[i:i+3]] for i in range(0,18,3))
    flat=tuple(p for x in outer for p in x)
    return flat in base_stabilizers

counts, triples = small_syndromes(S18)
assert counts == [0,0,0,378]
assert all(bound_test(word(18,t)) and in_span(unpack([word(18,t)])[0],piv)
           for t in triples)

two = []
for i,j in combinations(range(6),2):
    for a,x in enumerate(S6[i][1:],1):
        for b,y in enumerate(S6[j][1:],1):
            if x==y:
                w=word(6,((i,a),(j,b)))
                if tuple(x for p in w for x in p) not in base_stabilizers:
                    two.append(w)
assert len(two)==105 and all(0 not in r[1:] for r in S6)
outer=two[0]
new=tuple(p for l in outer for p in min(fibers[l],key=wt))
assert wt(new)==4 and not bound_test(new) and not in_span(unpack([new])[0],piv)
print("independent: direct syndromes give 105 base weight-2 logical words, no subdivided weight-1/2 words, 378 weight-3 stabilizers and a weight-4 logical witness")
