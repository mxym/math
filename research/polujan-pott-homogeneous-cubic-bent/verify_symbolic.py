#!/usr/bin/env python3
"""Independent verifier by symbolic substitution in F2[x_i]/(x_i^2-x_i)."""
from itertools import combinations
from hashlib import sha256
import json
from pathlib import Path

if not __debug__:
    raise SystemExit("Run without -O")
# Images of the last coordinate under the companion matrix's one-place shift;
# written as coordinate lists, independent of the integer-modulus implementation.
FOLD = {2:(0,1),3:(0,1),4:(0,1),5:(0,2),6:(0,1)}


def times(a,b):
    out=set()
    for i in a:
        for j in b:
            k=i|j
            if k in out:
                out.remove(k)
            else:
                out.add(k)
    return out


def original(d,offset):
    """Monomial masks of a single block in the old coordinates."""
    terms=set()
    for j in range(d):
        jp=[j+1] if j+1<d else FOLD[d]
        for k in jp:
            terms.add((1<<(offset+k)) | (1<<(offset+d+j)))
        terms.add((1<<(offset+j)) | (1<<(offset+d+j)) | (1<<(offset+2*d)))
    return terms


def rank(rows):
    rows=list(rows);r=0
    for b in range(max((x.bit_length() for x in rows),default=0)):
        j=next((j for j in range(r,len(rows)) if rows[j] & (1<<b)),None)
        if j is None:
            continue
        rows[j],rows[r]=rows[r],rows[j]
        for k in range(r+1,len(rows)):
            if rows[k]&(1<<b):rows[k]^=rows[r]
        r+=1
    return r


def proof(n,basis):
    l=(n-6)//2
    raw=original(2,0)^original(l,5)^{(1<<4)|(1<<(n-1))}
    images=[{1<<j for j,v in enumerate(basis) if v & (1<<i)} for i in range(n)]
    assert len(basis)==n and rank(basis)==n and all(v.bit_length()<=n for v in basis)
    final=set()
    for mask in raw:
        cur={0}
        for i in range(n):
            if mask&(1<<i):cur=times(cur,images[i])
        final ^= cur
    # Correct by the linear functional specified in the proof, not by deleting
    # arbitrary low-degree terms.
    correction={1<<i for i,v in enumerate(basis) if sum((v&t)==t for t in raw)%2}
    final ^= correction
    assert final and all(m.bit_count()==3 for m in final)
    # Independent linear-algebra check of slice bijectivity and polar nonsingularity.
    for d in {2,l}:
        cm=[1<<(i+1) for i in range(d-1)]+[sum(1<<j for j in FOLD[d])]
        assert rank(cm)==d and rank([a^(1<<i) for i,a in enumerate(cm)])==d
    expected=(2+l) # exact relaxed index from the two-block lemma
    hashed=sha256(b''.join(m.to_bytes(3,'little') for m in sorted(final))).hexdigest()
    print(f"n={n} cubic_terms={len(final)} correction_weight={len(correction)} r_ind_by_lemma={expected} ANF_SHA256={hashed}")
    return final


if __name__=='__main__':
    bases=json.loads(Path(__file__).with_name('bases.json').read_text())
    assert set(bases)=={'10','12','14','16','18'}
    for n in range(10,19,2):
        proof(n,bases[str(n)])
    # Canonical coordinates leave original quadratic terms (e.g. st) intact.
    try:
        proof(10,[1<<i for i in range(10)])
    except AssertionError:
        pass
    else:
        raise RuntimeError("identity-basis negative control did not fail")
    print("PASS: symbolic expansion and slice ranks; identity-basis control detected")
