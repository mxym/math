#!/usr/bin/env python3
"""Complete (not length-bounded) 18-state relation and product-language closure."""
if not __debug__:
    raise SystemExit("Use ordinary Python, not python -O: proof assertions must run")
from functools import lru_cache


def main():
    trans=((0,1),(0,2),(1,2)) # prior A/B/C row, low-to-high digit column
    def ix(s,v,c):return 2*(3*s+v)+c
    moves=[]
    for g in range(2):
        for beta in range(2):
            z=[]
            for p in range(2):
                for s in range(3):
                    for v in range(3):
                        for c in range(2):
                            bits=0
                            for a in range(2):
                                d=a^g^c; carry=(c+a+d)//2
                                h=beta*((s==2 and a)^(v==2 and d))
                                j=ix(trans[s][a],trans[v][d],carry)
                                bits|=1<<(j+18*(p^h))
                            z.append(bits)
            moves.append(z)
    @lru_cache(None)
    def extend(row,z):
        out=0
        while row:
            bit=row&-row; row^=bit; out|=moves[z][bit.bit_length()-1]
        return out
    identity=tuple(1<<j for j in range(18)); maps=[identity]; index={identity:0}; delta=[]
    for m in maps:
        nxt=[]
        for z in range(4):
            other=tuple(extend(row,z) for row in m)
            if other not in index:index[other]=len(maps);maps.append(other)
            nxt.append(index[other])
        delta.append(nxt)
    oddclosed=[any(row>>(18+j)&1 for j,row in enumerate(m)) for m in maps]
    allowed={(3,1),(1,0),(0,2),(0,3),(2,0)}
    # no beta ones so far, beta parity, length parity, capped length, first,
    # last, all adjacent pairs legal, capped number of letters 1.
    empty=(True,0,0,0,-1,-1,True,0)
    firststate=(0,empty); states=[firststate]; seen={firststate}; relevant=accept=0
    for mid,w in states:
        zero,p,odd,length,f,l,ok,ones=w
        if p==0 and odd and length==3:
            relevant+=1; good=not oddclosed[mid]; accept+=good
            expect=zero or (ones==1 and ok and (l,f) in allowed)
            assert good==expect,('language mismatch',mid,w,good,expect)
        for z in range(4):
            u=(zero and not z%2,p^(z%2),odd^1,min(3,length+1),z if f<0 else f,z,
               ok and (l<0 or (l,z) in allowed),min(2,ones+(z==1)))
            t=delta[mid][z],u
            if t not in seen:seen.add(t);states.append(t)
    print(f'relation monoid={len(maps)} product={len(states)} eligible={relevant} accepting={accept}')
    assert (len(maps),len(states),relevant,accept)==(4917,25906,6498,34)
    # Negative control: deleting a required target edge rejects the known n=5 word,
    # whereas the independently calculated relation still accepts it.
    word=(1,0,2,0,3); ctl=0
    for z in word:ctl=delta[ctl][z]
    cyc=set(zip(word,word[1:]+word[:1])); assert not oddclosed[ctl]
    assert cyc<=allowed and not cyc<=(allowed-{(2,0)})
    print('PASS: no language discrepancy at any eligible length; damaged-target negative control detected')

if __name__=='__main__':main()
