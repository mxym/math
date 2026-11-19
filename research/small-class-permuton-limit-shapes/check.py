"""Exact finite sanity checks for segment-rank and lifted-buffer arithmetic (not a proof)."""
from itertools import product, combinations
from collections import Counter
from fractions import Fraction as F

def expect(test, explanation):
    if not test:
        raise ArithmeticError(explanation)

# The single # is a bounded crossing. Each phase has two equally likely letters.
# Output order 1 = word order. Order 2 groups an FO local bit (previous letter is a/c),
# sorts phase within each group, then traverses the group forwards or backwards.
# The first input letter chooses the global reversal switch.
word_cases = 0
point_cases = 0
for n in range(1, 9):
    for j in range(n+1):
        for w in product((0,1),repeat=n):
            phase = [0]*j+[1]*(n-j)
            bit = [int(i>0 and phase[i]==phase[i-1] and w[i-1]==0) for i in range(n)]
            ctx = w[0]
            def key(i):
                g=bit[i]
                return (g^ctx,phase[i], i if g==0 else -i)
            literal=sorted(range(n),key=key)
            freqs=Counter(zip(phase,bit))
            prefix=Counter()
            for i in range(n):
                r=0
                for (ph,b),q in freqs.items():
                    bins=(b^ctx,ph)
                    me=(bit[i]^ctx,phase[i])
                    if bins<me: r+=q
                    elif bins==me:
                        before=prefix[ph,b]
                        r+=before if b==0 else q-before-1
                expect(literal[r]==i,'pair-table rank mismatch')
                prefix[phase[i],bit[i]]+=1
                point_cases+=1
            word_cases+=1
# Exact route law for two full binary phases: all n+1 crossing placements equal.
for n in range(1,80):
    expect(sum(F(j,n*(n+1)) for j in range(n+1))==F(1,2),'mean split')
    expect(sum(F(j*j,n*n*(n+1)) for j in range(n+1))==F(2*n+1,6*n),'second moment')

# Unmarked monoid C3 x {1,0}, letters have phase +1 and b kills the bit.
# B=bbb has phase zero; only occurrences starting in recorder phase zero count.
# Marked actions optionally reflect the group so order matters.
def ev(w,marks=(), start=0):
    x,h=start,1
    for i,a in enumerate(w):
        if i in marks:
            x=((2*x+(marks.index(i)+1))%3)
        else:
            x=(x+1)%3
        if a=='b':h=0
    return x,h
gaps=bad=two=0
for n in range(6,14):
    for w in product('ab',repeat=n):
        occ=[i for i in range(n-2) if w[i:i+3]==('b','b','b')]
        for i,j in combinations(occ,2):
            if j<i+3:continue
            y=ev(w[i:j+3])
            if i%3==j%3==0:
                expect(y==(0,0),'genuine lifted sandwich did not erase')
                gaps+=1
            elif y!=(0,0):bad+=1
        # Independent literal replacement: group at either end preserved for
        # every starting input and every placement of the two flags outside the gap.
        lifted=[i for i in occ if i%3==0]
        if len(lifted)>=2:
            i,j=lifted[0],lifted[-1]
            exterior=[p for p in range(n) if p<i or p>=j+3]
            for l,r in combinations(exterior,2):
                new=w[:i]+tuple('bbb')+w[j+3:]
                def shift(p):return p if p<i else p-(j-i)
                for x in range(3):
                    expect(ev(w,(l,r),x)==ev(new,(shift(l),shift(r)),x),'marked exterior change')
                two+=1
expect(gaps>0 and bad>0 and two>0,'vacuous lift or counterexample test')
print('pair table:',word_cases,'words/phase choices;',point_cases,'literal position ranks')
print('two-phase split first and second moments exact for n=1..79')
print('group-lift:',gaps,'erased lifted sandwiches;',bad,'unlifted nonerasing sandwiches;',two,'two-flag exterior replacements')
print('PASS')
