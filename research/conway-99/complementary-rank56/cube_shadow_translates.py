"""Exact small translate count for one distinct oriented complementary shadow."""
from collections import Counter

def polynomial(s):
    # In degree <=5, complete the square as in the proof.
    terms = Counter(v*v + v*w + 3*w*w + s*w
                    for w in range(-1,2) for v in range(-3,4))
    assert min(terms) == 0
    return [terms[j] for j in range(6)]

zero, plus, minus = (polynomial(s) for s in (0,1,-1))
assert zero == [1,2,0,4,2,4]
assert plus == minus == [1,2,2,0,6,0]
gain = [zero[j] + sum(m*plus[j-k] for k,m in [(1,56),(2,86),(3,56)] if j>=k)
        for j in range(6)]
assert gain == [1,58,198,344,286,452]
print('Exact additional vectors per oriented shadow, shells 4 to 9:', gain)
