from itertools import product
from fractions import Fraction as F


def require(flag, detail):
    if not flag:
        raise ArithmeticError(detail)


boxes = [
    ([(".279", ".281")], [(".289", ".291")], [(".459", ".461")]),
    ([(".289", ".291")], [(".309", ".311")],
       [(".209", ".211"), (".229", ".231")]),
    ([(".137", ".139"), (".149", ".151")],
      [(".155", ".157"), (".169", ".171")],
      [(".197", ".199"), (".219", ".221")]),
    ([(".1768", ".1772"), (".2098", ".2102")],
      [(".1798", ".1802"), (".2118", ".2122")],
      [(".1948", ".1952"), (".1998", ".2002")]),
]
total = 0
for k, (A, B, Q) in enumerate(boxes, 1):
    all_bands = [tuple(map(F, band)) for band in A+B+Q]
    bands = sorted(all_bands)
    require(all(b < c for (a,b),(c,d) in zip(bands, bands[1:])), "distinct")
    minimum = F(2)
    maximum = F(0)
    tail_max = F(0)
    for pt in product(*all_bands):
        a = sum(pt[:len(A)])
        b = sum(pt[len(A):len(A)+len(B)])
        remaining = pt[len(A)+len(B):]
        q = sum(remaining)
        expo = (a+b+3*q)/2+F(".0075")
        tail = a+b+q-1+F(".015")
        require(a+b+q>1 and max(a,b)<q and expo<1 and tail<min(remaining),
                (k, pt, a, b, q, expo, tail))
        minimum = min(minimum, a+b+q)
        maximum = max(maximum, expo)
        tail_max = max(tail_max, tail)
        total += 1
    print(k, "minimum tuple product exponent", float(minimum),
          "maximum error", float(maximum), "maximum h", float(tail_max))
print(total, "exact vertex checks")
