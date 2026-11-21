"""Exact rail and box overlap verification for the true rank-five Type I note."""
from fractions import Fraction as F

X = tuple(map(F, (".12000", ".09637", ".17294", ".18971", ".19414", ".22684")))
theta = F(7, 32)
boxes = (
    ((2,), (3, 4), (0, 1, 5), ".499", ".5555"),
    ((3,), (0, 1, 2), (4, 5), ".553", ".5783"),
    ((2,), (0, 1, 4), (3, 5), ".5779", ".5829"),
    ((3,), (2, 5), (0, 1, 4), ".580", ".5889"),
    ((4,), (2, 5), (0, 1, 3), ".5888", ".5934"),
)


def require(pred, msg):
    if not pred:
        raise ValueError(msg)


require(sum(X) == 1, "s and five q exponents must sum to one")
require(X[4] + X[5] == F(".42098"), "largest q pair changed")
require(sum(X[1:4]) == F(".45902"), "smallest q triple changed")
reach = F(".4995")
smallest = F(1)
for i, (un, ll, mm, dlo, dhi) in enumerate(boxes, 1):
    require(sorted(un + ll + mm) == list(range(6)), f"bad partition {i}")
    u, l, m = (sum(X[j] for j in group) for group in (un, ll, mm))
    a, b = F(dlo), F(dhi)
    require(a < reach < b, f"missing overlap {i}")
    reach = b
    rails = (
        u, F(2, 3) - u - l, m - l, a - m, u + l - b,
        1 + a - 2*u - 3*l,
        2 - 2*theta + (2+theta)*a - (7-4*theta)*u - (4-theta)*l,
        2 + 2*a - 7*u - 4*l - theta,
    )
    smallest = min(smallest, min(rails))
    require(min(rails) >= F(".00049"), f"insufficient strict reserve {i}: {rails}")
    print(i, *(str(z) for z in (u, l, m, a, b, min(rails))))
require(reach == F(".5934"), "incorrect end")
print("Minimum exact rail margin:", smallest)
