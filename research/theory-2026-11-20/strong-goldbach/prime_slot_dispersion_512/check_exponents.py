from fractions import Fraction as F
from itertools import product

B = (F(".5123"), F(".5129"))
C = (F(".499"), F(".512"))
corners = list(product(B, C))

checks = [
    ("variance, diagonal, q<T", lambda b, c: c-b, max, F("-.0003")),
    ("U", lambda b, c: b-1, max, F("-.4871")),
    ("V", lambda b, c: 3*b/2-1, max, F("-.23065")),
    ("W1", lambda b, c: F(17,20)*(c+b-1)+F(19,20)*b-c, max, F("-.00163")),
    ("W2", lambda b, c: c+b-1+F(7,8)*b-c, max, F("-.0383125")),
    ("H<T", lambda b, c: c-1, max, F("-.488")),
    ("H>1", lambda b, c: c+b-1, min, F(".0113")),
    ("low-q replacement 1", lambda b, c: b+C[0]/2, max, F(".7624")),
    ("low-q replacement 2", lambda b, c: C[0]+b/2, max, F(".75545")),
]

for name, formula, edge, expected in checks:
    value = edge(formula(b,c) for b,c in corners)
    if value != expected:
        raise SystemExit(f"{name}: got {value}, expected {expected}")
    print(f"{name}: {value} ({float(value):+.8f})")
print("All exact directed margins verified.")
