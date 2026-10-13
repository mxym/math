"""Exact rational strictness for the seven continuum certificate boxes."""
from pathlib import Path
from fractions import Fraction
import json
def main():
    root=Path(__file__).resolve().parents[2]
    p=root/'formalizations/appt-subunit-renyi/half_certificate.json'
    cells=json.loads(p.read_text())
    if len(cells)!=7:raise ValueError('wrong cell count')
    for i,c in enumerate(cells):
        b=c['b']
        if any(Fraction(x)<0 for row in b for x in row):raise ValueError('negative coefficient')
        corners=[b[0][0],b[0][-1],b[-1][0],b[-1][-1]]
        if any(Fraction(x)<=0 for x in corners):raise ValueError('nonstrict corner')
    print('EXACT_HALF_STRICTNESS_PASS: 7 continuum boxes; all 28 rational corners strictly positive')
if __name__=='__main__':main()
