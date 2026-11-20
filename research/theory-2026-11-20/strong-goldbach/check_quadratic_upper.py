"""Pure-rational enclosure. Run from this folder, alongside check_six.py."""
from fractions import Fraction as F
import runpy
from pathlib import Path
a=runpy.run_path(str(Path(__file__).resolve().with_name('check_six.py')))
pl,pu,ll,lu,z3l,z3u=(a[k] for k in ('pl','pu','ll','lu','z3l','z3u'))
lo=-pu**4/480 + pl**2*ll/6-3*z3u/4
hi=-pl**4/480 + pu**2*lu/6-3*z3l/4
if not (F(35702,10**6)<lo<hi<F(35704,10**6)):raise ValueError('five-factor enclosure failed')
if not 1+4*hi+2*F(6148,10**5)<F(1266,1000):raise ValueError('upper bound failed')
print('Quadratic five-factor interval and 1.266 comparison checked.')
